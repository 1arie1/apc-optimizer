import ApcOptimizer.Sp1Semantics
import ApcOptimizer.Implementation.EvalCongr
import ApcOptimizer.Implementation.InterfaceEncoding.Transfer
import ApcOptimizer.Implementation.InterfaceEncoding.Invariants
import ApcOptimizer.Implementation.InterfaceEncoding.Closure
import ApcOptimizer.Implementation.InterfaceEncoding.InternalPairs
import ApcOptimizer.Implementation.MemoryBusMultiset

set_option autoImplicit false

/-! # Interface-encoding metatheory: the audited theorems

The headline statements of the metatheory, over the definitions in
`ApcOptimizer/InterfaceEncoding/Spec.lean`. Like `ApcOptimizer/Optimizer.lean`, this file is
part of the audited surface: audit the statements here and in `Spec.lean`; the proof
machinery lives under `ApcOptimizer/Implementation/InterfaceEncoding/` and needs no audit —
check the proofs by running `lake build`.

The story in four steps:
1. Abstract (interface) equivalence implies concrete equivalence
   (`concreteEquiv_of_abstractEquiv`), because an `InterfaceMatch` is a permutation of the
   interface data, which determines side effects and transports the order-free bus rely.
2. What the verifier actually certifies is stronger on two counts, both harmless: its
   alignment is one *circuit-level* pairing, fixed before any assignment and used in both
   proof directions (`abstractEquivUnder_of_aligned`), and its reference-side premises
   restrict the ∀-side by invariants `accepts` already grants (`abstractEquiv_of_under`,
   `openVm_recvBytes_of_accepts`). The end-to-end OpenVM root is
   `openVm_concreteEquiv_of_interfaceVerified`.
3. The observable is the whole memory behavior: the window-atomicity rely says exactly
   "the traffic admits a closing environment" (`admissibleMemoryBusM_of_closes`,
   `exists_closes_of_admissible`); under a closing environment the nondeterministic receive
   payloads are a function of the environment and the send history
   (`closes_recv_determined`); and interface-matched runs close with the same environments
   (`interfaceMatch_closes_iff`) — identical traffic means identical closed compositions.
4. Bridges to the Spec vocabulary: `isSoundReplacementOf_of_concreteEquiv`, and the exact
   decomposition of the invariants clause — the stateful fragment transports
   (`statefulInvariants_of_abstractEquiv`), the stateless fragment is a per-circuit
   obligation, and together they assemble the full clause
   (`guaranteesInvariants_of_fragments`). For OpenVM the stateless fragment is *exactly* the
   multiplicity value (`openVm_stateless_maintainsInvariants_iff`), so the only check
   interface equivalence leaves open is the lookup-multiplicity discipline
   (`openVm_guaranteesInvariants_of_multOne`). Concrete equivalence is the bridge every
   technique passes through: for OpenVM it needs no interface data of its own, only the
   syntactic multiplicity discipline on the optimized circuit, and it lands directly on the
   Spec's soundness notion (`openVm_isSoundReplacementOf_of_concreteEquiv`). The Spec's
   *completeness* notion is out of reach of any equivalence — its witness is pinned to
   `Derivations.witgen` — so it is reached by keeping the witness instead of forgetting it
   (`ReplacesWithVia`, `replacesWith_of_via`,
   `isCompleteReplacementOf_of_replacesWithVia`). Concrete equivalence still reaches it
   under one extra hypothesis, the honest content of "a witness exists": that witness
   generation *reproduces* the equivalence's witness on the optimized circuit's variables,
   which is all its semantics reads (`isCompleteReplacementOf_of_replacesWith_of_agrees`).

5. The match need not be exact. An optimizer that *cancels* an internally-matched
   send/receive pair (`busUnify`; the verifier's internal pairs) leaves the two circuits with
   different traffic, so the chain is redone over `InterfaceMatchUpTo`
   (`concreteEquivUpTo_of_abstractEquivUpTo`, and the OpenVM root
   `openVm_concreteEquivUpTo_of_interfaceVerified`). Everything survives with one loss: the
   admissibility clause degrades from `↔` to a one-way implication (`MonoPair`), running from
   the traffic-richer circuit to the optimized one, because a dropped message's ∀-style rely
   conjuncts cannot be reinstated (`AdmissibleDropInvariant`). No consumer wanted more —
   soundness never mentions admissibility (`isSoundReplacementOf_of_witnessedBy`) and
   completeness used only `.mp` (`isCompleteReplacementOf_of_replacesWithMono_of_agrees`).
   The loss is an artifact of those conjuncts, not of the memory behavior: the closure
   statement is still a full `↔` (`interfaceMatchUpTo_closes_iff`), i.e. the dropped traffic
   is traffic no environment ever saw.

Not discharged here: the matching hypothesis itself — which interactions pair up is what
the external alignment analysis certifies and its SMT run assumes per instance. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-! ## Abstract equivalence implies concrete equivalence -/

/-- MAIN TRANSFER THEOREM: abstract (interface) equivalence implies concrete equivalence —
    the matched witness has the same side effects, and the order-free rely transports across
    the match. -/
theorem concreteEquiv_of_abstractEquiv {bs : BusSemantics p}
    (hperm : AdmissiblePermInvariant bs) {A B : Circuit p}
    (h : AbstractEquiv bs A B) : ConcreteEquiv bs A B := by
  constructor
  · intro a hsat
    obtain ⟨b, hbsat, hmatch⟩ := h.1 a hsat
    exact ⟨b, hbsat, sideEffects_eq_of_interfaceMatch hmatch,
      admissible_iff_of_interfaceMatch hperm hmatch⟩
  · intro b hsat
    obtain ⟨a, hasat, hmatch⟩ := h.2 b hsat
    exact ⟨a, hasat, (sideEffects_eq_of_interfaceMatch hmatch).symm,
      (admissible_iff_of_interfaceMatch hperm hmatch).symm⟩

/-- Restricting the ∀-side of the abstract equivalence by an invariant that `accepts`
    already grants on active messages loses nothing. This is why the verifier's
    premise-side facts (its "consequences" channel) do not shrink the certified
    statement. -/
theorem abstractEquiv_of_under {bs : BusSemantics p} {A B : Circuit p}
    {I : BusInteraction (ZMod p) → Prop}
    (hI : ∀ m : BusInteraction (ZMod p), m.multiplicity ≠ 0 → bs.accepts m → I m)
    (h : AbstractEquivUnder bs I A B) : AbstractEquiv bs A B := by
  constructor
  · intro a hsat
    exact h.1 a hsat fun m hm =>
      have ⟨hz, hacc⟩ := accepts_of_mem_activeStateful hsat hm
      hI m hz hacc
  · intro b hsat
    exact h.2 b hsat fun m hm =>
      have ⟨hz, hacc⟩ := accepts_of_mem_activeStateful hsat hm
      hI m hz hacc

/-- What the verifier certifies — ONE circuit-level alignment `σ` of the syntactic stateful
    interactions, fixed before any assignment is chosen, whose per-pair equalities are read
    with the SAME `σ` in both proof directions and under the premise restriction — implies
    the (weaker) `AbstractEquivUnder` the transfer pipeline consumes, which keeps only each
    witness's message-multiset equality. (A pairing quantified per assignment would carry no
    more information than `InterfaceMatch` itself; the certificate's strength is `σ`'s
    uniformity, which this theorem is free to forget.) -/
theorem abstractEquivUnder_of_aligned {bs : BusSemantics p}
    {I : BusInteraction (ZMod p) → Prop} {A B : Circuit p}
    (σ : Fin (statefulInteractions A bs).length ≃ Fin (statefulInteractions B bs).length)
    (h₁ : ∀ a, A.satisfies bs a → (∀ m ∈ activeStateful A bs a, I m) →
      ∃ b, B.satisfies bs b ∧ AlignedMatch bs A B σ a b)
    (h₂ : ∀ b, B.satisfies bs b → (∀ m ∈ activeStateful B bs b, I m) →
      ∃ a, A.satisfies bs a ∧ AlignedMatch bs A B σ a b) :
    AbstractEquivUnder bs I A B := by
  constructor
  · intro a ha hIa
    obtain ⟨b, hb, hal⟩ := h₁ a ha hIa
    exact ⟨b, hb, interfaceMatch_of_aligned hal⟩
  · intro b hb hIb
    obtain ⟨a, ha, hal⟩ := h₂ b hb hIb
    exact ⟨a, ha, interfaceMatch_of_aligned hal⟩

/-! ## Removal-tolerant transfer: dropping internal pairs

The match above is exact, so it covers only optimizations that *rearrange* stateful traffic.
Cancelling an internally-matched send/receive pair — what powdr's `busUnify` does, and what
the verifier's *internal pairs* certify — leaves the two circuits with different traffic, and
the whole chain has to be re-established over `InterfaceMatchUpTo`. It survives, with exactly
one loss: the admissibility clause degrades from `↔` to a one-way implication running from
the traffic-richer circuit to the optimized one (`MonoPair`), and no consumer wanted more. -/

/-- An exact match is the empty-removal case. -/
theorem interfaceMatchUpTo_of_interfaceMatch {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b) :
    InterfaceMatchUpTo bs A B a b :=
  ⟨[], ⟨[], by simp⟩, by simpa using h⟩

theorem abstractEquivUpTo_of_abstractEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : AbstractEquiv bs A B) : AbstractEquivUpTo bs A B :=
  ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, interfaceMatchUpTo_of_interfaceMatch hb.2⟩,
    fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, interfaceMatchUpTo_of_interfaceMatch ha.2⟩⟩

/-- Restricting the ∀-side by an invariant `accepts` already grants loses nothing here
    either — the argument is about the premise channel, not about the match. -/
theorem abstractEquivUpTo_of_under {bs : BusSemantics p} {A B : Circuit p}
    {I : BusInteraction (ZMod p) → Prop}
    (hI : ∀ m : BusInteraction (ZMod p), m.multiplicity ≠ 0 → bs.accepts m → I m)
    (h : AbstractEquivUnderUpTo bs I A B) : AbstractEquivUpTo bs A B := by
  constructor
  · intro a hsat
    exact h.1 a hsat fun m hm =>
      have ⟨hz, hacc⟩ := accepts_of_mem_activeStateful hsat hm
      hI m hz hacc
  · intro b hsat
    exact h.2 b hsat fun m hm =>
      have ⟨hz, hacc⟩ := accepts_of_mem_activeStateful hsat hm
      hI m hz hacc

/-- MAIN TRANSFER THEOREM, removal-tolerant: a match up to internal pairs still gives mutual
    coverage with equal side effects, and carries the rely from `A` to `B`.

    Two hypotheses on the rely instead of one. `AdmissiblePermInvariant` moves it across the
    permutation as before; `AdmissibleDropInvariant` then discards the cancelling traffic.
    That second step is where the `↔` is lost, and only there. -/
theorem concreteEquivUpTo_of_abstractEquivUpTo {bs : BusSemantics p}
    (hperm : AdmissiblePermInvariant bs) (hdrop : AdmissibleDropInvariant bs)
    {A B : Circuit p} (h : AbstractEquivUpTo bs A B) : ConcreteEquivUpTo bs A B := by
  have hpair : ∀ a b, InterfaceMatchUpTo bs A B a b → MonoPair bs A B a b := by
    intro a b hm
    refine ⟨sideEffects_eq_of_interfaceMatchUpTo hm, fun hadm => ?_⟩
    obtain ⟨D, hD, hmperm⟩ := hm
    rw [admissible_def] at hadm ⊢
    exact hdrop hD ((hperm hmperm).mp hadm)
  exact ⟨fun a ha => (h.1 a ha).imp fun b hb => ⟨hb.1, hpair a b hb.2⟩,
    fun b hb => (h.2 b hb).imp fun a ha => ⟨ha.1, hpair a b ha.2⟩⟩

/-- The exact-match conclusion refines the removal-tolerant one. -/
theorem concreteEquivUpTo_of_concreteEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : ConcreteEquiv bs A B) : ConcreteEquivUpTo bs A B :=
  ⟨fun a ha => (h.1 a ha).imp fun _ hb => ⟨hb.1, hb.2.1, hb.2.2.mp⟩,
    fun b hb => (h.2 b hb).imp fun _ ha => ⟨ha.1, ha.2.1.symm, ha.2.2.mpr⟩⟩

/-! ## Bridges to the Spec vocabulary -/

/-- Concrete equivalence yields the Spec's soundness direction. The invariants clause is a
    hypothesis: interface data cannot supply it (module docstring of `Spec.lean`). -/
theorem isSoundReplacementOf_of_concreteEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : ConcreteEquiv bs A B)
    (hinv : A.guaranteesInvariants bs → B.guaranteesInvariants bs) :
    B.isSoundReplacementOf A bs := by
  refine ⟨fun b hsat => ?_, hinv⟩
  obtain ⟨a, hasat, heff, _⟩ := h.2 b hsat
  exact ⟨a, hasat, heff⟩

/-- The Spec's soundness direction needs no admissibility clause at all — only that every run
    of `B` is covered by a run of `A` with equal side effects. So the removal-tolerant
    coverage lands it unchanged, and `isSoundReplacementOf_of_concreteEquiv` is its
    exact-match instance. -/
theorem isSoundReplacementOf_of_witnessedBy {bs : BusSemantics p} {A B : Circuit p}
    (h : WitnessedBy bs A B)
    (hinv : A.guaranteesInvariants bs → B.guaranteesInvariants bs) :
    B.isSoundReplacementOf A bs := by
  refine ⟨fun b hsat => ?_, hinv⟩
  obtain ⟨a, hasat, heff, -⟩ := h b hsat
  exact ⟨a, hasat, heff.symm⟩

theorem isSoundReplacementOf_of_concreteEquivUpTo {bs : BusSemantics p} {A B : Circuit p}
    (h : ConcreteEquivUpTo bs A B)
    (hinv : A.guaranteesInvariants bs → B.guaranteesInvariants bs) :
    B.isSoundReplacementOf A bs :=
  isSoundReplacementOf_of_witnessedBy h.2 hinv

/-- Forgetting the witness map: a witnessed replacement is a replacement. `ConcreteEquiv`
    is the forgetful image of the witnessed notion — which is why it lands the Spec's
    soundness direction but not its completeness. -/
theorem replacesWith_of_via {bs : BusSemantics p} {X Y : Circuit p}
    {w : (Variable → ZMod p) → (Variable → ZMod p)} (h : ReplacesWithVia bs X Y w) :
    ReplacesWith bs X Y :=
  fun x hx => ⟨w x, h x hx⟩

/-- Concrete replacement *along `Derivations.witgen ds`* yields the Spec's completeness
    direction. The two remaining conjuncts are bookkeeping about `ds` alone — no unused
    derivations, and every output variable reachable from the input ones — which no
    equivalence between circuits could state, let alone prove.

    Keeping the witness is exactly what makes this possible: the Spec pins the run
    reproducing `assignment` to `witgen ds assignment`, so an existential replacement is
    not enough (`ReplacesWithVia`). The hypothesis is also slightly stronger than needed —
    it covers every satisfying run of `A`, while completeness asks only about admissible
    ones — and only the forward half of the admissibility clause is used. -/
theorem isCompleteReplacementOf_of_replacesWithVia {bs : BusSemantics p} {A B : Circuit p}
    {ds : Derivations p} (h : ReplacesWithVia bs A B (Derivations.witgen ds))
    (hused : ∀ derivation ∈ ds, derivation.1 ∈ B.vars)
    (hcover : ds.cover A.vars B.vars) :
    B.isCompleteReplacementOf A bs ds := by
  refine fun _ => ⟨hused, hcover, fun assignment hadm hsat => ?_⟩
  obtain ⟨hsat', heff, hadm'⟩ := h assignment hsat
  exact ⟨hsat', hadm'.mp hadm, heff⟩

/-- A replacement whose witness the map `w` *reproduces* is a witnessed replacement. Since
    everything `B` says — `satisfies`, `admissible`, `sideEffects` — reads only `B.vars`,
    `w` need only agree with the witness there, not equal it.

    This is how concrete replacement reaches the Spec's completeness after all: the
    equivalence supplies the witness's *existence*, `w` supplies its *computation*, and the
    hypothesis is exactly that the two agree on the optimized circuit's variables. Take `h`
    to be `ConcreteEquiv`'s first component and `w` to be `Derivations.witgen ds`, and
    `isCompleteReplacementOf_of_replacesWithVia` finishes the job
    (`isCompleteReplacementOf_of_replacesWith_of_agrees`). -/
theorem replacesWithVia_of_replacesWith_of_agrees {bs : BusSemantics p} {A B : Circuit p}
    {w : (Variable → ZMod p) → (Variable → ZMod p)} (h : ReplacesWith bs A B)
    (hagrees : ∀ a b, A.satisfies bs a → B.satisfies bs b →
      A.sideEffects bs a = B.sideEffects bs b → (A.admissible bs a ↔ B.admissible bs b) →
      ∀ v ∈ B.vars, w a v = b v) :
    ReplacesWithVia bs A B w := by
  intro a ha
  obtain ⟨b, hb, heff, hadm⟩ := h a ha
  have hv : ∀ v ∈ B.vars, w a v = b v := hagrees a b ha hb heff hadm
  exact ⟨(Circuit.satisfies_congr hv).mpr hb,
    heff.trans (Circuit.sideEffects_congr hv).symm,
    hadm.trans (Circuit.admissible_congr hv).symm⟩

/-- END-TO-END: concrete replacement plus "witness generation computes the witness" yields
    the Spec's completeness. The agreement hypothesis is the honest content of *assuming a
    witness exists*: the existential is already in `h`, and what `ds` must add is that
    `witgen` lands on it — on `B.vars`, where alone it matters. -/
theorem isCompleteReplacementOf_of_replacesWith_of_agrees {bs : BusSemantics p}
    {A B : Circuit p} {ds : Derivations p} (h : ReplacesWith bs A B)
    (hagrees : ∀ a b, A.satisfies bs a → B.satisfies bs b →
      A.sideEffects bs a = B.sideEffects bs b → (A.admissible bs a ↔ B.admissible bs b) →
      ∀ v ∈ B.vars, Derivations.witgen ds a v = b v)
    (hused : ∀ derivation ∈ ds, derivation.1 ∈ B.vars)
    (hcover : ds.cover A.vars B.vars) :
    B.isCompleteReplacementOf A bs ds :=
  isCompleteReplacementOf_of_replacesWithVia
    (replacesWithVia_of_replacesWith_of_agrees h hagrees) hused hcover

/-! ### Completeness under removals

The same three theorems over `MonoPair`. Only `.mp` of the admissibility `↔` was ever used,
so nothing is lost — the completeness route survives a removal-tolerant match intact. -/

theorem replacesWithMono_of_viaMono {bs : BusSemantics p} {X Y : Circuit p}
    {w : (Variable → ZMod p) → (Variable → ZMod p)} (h : ReplacesWithViaMono bs X Y w) :
    ReplacesWithMono bs X Y :=
  fun x hx => ⟨w x, h x hx⟩

theorem isCompleteReplacementOf_of_replacesWithViaMono {bs : BusSemantics p}
    {A B : Circuit p} {ds : Derivations p}
    (h : ReplacesWithViaMono bs A B (Derivations.witgen ds))
    (hused : ∀ derivation ∈ ds, derivation.1 ∈ B.vars)
    (hcover : ds.cover A.vars B.vars) :
    B.isCompleteReplacementOf A bs ds := by
  refine fun _ => ⟨hused, hcover, fun assignment hadm hsat => ?_⟩
  obtain ⟨hsat', heff, hadm'⟩ := h assignment hsat
  exact ⟨hsat', hadm' hadm, heff⟩

theorem replacesWithViaMono_of_replacesWithMono_of_agrees {bs : BusSemantics p}
    {A B : Circuit p} {w : (Variable → ZMod p) → (Variable → ZMod p)}
    (h : ReplacesWithMono bs A B)
    (hagrees : ∀ a b, A.satisfies bs a → B.satisfies bs b → MonoPair bs A B a b →
      ∀ v ∈ B.vars, w a v = b v) :
    ReplacesWithViaMono bs A B w := by
  intro a ha
  obtain ⟨b, hb, heff, hadm⟩ := h a ha
  have hv : ∀ v ∈ B.vars, w a v = b v := hagrees a b ha hb ⟨heff, hadm⟩
  exact ⟨(Circuit.satisfies_congr hv).mpr hb,
    heff.trans (Circuit.sideEffects_congr hv).symm,
    fun hA => (Circuit.admissible_congr hv).mpr (hadm hA)⟩

/-- END-TO-END under removals: removal-tolerant replacement plus "witness generation computes
    the witness" still yields the Spec's completeness. -/
theorem isCompleteReplacementOf_of_replacesWithMono_of_agrees {bs : BusSemantics p}
    {A B : Circuit p} {ds : Derivations p} (h : ReplacesWithMono bs A B)
    (hagrees : ∀ a b, A.satisfies bs a → B.satisfies bs b → MonoPair bs A B a b →
      ∀ v ∈ B.vars, Derivations.witgen ds a v = b v)
    (hused : ∀ derivation ∈ ds, derivation.1 ∈ B.vars)
    (hcover : ds.cover A.vars B.vars) :
    B.isCompleteReplacementOf A bs ds :=
  isCompleteReplacementOf_of_replacesWithViaMono
    (replacesWithViaMono_of_replacesWithMono_of_agrees h hagrees) hused hcover

/-- The stateful fragment of the invariants clause *does* transport: a matched stateful
    message of `B` is a stateful message of `A`'s matching run. -/
theorem statefulInvariants_of_abstractEquivUpTo {bs : BusSemantics p} {A B : Circuit p}
    (h : AbstractEquivUpTo bs A B) (hA : A.guaranteesInvariants bs) :
    GuaranteesStatefulInvariants B bs := by
  intro b hbsat m hm
  obtain ⟨a, hasat, D, -, hmatch⟩ := h.2 b hbsat
  have hmA : m ∈ activeStateful A bs a := hmatch.mem_iff.mpr (List.mem_append_left D hm)
  have hz : m.multiplicity ≠ 0 := (accepts_of_mem_activeStateful hasat hmA).1
  obtain ⟨bi, hbi, rfl⟩ := exists_interaction_of_mem_activeStateful hmA
  exact hA a hasat bi hbi hz

theorem statefulInvariants_of_abstractEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : AbstractEquiv bs A B) (hA : A.guaranteesInvariants bs) :
    GuaranteesStatefulInvariants B bs :=
  statefulInvariants_of_abstractEquivUpTo (abstractEquivUpTo_of_abstractEquiv h) hA

/-- The two fragments assemble the full Spec invariants clause — transported stateful
    (`statefulInvariants_of_abstractEquiv`) plus circuit-local stateless. Nothing falls in
    the gap: every active message is one or the other. -/
theorem guaranteesInvariants_of_fragments {bs : BusSemantics p} {circuit : Circuit p}
    (hstateful : GuaranteesStatefulInvariants circuit bs)
    (hstateless : GuaranteesStatelessInvariants circuit bs) :
    circuit.guaranteesInvariants bs := by
  intro a hsat bi hbi
  show (bi.eval a).multiplicity ≠ 0 → bs.maintainsInvariants (bi.eval a)
  intro hz
  cases hs : bs.isStateful (bi.eval a).busId with
  | true =>
    refine hstateful a hsat (bi.eval a)
      (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨bi, hbi, rfl⟩, ?_⟩)
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hz, hs⟩
  | false => exact hstateless a hsat bi hbi hs hz

/-! ## OpenVM and SP1 instances -/

theorem openVm_admissiblePermInvariant (busMap : OpenVM.BusMap)
    (entryPc : Option (ZMod p)) :
    AdmissiblePermInvariant (OpenVM.openVmBusSemantics p busMap entryPc) :=
  fun _ _ h => OpenVM.openVmAdmissible_perm busMap entryPc h

theorem sp1_admissiblePermInvariant (busMap : SP1.BusMap) :
    AdmissiblePermInvariant (SP1.sp1BusSemantics p busMap) :=
  fun _ _ h => SP1.sp1Admissible_perm busMap h

/-- Dropping internal pairs preserves the OpenVM rely. The memory discipline and the entry
    designation are untouched (the excess is unchanged); the timestamp bound and
    `x0ReturnsZero` survive because they are per-message and the traffic only shrinks. -/
theorem openVm_admissibleDropInvariant (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) :
    AdmissibleDropInvariant (OpenVM.openVmBusSemantics p busMap entryPc) :=
  openVmAdmissible_drop busMap entryPc

theorem sp1_admissibleDropInvariant (busMap : SP1.BusMap) :
    AdmissibleDropInvariant (SP1.sp1BusSemantics p busMap) :=
  sp1Admissible_drop busMap

/-- The verifier's premise-side invariant for OpenVM: an active memory receive into a
    byte-checked address space carries byte data limbs. -/
def RecvBytes (busMap : OpenVM.BusMap) (m : BusInteraction (ZMod p)) : Prop :=
  busMap m.busId = some .memory → m.multiplicity = -1 →
    ∀ f, OpenVM.memoryPayload? m.payload = some f →
      f.isByteChecked → ∀ d ∈ f.data, OpenVM.isByte d

/-- OpenVM's `accepts` grants the recv-byte invariant, so the verifier's premise-side byte
    assumption restricts nothing. -/
theorem openVm_recvBytes_of_accepts (busMap : OpenVM.BusMap)
    (m : BusInteraction (ZMod p)) (hacc : OpenVM.accepts busMap m) :
    RecvBytes busMap m :=
  openVm_accepts_memory_recv_bytes busMap m hacc

/-- OpenVM's stateless invariant is EXACTLY the multiplicity value: on a known stateless
    bus, `maintainsInvariants` says `multiplicity = 1` and nothing else — payload
    correctness is `accepts`' business and holds in each circuit independently. So the only
    check the interface transport leaves open for the full invariants clause is the
    lookup-multiplicity discipline. -/
theorem openVm_stateless_maintainsInvariants_iff {busMap : OpenVM.BusMap}
    {m : BusInteraction (ZMod p)} {t : OpenVM.OpenVmBusType}
    (hbus : busMap m.busId = some t) (hs : t.isStateful = false) :
    OpenVM.maintainsInvariants busMap m ↔ m.multiplicity = 1 := by
  unfold OpenVM.maintainsInvariants
  rw [hbus]
  cases t
  all_goals first
    | exact Iff.rfl
    | simp [OpenVM.OpenVmBusType.isStateful] at hs

/-- For OpenVM, the transported stateful fragment plus the multiplicity discipline on
    stateless buses assemble the full invariants clause — the multiplicity value is the ONLY
    missing check (`openVm_stateless_maintainsInvariants_iff`). Unknown buses need no
    hypothesis: an active message on one is already rejected by `accepts`. -/
theorem openVm_guaranteesInvariants_of_multOne (busMap : OpenVM.BusMap)
    (entryPc : Option (ZMod p)) {circuit : Circuit p}
    (hstateful : GuaranteesStatefulInvariants circuit
      (OpenVM.openVmBusSemantics p busMap entryPc))
    (hmult : ∀ a, circuit.satisfies (OpenVM.openVmBusSemantics p busMap entryPc) a →
      ∀ bi ∈ circuit.busInteractions,
        (OpenVM.openVmBusSemantics p busMap entryPc).isStateful (bi.eval a).busId = false →
        (bi.eval a).multiplicity ≠ 0 → (bi.eval a).multiplicity = 1) :
    circuit.guaranteesInvariants (OpenVM.openVmBusSemantics p busMap entryPc) := by
  refine guaranteesInvariants_of_fragments hstateful ?_
  intro a hsat bi hbi hs hz
  have hacc : OpenVM.accepts busMap (bi.eval a) := hsat.2 bi hbi hz
  obtain ⟨t, hbus⟩ := openVm_busMap_isSome_of_accepts hacc
  have hts : t.isStateful = false := by
    have hs' : (match busMap (bi.eval a).busId with
        | some u => u.isStateful
        | none => false) = false := hs
    rw [hbus] at hs'
    exact hs'
  show OpenVM.maintainsInvariants busMap (bi.eval a)
  rw [openVm_stateless_maintainsInvariants_iff hbus hts]
  exact hmult a hsat bi hbi hs hz

/-- END-TO-END, OpenVM: what the interface-encoded VC certifies (`AbstractEquivUnder` the
    recv-byte premise, under the OpenVM bus semantics) implies concrete equivalence. -/
theorem openVm_concreteEquiv_of_interfaceVerified
    (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) {A B : Circuit p}
    (h : AbstractEquivUnder (OpenVM.openVmBusSemantics p busMap entryPc)
      (RecvBytes busMap) A B) :
    ConcreteEquiv (OpenVM.openVmBusSemantics p busMap entryPc) A B :=
  concreteEquiv_of_abstractEquiv (openVm_admissiblePermInvariant busMap entryPc)
    (abstractEquiv_of_under
      (fun m _ hacc => openVm_recvBytes_of_accepts busMap m hacc) h)

/-- CONCRETE EQUIVALENCE IS THE BRIDGE, OpenVM: `isSoundReplacementOf_of_concreteEquiv` with
    its invariants hypothesis discharged from `ConcreteEquiv` plus one syntactic side
    condition on `B` — the multiplicity discipline. Nothing is assumed about `A` beyond the
    `guaranteesInvariants` it has by construction, which is the antecedent of the clause
    being proved.

    The side condition is what `ConcreteEquiv` structurally cannot see: `Circuit.sideEffects`
    records the *net* multiplicity per tuple, so it neither pins down an individual
    multiplicity nor notices a send whose contribution is canceled. Once every active
    interaction is sent once or received once, both leaks close — a canceled send is canceled
    by a *receive* of the identical tuple, whose data `accepts` already forces to be bytes,
    and an uncanceled one is matched by an active message of `A` on the same tuple.

    `hlen` rules out the degenerate cancellation by field wrap-around (`p` sends of one tuple
    summing to zero); any real circuit has far fewer interactions than the field size. -/
theorem openVm_isSoundReplacementOf_of_concreteEquivUpTo
    (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) {A B : Circuit p}
    (h : ConcreteEquivUpTo (OpenVM.openVmBusSemantics p busMap entryPc) A B)
    (hdisc : MultiplicityDiscipline B (OpenVM.openVmBusSemantics p busMap entryPc))
    (hlen : B.busInteractions.length < p) :
    B.isSoundReplacementOf A (OpenVM.openVmBusSemantics p busMap entryPc) :=
  isSoundReplacementOf_of_concreteEquivUpTo h
    (fun hA => openVm_guaranteesInvariants_of_concreteEquiv busMap entryPc h.2 hA hdisc hlen)

theorem openVm_isSoundReplacementOf_of_concreteEquiv
    (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) {A B : Circuit p}
    (h : ConcreteEquiv (OpenVM.openVmBusSemantics p busMap entryPc) A B)
    (hdisc : MultiplicityDiscipline B (OpenVM.openVmBusSemantics p busMap entryPc))
    (hlen : B.busInteractions.length < p) :
    B.isSoundReplacementOf A (OpenVM.openVmBusSemantics p busMap entryPc) :=
  openVm_isSoundReplacementOf_of_concreteEquivUpTo busMap entryPc
    (concreteEquivUpTo_of_concreteEquiv h) hdisc hlen

/-- END-TO-END, OpenVM, removal-tolerant: what the interface-encoded VC certifies when the
    alignment is allowed to drop internally-matched pairs. Both rely hypotheses are
    discharged from the OpenVM semantics. -/
theorem openVm_concreteEquivUpTo_of_interfaceVerified
    (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) {A B : Circuit p}
    (h : AbstractEquivUnderUpTo (OpenVM.openVmBusSemantics p busMap entryPc)
      (RecvBytes busMap) A B) :
    ConcreteEquivUpTo (OpenVM.openVmBusSemantics p busMap entryPc) A B :=
  concreteEquivUpTo_of_abstractEquivUpTo (openVm_admissiblePermInvariant busMap entryPc)
    (openVm_admissibleDropInvariant busMap entryPc)
    (abstractEquivUpTo_of_under
      (fun m _ hacc => openVm_recvBytes_of_accepts busMap m hacc) h)

/-! ## Closure semantics: the observable is the whole memory behavior -/

/-- Closing with some environment entails the audited window-atomicity rely: the environment
    supplies at most one record per address, so the receives' excess is at most one. -/
theorem admissibleMemoryBusM_of_closes {shape : MemoryBusShape} {E : MemEnv p}
    {M : Multiset (BusInteraction (ZMod p))} (h : Closes shape E M) :
    admissibleMemoryBusM shape M := by
  intro addr
  refine le_trans (Multiset.card_le_card (excessAt_le_entryMS_of_closes h addr)) ?_
  unfold MemEnv.entryMS
  cases E.entry addr <;> simp

/-- Conversely, the rely entails closure with *some* environment, whenever receives and
    sends per address are equinumerous (the shape of real blocks: each access is a
    receive/send pair). This is the semantic reading of `admissibleMemoryBusM`: window
    atomicity = "the traffic admits an environment". -/
theorem exists_closes_of_admissible {shape : MemoryBusShape}
    {M : Multiset (BusInteraction (ZMod p))}
    (hM : admissibleMemoryBusM shape M)
    (hbal : ∀ addr : List (Option (ZMod p)),
      Multiset.card (recvsAt shape addr M) = Multiset.card (sendsAt shape addr M)) :
    ∃ E : MemEnv p, Closes shape E M := by
  choose e x he hx using env_reps_of_admissible hM hbal
  refine ⟨⟨e, x⟩, fun addr => ?_⟩
  show (recvsAt shape addr M).map BusInteraction.payload + (x addr).elim 0 (fun P => {P})
      = (sendsAt shape addr M).map BusInteraction.payload + (e addr).elim 0 (fun P => {P})
  rw [← hx addr, ← he addr]
  exact add_sub_comm_union _ _

/-- MEMORY DETERMINISM: under a closing environment, the nondeterministic receive payloads
    are a *function* of the environment and the send history. Present one address group as
    `k` accesses in timestamp order (the same presentation hypotheses as
    `admissibleMemoryBusM_copies` — no TS_BOUND is needed): the first receive reads the
    environment's entry record, and every later receive copies the previous send. -/
theorem closes_recv_determined {k : ℕ} (shape : MemoryBusShape)
    {M : Multiset (BusInteraction (ZMod p))} {E : MemEnv p} (hclose : Closes shape E M)
    (addr : List (Option (ZMod p)))
    (send recv : Fin k → BusInteraction (ZMod p))
    (hsend : sendsAt shape addr M = Multiset.map send ↑(List.finRange k))
    (hrecv : recvsAt shape addr M = Multiset.map recv ↑(List.finRange k))
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hpay : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hmono : StrictMono fun i => tsVal (send i))
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i)) :
    (∀ h0 : 0 < k, E.entry addr = some ((recv ⟨0, h0⟩).payload)) ∧
    (∀ i : Fin k, 0 < i.val →
      (recv i).payload
        = (send ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).payload) := by
  constructor
  · intro h0
    exact entry_eq_of_mem_excess hclose
      (recv_zero_in_excess shape send recv hsend hrecv tsVal hpay hmono hlt h0)
  · exact admissibleMemoryBusM_copies shape M addr (admissibleMemoryBusM_of_closes hclose)
      send recv hsend hrecv tsVal hpay hmono hlt

/-- Interface-matched runs close with the same environments, on every memory-shaped bus: no
    environment can observe a difference or supply data distinguishing the two runs. -/
theorem interfaceMatch_closes_iff {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b)
    (shape : MemoryBusShape) (busId : Nat) (E : MemEnv p) :
    Closes shape E (busTraffic A bs busId a) ↔ Closes shape E (busTraffic B bs busId b) := by
  rw [busTraffic_eq_of_interfaceMatch h busId]

/-- Dropping internal pairs is invisible to the environment too, and here the statement is a
    full `↔` — closure is an exact balance, and a cancelling pair adds the same payload to
    both of its sides. The semantic reading of the removal: `B` computes with the same
    memory environments as `A`, and the traffic it dropped is traffic no environment ever
    saw. Contrast the rely (`AdmissibleDropInvariant`), which only survives one way — the
    asymmetry is an artifact of the rely's per-message conjuncts, not of the memory
    behavior. -/
theorem interfaceMatchUpTo_closes_iff {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatchUpTo bs A B a b)
    (shape : MemoryBusShape) (busId : Nat) (E : MemEnv p) :
    Closes shape E (busTraffic A bs busId a) ↔ Closes shape E (busTraffic B bs busId b) := by
  obtain ⟨D, hD, heq⟩ := busTraffic_add_of_interfaceMatchUpTo h busId
  rw [heq]
  exact closes_add_iff hD

end ApcOptimizer.Interface
