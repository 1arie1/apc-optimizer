import ApcOptimizer.InterfaceEncoding.Equiv
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics

set_option autoImplicit false

/-! # Interface-encoding transfer: abstract equivalence implies concrete equivalence

The thin bridge (`concreteEquiv_of_abstractEquiv`): an `InterfaceMatch` is a permutation of
the active stateful message lists, so side effects — net multiplicities, i.e. sums over that
list — agree, and the (order-free) bus rely transports. The end-to-end OpenVM root is
`openVm_concreteEquiv_of_interfaceVerified`: what the verifier certifies (`AbstractEquivUnder`
the recv-byte premise) implies concrete equivalence, because `accepts` already grants the
premise (`openVm_recvBytes_of_accepts`). -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-! ## Side effects factor through the interface data -/

/-- The net multiplicity a message key collects from a list of evaluated messages. -/
def netMult (L : List (BusInteraction (ZMod p))) (key : BusMessage p) : ZMod p :=
  ((L.filter (fun m => decide ((m.busId, m.payload) = key))).map
    (fun m => m.multiplicity)).sum

theorem netMult_perm {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L')
    (key : BusMessage p) : netMult L key = netMult L' key :=
  ((h.filter _).map _).sum_eq

/-- `Circuit.sideEffects` is the per-key net multiplicity of the interface data: a key on a
    stateless bus collects nothing on either side, and the zero-multiplicity messages the
    activity filter drops contribute zero. -/
theorem sideEffects_eq_netMult (circuit : Circuit p) (bs : BusSemantics p)
    (a : Variable → ZMod p) (key : BusMessage p) :
    circuit.sideEffects bs a key = netMult (activeStateful circuit bs a) key := by
  unfold Circuit.sideEffects netMult activeStateful
  generalize (circuit.busInteractions.map (fun bi => bi.eval a)) = L
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hs : bs.isStateful hd.busId
    · by_cases hk : (hd.busId, hd.payload) = key
      · by_cases hz : hd.multiplicity = 0
        · rw [List.filter_cons_of_pos (by simp [hs, hk]),
            List.filter_cons_of_neg (by simp [hz]),
            List.map_cons, List.sum_cons, hz, zero_add]
          exact ih
        · rw [List.filter_cons_of_pos (by simp [hs, hk]),
            List.filter_cons_of_pos (by simp [hz, hs]),
            List.filter_cons_of_pos (by simp [hk]),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      · by_cases hz : hd.multiplicity = 0
        · rw [List.filter_cons_of_neg (by simp [hk]),
            List.filter_cons_of_neg (by simp [hz])]
          exact ih
        · rw [List.filter_cons_of_neg (by simp [hk]),
            List.filter_cons_of_pos (by simp [hz, hs]),
            List.filter_cons_of_neg (by simp [hk])]
          exact ih
    · rw [List.filter_cons_of_neg (by simp [hs]),
        List.filter_cons_of_neg (by simp [hs])]
      exact ih

theorem sideEffects_eq_of_interfaceMatch {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b) :
    A.sideEffects bs a = B.sideEffects bs b := by
  funext key
  rw [sideEffects_eq_netMult, sideEffects_eq_netMult]
  exact netMult_perm h key

theorem admissible_iff_of_interfaceMatch {bs : BusSemantics p}
    (hperm : AdmissiblePermInvariant bs) {A B : Circuit p} {a b : Variable → ZMod p}
    (h : InterfaceMatch bs A B a b) :
    (A.admissible bs a ↔ B.admissible bs b) := by
  rw [admissible_def, admissible_def]
  exact hperm h

/-! ## The thin bridge -/

/-- Abstract (interface) equivalence implies concrete equivalence: the matched witness has
    the same side effects (`sideEffects_eq_of_interfaceMatch`) and the order-free rely
    transports across the match (`admissible_iff_of_interfaceMatch`). -/
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

/-! ## The premise restriction is harmless -/

/-- Every interface message of a satisfying run is active and accepted. -/
theorem accepts_of_mem_activeStateful {circuit : Circuit p} {bs : BusSemantics p}
    {a : Variable → ZMod p} (hsat : circuit.satisfies bs a)
    {m : BusInteraction (ZMod p)} (hm : m ∈ activeStateful circuit bs a) :
    m.multiplicity ≠ 0 ∧ bs.accepts m := by
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hm
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hmem
  have hz : (bi.eval a).multiplicity ≠ 0 :=
    of_decide_eq_true ((Bool.and_eq_true _ _).mp hcond).1
  exact ⟨hz, hsat.2 bi hbi hz⟩

/-- Restricting the ∀-side of the abstract equivalence by an invariant that `accepts` already
    grants on active messages loses nothing. This is why the verifier's premise-side recv-byte
    assumption (its "consequences" channel) does not shrink the certified statement. -/
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

/-! ## Bridges to the Spec vocabulary -/

/-- Concrete equivalence yields the Spec's soundness direction. The invariants clause is a
    hypothesis: interface data cannot supply it (module docstring of `Equiv.lean`). -/
theorem isSoundReplacementOf_of_concreteEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : ConcreteEquiv bs A B)
    (hinv : A.guaranteesInvariants bs → B.guaranteesInvariants bs) :
    B.isSoundReplacementOf A bs := by
  refine ⟨fun b hsat => ?_, hinv⟩
  obtain ⟨a, hasat, heff, _⟩ := h.2 b hsat
  exact ⟨a, hasat, heff⟩

/-- The stateful fragment of the invariants clause *does* transport: a matched stateful
    message of `B` is a stateful message of `A`'s matching run. -/
theorem statefulInvariants_of_abstractEquiv {bs : BusSemantics p} {A B : Circuit p}
    (h : AbstractEquiv bs A B) (hA : A.guaranteesInvariants bs) :
    GuaranteesStatefulInvariants B bs := by
  intro b hbsat m hm
  obtain ⟨a, hasat, hmatch⟩ := h.2 b hbsat
  have hmA : m ∈ activeStateful A bs a := hmatch.mem_iff.mpr hm
  have hz : m.multiplicity ≠ 0 := (accepts_of_mem_activeStateful hasat hmA).1
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hmA
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hmem
  exact hA a hasat bi hbi hz

/-! ## OpenVM and SP1 instances -/

theorem openVm_admissiblePermInvariant (busMap : OpenVM.BusMap)
    (entryPc : Option (ZMod p)) :
    AdmissiblePermInvariant (OpenVM.openVmBusSemantics p busMap entryPc) :=
  fun _ _ h => OpenVM.openVmAdmissible_perm busMap entryPc h

theorem sp1_admissiblePermInvariant (busMap : SP1.BusMap) :
    AdmissiblePermInvariant (SP1.sp1BusSemantics p busMap) :=
  fun _ _ h => SP1.sp1Admissible_perm busMap h

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
    RecvBytes busMap m := by
  intro hbus hmult f hf
  unfold OpenVM.accepts at hacc
  split at hacc
  -- every non-memory arm carries an equation on `busMap m.busId` contradicting `hbus`;
  -- the memory arm reduces `hacc` to the inner match on `memoryPayload?`
  all_goals
    first
      | (rw [hf] at hacc; exact hacc hmult)
      | simp_all

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

end ApcOptimizer.Interface
