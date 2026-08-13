import ApcOptimizer.VmSpec
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

/-! Connecting `Spec.lean`'s per-chip replacement conditions to `VmSpec.lean`'s VM-level
    `VmEquivalent`. This file proves the **soundness** half: if every guest chip is replaced by a
    `Circuit.isSoundReplacementOf`, then every effect the optimized VM can produce, the original
    VM can produce too (`canProduce_of_isSoundReplacementOf`).

    Two vocabularies have to be bridged:

    * `Circuit.satisfies` demands `BusSemantics.accepts` on every active message;
      `VmAssignment.satisfiesGuest` demands only the algebraic constraints. `Host.forcesAccepts`
      is the missing half, and it is **derived**, not assumed: the host chips *are* the lookup
      tables, so in a balanced VM a guest's active stateless message has nowhere to go but into a
      chip that only receives accepted payloads. See `forcesAccepts_of_sinksAreTables`, which
      formalizes the stateless induction of the manuscript's `bus_int.tex`.

      That induction is where `VmAssignment.withinBudget` earns its place. The manuscript argues
      with `mᵢ > 0`/`mᵢ < 0` over the canonical embedding in `ℤ`, but balancing is an equation in
      `ZMod p`: `p` instances that each send the same message sum to `0` in the field while
      summing to `p` in `ℤ`, and the sink is never obliged to receive them. `Circuit.countAt`
      tracks the honest natural number, and the budget keeps it below `p`.

    * `Circuit.sideEffects` — what a sound replacement preserves — covers only *stateful* buses,
      whereas `VmAssignment.netBus` sums over *all* of them. So replacing a guest chip may well
      unbalance the stateless buses (dropping a redundant range check is exactly this), and the
      host's lookup chips have to be rebuilt to match. `Host.absorbsStateless` is the permission
      to do that — the manuscript's observation that a table sink can balance *any* legal
      interaction with its bus, which is also why equivalence need only hold on the stateful ones.

    Note what `absorbsStateless` does *not* permit: the input and output chips are pinned, so the
    observed `VmEffect` is carried across untouched. That, plus stateful balance coming from
    `sideEffects` preservation, is the whole argument.

    What is still assumed: `Circuit.statefulAccepts` per guest chip (the manuscript derives the
    corresponding `eq:legal:recv_byte` from a second balancing argument), and the two `Host`
    conditions, which are stated abstractly here and not yet discharged for `openVmHost`. -/

variable {p : ℕ}

--------- Host assignments in isolation ---------

/-- The host side of a `VmAssignment`, on its own, so that the `Host` conditions below can be
    stated without a `Vm` in scope. -/
abbrev HostAssignment (p : ℕ) (host : Host p) := Fin host.chips.length → List (BusState p)

/-- `VmAssignment.satisfiesHost` as a predicate on the host assignment alone (it never reads the
    guest side), so that `Host.absorbsStateless` can be stated without a `Vm` in scope. -/
def HostLegal {host : Host p} (hA : HostAssignment p host) : Prop :=
  (∀ t : Fin host.chips.length, ∀ effect ∈ hA t, (host.chips.get t).canProduce effect) ∧
  (∀ t : Fin host.chips.length, (host.chips.get t).singleton → (hA t).length = 1)

/-- The net multiplicity the host chips contribute to every message. -/
def hostNet {host : Host p} (hA : HostAssignment p host) : BusState p :=
  fun message => ∑ t : Fin host.chips.length, ((hA t).map (fun effect => effect message)).sum

/-- The net multiplicity the guest chips contribute to every message. -/
def guestNet (G : List (Circuit p)) (gA : (t : Fin G.length) → List (ChipAssignment p)) :
    BusState p :=
  fun message =>
    ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg message)).sum

theorem netBus_apply {host : Host p} {G : List (Circuit p)} (a : VmAssignment p ⟨host, G⟩)
    (m : BusMessage p) :
    a.netBus m = guestNet G a.guestAssignments m + hostNet a.hostAssignment m :=
  rfl

theorem hostLegal_of_satisfiesHost {host : Host p} {G : List (Circuit p)}
    {a : VmAssignment p ⟨host, G⟩} (h : a.satisfiesHost) : HostLegal a.hostAssignment :=
  h

--------- `allEffects` vs `sideEffects` ---------

/-- On a stateful message the two agree: `Circuit.sideEffects`'s extra `isStateful` filter is
    implied by the message-equality filter both share. This is the bridge between what a sound
    replacement preserves and what `VmSat` balances. -/
theorem allEffects_eq_sideEffects {c : Circuit p} {bs : BusSemantics p}
    {asg : ChipAssignment p} {m : BusMessage p} (hm : bs.isStateful m.1 = true) :
    c.allEffects asg m = c.sideEffects bs asg m := by
  have hpt : ∀ x : BusInteraction (ZMod p),
      decide ((x.busId, x.payload) = m) =
        (bs.isStateful x.busId && decide ((x.busId, x.payload) = m)) := by
    intro x
    by_cases h : (x.busId, x.payload) = m
    · have hbus : x.busId = m.1 := congrArg Prod.fst h
      simp [hbus, hm]
    · simp [h]
  have key : (c.busInteractions.map (fun bi => bi.eval asg)).filter
        (fun x => decide ((x.busId, x.payload) = m)) =
      (c.busInteractions.map (fun bi => bi.eval asg)).filter
        (fun x => bs.isStateful x.busId && decide ((x.busId, x.payload) = m)) :=
    List.filter_congr (fun x _ => hpt x)
  simp only [Circuit.allEffects, Circuit.sideEffects, key]

/-- A message a chip nets a nonzero multiplicity onto is carried by one of its bus interactions,
    with a nonzero multiplicity of its own — the step that turns `VmSat`'s balance into a
    `Circuit.satisfies` acceptance obligation. -/
theorem exists_active_of_allEffects_ne_zero {c : Circuit p} {asg : ChipAssignment p}
    {m : BusMessage p} (h : c.allEffects asg m ≠ 0) :
    ∃ bi ∈ c.busInteractions, ((bi.eval asg).busId, (bi.eval asg).payload) = m ∧
      (bi.eval asg).multiplicity ≠ 0 := by
  by_contra hcon
  refine h (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  by_contra hmult
  exact hcon ⟨bi, hbi, of_decide_eq_true hy2, hmult⟩

theorem exists_instance_of_guestNet_ne_zero {G : List (Circuit p)}
    {gA : (t : Fin G.length) → List (ChipAssignment p)} {m : BusMessage p}
    (h : guestNet G gA m ≠ 0) :
    ∃ (t : Fin G.length) (asg : ChipAssignment p),
      asg ∈ gA t ∧ (G.get t).allEffects asg m ≠ 0 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_contra hcon
  refine ht (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨asg, hasg, rfl⟩ := List.mem_map.mp hx
  by_contra hne
  exact hcon ⟨t, asg, hasg, hne⟩

theorem exists_instance_of_hostNet_ne_zero {host : Host p} {hA : HostAssignment p host}
    {m : BusMessage p} (h : hostNet hA m ≠ 0) :
    ∃ (t : Fin host.chips.length) (c : BusState p), c ∈ hA t ∧ c m ≠ 0 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_contra hcon
  refine ht (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  by_contra hne
  exact hcon ⟨t, c, hc, hne⟩

--------- Choosing the original assignment a sound replacement promises ---------

open Classical in
/-- The original-circuit assignment `Circuit.isSoundReplacementOf` promises for `asg`, as a total
    function (`asg` itself on inputs where no such assignment exists, which
    `soundWitness_spec`'s hypothesis rules out). -/
noncomputable def soundWitness (optimized original : Circuit p) (bs : BusSemantics p)
    (asg : ChipAssignment p) : ChipAssignment p :=
  if h : ∃ asg', original.satisfies bs asg' ∧
      optimized.sideEffects bs asg = original.sideEffects bs asg'
    then h.choose else asg

theorem soundWitness_spec {optimized original : Circuit p} {bs : BusSemantics p}
    {asg : ChipAssignment p}
    (h : ∃ asg', original.satisfies bs asg' ∧
      optimized.sideEffects bs asg = original.sideEffects bs asg') :
    original.satisfies bs (soundWitness optimized original bs asg) ∧
      optimized.sideEffects bs asg =
        original.sideEffects bs (soundWitness optimized original bs asg) := by
  rw [soundWitness, dif_pos h]
  exact h.choose_spec

--------- What the host must provide ---------

--------- Well-formedness of a guest chip ---------

/-- A guest chip writes only `0`/`1` multiplicities to stateless buses — the manuscript's
    `eq:legal:stateless:mult`, and OpenVM's requirement on every IR.

    Conditioned on the chip's **algebraic** constraints alone, deliberately: conditioning on
    `Circuit.satisfies` would be circular, since `satisfies` bundles the very `accepts` obligation
    that `Host.forcesAccepts` derives *from* this property. `VmSat` supplies exactly the algebraic
    half (`VmAssignment.satisfiesGuest`), which is what makes the induction go through. -/
def Circuit.statelessSendOnly (c : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ asg : ChipAssignment p, (∀ e ∈ c.algebraicConstraints, e.eval asg = 0) →
    ∀ bi ∈ c.busInteractions, bs.isStateful bi.busId = false →
      (bi.eval asg).multiplicity = 0 ∨ (bi.eval asg).multiplicity = 1

/-- A guest chip's active *stateful* messages are accepted, on the strength of its algebraic
    constraints alone.

    Assumed rather than derived. The bus-balancing argument in this file covers the stateless
    buses; for memory the manuscript derives the analogous fact (`eq:legal:recv_byte`: only bytes
    are received, because only bytes are sent) from a second balancing argument layered on top of
    the stateless one. Doing that here would mean formalizing `eq:legal:stateful:send_byte` and
    its induction; until then this stands in for it. -/
def Circuit.statefulAccepts (c : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ asg : ChipAssignment p, (∀ e ∈ c.algebraicConstraints, e.eval asg = 0) →
    ∀ bi ∈ c.busInteractions, bs.isStateful bi.busId = true →
      (bi.eval asg).multiplicity ≠ 0 → bs.accepts (bi.eval asg)

/-- What a VM requires of any guest chip it will run, before and after optimization alike. -/
structure Circuit.legalGuest (c : Circuit p) (bs : BusSemantics p) : Prop where
  sendOnly : c.statelessSendOnly bs
  statefulOk : c.statefulAccepts bs

--------- What the host must provide ---------

/-- The host's stateless chips are lookup tables: any stateless message they leave with a nonzero
    net multiplicity is one the semantics accepts. This is the manuscript's "table sink"
    (`bus_int.tex`), which implements its bus's predicate.

    Much weaker than `Host.forcesAccepts`, and not a statement about guests at all — it says only
    that the sinks are honest. `forcesAccepts_of_sinksAreTables` supplies the balancing argument
    that turns it into a guarantee about every guest instance. -/
def Host.sinksAreTables (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, HostLegal hA →
    ∀ m : BusMessage p, bs.isStateful m.1 = false → hostNet hA m ≠ 0 →
      ∀ mult : ZMod p, mult ≠ 0 → bs.accepts ⟨m.1, mult, m.2⟩

/-- The host chips realize `bs`'s acceptance: in any satisfying VM built on this host whose guest
    chips are `Circuit.legalGuest` and small enough not to wrap `ZMod p`, every guest instance's
    assignment is `Circuit.satisfies`-good, not merely algebraically consistent.

    `L` bounds each chip's bus-interaction count; `L * host.maxInstances < p` is the
    anti-wraparound condition. It has to count *interactions*, not instances: one instance may
    carry the same message several times (two range checks on one value at one width), so the
    natural number that must stay below `p` is instances × interactions.

    Proved from `Host.sinksAreTables` — see `forcesAccepts_of_sinksAreTables`. -/
def Host.forcesAccepts (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ (G : List (Circuit p)) (L : ℕ),
    (∀ t : Fin G.length, (G.get t).legalGuest bs) →
    (∀ t : Fin G.length, (G.get t).busInteractions.length ≤ L) →
    L * host.maxInstances < p →
    ∀ (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a →
      ∀ (t : Fin G.length), ∀ asg ∈ a.guestAssignments t, (G.get t).satisfies bs asg

/-- The host can re-balance a stateless change: given a legal host assignment and a `δ` supported
    on stateless messages the semantics accepts, some legal host assignment nets exactly `δ` more,
    **leaving the input and output chips alone**.

    Lookup host chips are free in exactly this way — their legality predicate constrains *which*
    payloads may carry a nonzero net multiplicity, not what that multiplicity is — and they are
    not `HostChip.singleton`, so their instance count is free too. The input/output clauses are
    what make the observed effect survive the rebuild. -/
def Host.absorbsStateless (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, HostLegal hA →
    ∀ δ : BusState p,
      (∀ m : BusMessage p, δ m ≠ 0 →
        bs.isStateful m.1 = false ∧
          ∃ mult : ZMod p, mult ≠ 0 ∧ bs.accepts ⟨m.1, mult, m.2⟩) →
      ∃ hA' : HostAssignment p host, HostLegal hA' ∧ hostNet hA' = hostNet hA + δ ∧
        hA' host.inputChip = hA host.inputChip ∧
        hA' host.outputChip = hA host.outputChip

--------- Counting: why balance forces a lookup to be consulted ---------

/-- The multiplicities a chip's bus interactions put on `m` — precisely the list
    `Circuit.allEffects` sums. -/
def Circuit.multsAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : List (ZMod p) :=
  ((c.busInteractions.map (fun bi => bi.eval asg)).filter
    (fun x => decide ((x.busId, x.payload) = m))).map (fun x => x.multiplicity)

/-- How many of a chip's bus interactions actively carry `m`. The natural number that must be
    kept below `p`: it is what `Circuit.allEffects` degenerates to once multiplicities are `0`/`1`,
    and unlike the field element it cannot silently wrap to zero. -/
def Circuit.countAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : ℕ :=
  (c.multsAt asg m).countP (fun v => decide (v ≠ 0))

theorem countAt_le_length (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) :
    c.countAt asg m ≤ c.busInteractions.length := by
  refine le_trans List.countP_le_length ?_
  simp only [Circuit.multsAt, List.length_map]
  exact le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map _))

/-- A list of `0`s and `1`s sums to its own count of nonzeros. -/
theorem sum_eq_countP {l : List (ZMod p)} (h : ∀ x ∈ l, x = 0 ∨ x = 1) :
    l.sum = (l.countP (fun v => decide (v ≠ 0)) : ZMod p) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, List.countP_cons, ih (fun x hx => h x (by simp [hx]))]
    -- `(1 : ZMod 1) = 0`, so the `1` branch still needs a case split.
    rcases h a (by simp) with rfl | rfl
    · simp
    · by_cases h1 : (1 : ZMod p) = 0 <;> simp [h1, add_comm]

theorem multsAt_zero_or_one {c : Circuit p} {bs : BusSemantics p} {asg : ChipAssignment p}
    {m : BusMessage p} (hsend : c.statelessSendOnly bs)
    (halg : ∀ e ∈ c.algebraicConstraints, e.eval asg = 0) (hm : bs.isStateful m.1 = false) :
    ∀ x ∈ c.multsAt asg m, x = 0 ∨ x = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  have hbus : bi.busId = m.1 := congrArg Prod.fst (of_decide_eq_true hy2)
  refine hsend asg halg bi hbi ?_
  rw [hbus]
  exact hm

theorem allEffects_eq_countAt {c : Circuit p} {bs : BusSemantics p} {asg : ChipAssignment p}
    {m : BusMessage p} (hsend : c.statelessSendOnly bs)
    (halg : ∀ e ∈ c.algebraicConstraints, e.eval asg = 0) (hm : bs.isStateful m.1 = false) :
    c.allEffects asg m = (c.countAt asg m : ZMod p) :=
  sum_eq_countP (multsAt_zero_or_one hsend halg hm)

theorem countAt_ne_zero {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ c.busInteractions)
    (hmsg : ((bi.eval asg).busId, (bi.eval asg).payload) = m)
    (hmult : (bi.eval asg).multiplicity ≠ 0) : c.countAt asg m ≠ 0 := by
  intro h
  have hmem : (bi.eval asg).multiplicity ∈ c.multsAt asg m :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_map_of_mem hbi, by simpa using hmsg⟩)
  have hzero := List.countP_eq_zero.mp h _ hmem
  simp only [decide_eq_true_eq, Bool.not_eq_true, decide_not, Bool.not_eq_false'] at hzero
  exact hmult hzero

/-- The natural-number analogue of `guestNet`, on one message. -/
def guestCount (G : List (Circuit p)) (gA : (t : Fin G.length) → List (ChipAssignment p))
    (m : BusMessage p) : ℕ :=
  ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).countAt asg m)).sum

theorem guestNet_eq_guestCount {G : List (Circuit p)}
    {gA : (t : Fin G.length) → List (ChipAssignment p)} {bs : BusSemantics p} {m : BusMessage p}
    (hsend : ∀ t, (G.get t).statelessSendOnly bs)
    (halg : ∀ t, ∀ asg ∈ gA t, ∀ e ∈ (G.get t).algebraicConstraints, e.eval asg = 0)
    (hm : bs.isStateful m.1 = false) :
    guestNet G gA m = (guestCount G gA m : ZMod p) := by
  show (∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg m)).sum) = _
  rw [guestCount]
  push_cast
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left (fun asg hasg => ?_))
  exact allEffects_eq_countAt (hsend t) (halg t asg hasg) hm

theorem guestCount_le {G : List (Circuit p)}
    {gA : (t : Fin G.length) → List (ChipAssignment p)} {m : BusMessage p} {L : ℕ}
    (hSize : ∀ t : Fin G.length, (G.get t).busInteractions.length ≤ L) :
    guestCount G gA m ≤ (∑ t : Fin G.length, (gA t).length) * L := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun t _ => ?_)
  refine le_trans (List.sum_le_card_nsmul _ L (fun x hx => ?_)) (by simp)
  obtain ⟨asg, -, rfl⟩ := List.mem_map.mp hx
  exact le_trans (countAt_le_length _ _ _) (hSize t)

/-- **The stateless half of the manuscript's `eq:stateless_as_pred`.** In a satisfying VM whose
    guest chips are send-only on stateless buses and small enough not to wrap `ZMod p`, an active
    stateless message leaves the guests with a genuinely nonzero net multiplicity — so balance
    forces a host chip to receive it. -/
theorem guestNet_ne_zero_of_active [Fact p.Prime] {host : Host p} {G : List (Circuit p)} {L : ℕ}
    {bs : BusSemantics p} {a : VmAssignment p ⟨host, G⟩} (hsat : VmSat ⟨host, G⟩ a)
    (hsend : ∀ t : Fin G.length, (G.get t).statelessSendOnly bs)
    (hSize : ∀ t : Fin G.length, (G.get t).busInteractions.length ≤ L)
    (hBudget : L * host.maxInstances < p)
    {t : Fin G.length} {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ (G.get t).busInteractions)
    {m : BusMessage p} (hmsg : ((bi.eval asg).busId, (bi.eval asg).payload) = m)
    (hmult : (bi.eval asg).multiplicity ≠ 0) (hm : bs.isStateful m.1 = false) :
    guestNet G a.guestAssignments m ≠ 0 := by
  have halg : ∀ t, ∀ asg ∈ a.guestAssignments t,
      ∀ e ∈ (G.get t).algebraicConstraints, e.eval asg = 0 := hsat.1
  have hpos : guestCount G a.guestAssignments m ≠ 0 := by
    intro h
    refine countAt_ne_zero hbi hmsg hmult ?_
    have hz := Finset.sum_eq_zero_iff.mp h t (Finset.mem_univ t)
    exact List.sum_eq_zero_iff.mp hz _ (List.mem_map_of_mem hasg)
  have hlt : guestCount G a.guestAssignments m < p :=
    lt_of_le_of_lt (le_trans (guestCount_le hSize) (Nat.mul_le_mul_right L hsat.2.2.2))
      (by rwa [Nat.mul_comm])
  rw [guestNet_eq_guestCount hsend halg hm]
  intro hcast
  refine hpos ?_
  have hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have := ZMod.val_cast_of_lt hlt
  rw [hcast, ZMod.val_zero] at this
  exact this.symm

/-- **`Host.forcesAccepts` is derivable.** Honest table sinks plus bus balancing plus the
    anti-wraparound budget give every guest instance the full `Circuit.satisfies`, not just its
    algebraic constraints. This is `bus_int.tex`'s stateless induction; the stateful half is
    assumed via `Circuit.statefulAccepts`. -/
theorem forcesAccepts_of_sinksAreTables [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    (hsinks : host.sinksAreTables bs) : host.forcesAccepts bs := by
  intro G L hLegal hSize hBudget a hsat t asg hasg
  refine ⟨hsat.1 t asg hasg, fun bi hbi hmult => ?_⟩
  by_cases hst : bs.isStateful bi.busId
  · exact (hLegal t).statefulOk asg (hsat.1 t asg hasg) bi hbi hst hmult
  · have hm : bs.isStateful ((bi.eval asg).busId, (bi.eval asg).payload).1 = false := by
      simpa using hst
    have hguest := guestNet_ne_zero_of_active hsat (fun t => (hLegal t).sendOnly) hSize hBudget
      hasg hbi rfl hmult hm
    have hbal := hsat.2.2.1 ((bi.eval asg).busId, (bi.eval asg).payload)
    have hhost : hostNet a.hostAssignment ((bi.eval asg).busId, (bi.eval asg).payload) ≠ 0 := by
      intro h
      exact hguest (by rw [netBus_apply, h, add_zero] at hbal; exact hbal)
    exact hsinks a.hostAssignment (hostLegal_of_satisfiesHost hsat.2.1) _ hm hhost
      (bi.eval asg).multiplicity hmult

--------- The soundness half of the connection ---------

theorem head_congr {α : Type _} {l l' : List α} (h : l = l') (hl : l ≠ []) (hl' : l' ≠ []) :
    l.head hl = l'.head hl' := by
  subst h; rfl

/-- Two assignments over the same host with the same input- and output-chip instances have the
    same observable effect, whatever their guest chips do. -/
theorem effects_eq_of_io {host : Host p} {G G' : List (Circuit p)}
    {a : VmAssignment p ⟨host, G⟩} {a' : VmAssignment p ⟨host, G'⟩}
    (h : VmSat ⟨host, G⟩ a) (h' : VmSat ⟨host, G'⟩ a')
    (hin : a.hostAssignment host.inputChip = a'.hostAssignment host.inputChip)
    (hout : a.hostAssignment host.outputChip = a'.hostAssignment host.outputChip) :
    a.effects h = a'.effects h' := by
  unfold VmAssignment.effects
  exact congrArg₂ VmEffect.mk
    (congrArg List.flatten (congrArg (List.map host.getInputChunk) hin))
    (congrArg host.getOutput (head_congr hout _ _))

/-- **The soundness half of the VM-level connection.** If every guest chip of `G'` is a sound
    replacement for the corresponding chip of `G`, then every effect the optimized guest chips
    can produce against `host`, the original guest chips can produce too.

    The witness keeps the host's stateful chips — memory, input, output — exactly as they were,
    replaces each guest instance's assignment by the one `Circuit.isSoundReplacementOf` promises,
    and lets `Host.absorbsStateless` rebuild the lookup chips around the difference. -/
theorem canProduce_of_isSoundReplacementOf
    {host : Host p} {bs : BusSemantics p} {G G' : List (Circuit p)} {L : ℕ}
    (hlen : G'.length = G.length)
    -- TODO: `hAccepts`, `hAbsorbs`, and `hLegal'` are all suspicious.
    -- `hlegal` seems most structurally acceptable, but its contents must be checked.
    (hAccepts : host.forcesAccepts bs) (hAbsorbs : host.absorbsStateless bs)
    (hLegal' : ∀ t : Fin G'.length, (G'.get t).legalGuest bs)
    (hSize' : ∀ t : Fin G'.length, (G'.get t).busInteractions.length ≤ L)
    (hBudget : L * host.maxInstances < p)
    (hSound : ∀ t : Fin G.length,
      (G'.get (Fin.cast hlen.symm t)).isSoundReplacementOf (G.get t) bs)
    {e : VmEffect p} (h : CanProduce ⟨host, G'⟩ e) : CanProduce ⟨host, G⟩ e := by
  obtain ⟨a', hsat', rfl⟩ := h
  -- Reindex `G`'s chip types into `G'`'s.
  set ι : Fin G.length → Fin G'.length := Fin.cast hlen.symm with hι
  -- The host forces every optimized guest instance to be `Circuit.satisfies`-good.
  have hsat'g : ∀ (t : Fin G'.length), ∀ asg ∈ a'.guestAssignments t,
      (G'.get t).satisfies bs asg := hAccepts G' L hLegal' hSize' hBudget a' hsat'
  -- Per instance, the original assignment soundness promises.
  set gA : (t : Fin G.length) → List (ChipAssignment p) :=
    fun t => (a'.guestAssignments (ι t)).map (soundWitness (G'.get (ι t)) (G.get t) bs) with hgA
  have hwit : ∀ (t : Fin G.length), ∀ asg ∈ a'.guestAssignments (ι t),
      (G.get t).satisfies bs (soundWitness (G'.get (ι t)) (G.get t) bs asg) ∧
        (G'.get (ι t)).sideEffects bs asg =
          (G.get t).sideEffects bs (soundWitness (G'.get (ι t)) (G.get t) bs asg) :=
    fun t asg hasg => soundWitness_spec ((hSound t).1 asg (hsat'g (ι t) asg hasg))
  have hsatG : ∀ (t : Fin G.length), ∀ asg ∈ gA t, (G.get t).satisfies bs asg := by
    intro t asg hasg
    obtain ⟨asg0, hasg0, rfl⟩ := List.mem_map.mp hasg
    exact (hwit t asg0 hasg0).1
  -- Stateful buses see no change at all: that is exactly what `sideEffects` preservation says.
  have hstateful : ∀ m : BusMessage p, bs.isStateful m.1 = true →
      guestNet G gA m = guestNet G' a'.guestAssignments m := by
    intro m hm
    show (∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg m)).sum) =
      ∑ t : Fin G'.length,
        ((a'.guestAssignments t).map (fun asg => (G'.get t).allEffects asg m)).sum
    refine Fintype.sum_equiv (finCongr hlen.symm) _ _ (fun t => ?_)
    show (((a'.guestAssignments (ι t)).map (soundWitness (G'.get (ι t)) (G.get t) bs)).map
        (fun asg => (G.get t).allEffects asg m)).sum =
      ((a'.guestAssignments (ι t)).map (fun asg => (G'.get (ι t)).allEffects asg m)).sum
    simp only [List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun asg hasg => ?_))
    show (G.get t).allEffects (soundWitness (G'.get (ι t)) (G.get t) bs asg) m =
      (G'.get (ι t)).allEffects asg m
    rw [allEffects_eq_sideEffects hm, allEffects_eq_sideEffects hm, ← (hwit t asg hasg).2]
  -- The stateless imbalance the replacement leaves behind.
  set δ : BusState p := fun m => guestNet G' a'.guestAssignments m - guestNet G gA m with hδ
  have hδspec : ∀ m : BusMessage p, δ m ≠ 0 →
      bs.isStateful m.1 = false ∧ ∃ mult : ZMod p, mult ≠ 0 ∧ bs.accepts ⟨m.1, mult, m.2⟩ := by
    intro m hm
    have hne : guestNet G' a'.guestAssignments m ≠ guestNet G gA m := sub_ne_zero.mp hm
    refine ⟨?_, ?_⟩
    · by_contra hst
      exact hne (hstateful m (by simpa using hst)).symm
    · -- Some instance, original or optimized, actively carries `m`; its chip `satisfies`.
      have hactive : ∃ (c : Circuit p) (asg : ChipAssignment p),
          c.satisfies bs asg ∧ c.allEffects asg m ≠ 0 := by
        by_cases hz : guestNet G' a'.guestAssignments m = 0
        · obtain ⟨t, asg, hasg, hne'⟩ :=
            exists_instance_of_guestNet_ne_zero (fun hc => hne (hz.trans hc.symm))
          exact ⟨G.get t, asg, hsatG t asg hasg, hne'⟩
        · obtain ⟨t, asg, hasg, hne'⟩ := exists_instance_of_guestNet_ne_zero hz
          exact ⟨G'.get t, asg, hsat'g t asg hasg, hne'⟩
      obtain ⟨c, asg, hcsat, hcne⟩ := hactive
      obtain ⟨bi, hbi, hmsg, hmult⟩ := exists_active_of_allEffects_ne_zero hcne
      refine ⟨(bi.eval asg).multiplicity, hmult, ?_⟩
      have : ((bi.eval asg).busId, (bi.eval asg).payload) = m := hmsg
      rw [← this]
      exact hcsat.2 bi hbi hmult
  obtain ⟨hA', hA'legal, hA'net, hA'in, hA'out⟩ :=
    hAbsorbs a'.hostAssignment (hostLegal_of_satisfiesHost hsat'.2.1) δ hδspec
  have hsat : VmSat (⟨host, G⟩ : Vm p) ⟨gA, hA'⟩ := by
    refine ⟨fun t asg hasg => (hsatG t asg hasg).1, hA'legal, ⟨fun m => ?_, ?_⟩⟩
    · have hb : guestNet G' a'.guestAssignments m + hostNet a'.hostAssignment m = 0 :=
        hsat'.2.2.1 m
      have hn : hostNet hA' m = hostNet a'.hostAssignment m + δ m := congrFun hA'net m
      rw [netBus_apply, hn, hδ]
      show guestNet G gA m +
        (hostNet a'.hostAssignment m +
          (guestNet G' a'.guestAssignments m - guestNet G gA m)) = 0
      linear_combination hb
    · -- Instance counts are preserved exactly (the new lists are `map`s), so the shared
      -- `Host`-level budget transfers.
      show (∑ t : Fin G.length, (gA t).length) ≤ host.maxInstances
      refine le_trans (le_of_eq ?_) hsat'.2.2.2
      exact Fintype.sum_equiv (finCongr hlen.symm) _ _ (fun t => List.length_map _)
  exact ⟨⟨gA, hA'⟩, hsat, effects_eq_of_io hsat hsat' hA'in hA'out⟩
