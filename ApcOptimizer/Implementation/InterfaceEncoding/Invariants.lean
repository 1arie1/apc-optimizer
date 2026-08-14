import ApcOptimizer.Implementation.InterfaceEncoding.Transfer

set_option autoImplicit false

/-! Proof machinery for transporting the Spec's invariants clause across `ConcreteEquiv`
under the multiplicity discipline. Not part of the audited surface. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-- A list of `0`s and `1`s sums to the number of `1`s in it. -/
theorem sum_eq_ones_length {l : List (ZMod p)} (h01 : ∀ x ∈ l, x = 0 ∨ x = 1) :
    l.sum = (((l.filter (fun x => decide (x = 1))).length : ℕ) : ZMod p) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have htl : ∀ x ∈ tl, x = 0 ∨ x = 1 := fun x hx => h01 x (List.mem_cons_of_mem _ hx)
    by_cases hd1 : hd = 1
    · rw [List.filter_cons_of_pos (by simp [hd1]), List.sum_cons, ih htl, List.length_cons,
        hd1, Nat.cast_add, Nat.cast_one, add_comm]
    · rw [List.filter_cons_of_neg (by simp [hd1]), List.sum_cons, ih htl,
        (h01 hd List.mem_cons_self).resolve_right hd1, zero_add]

/-- A sum of `0`s and `1`s containing at least one `1`, over fewer than `p` summands, cannot
    wrap around to `0`. -/
theorem sum_ne_zero_of_zero_one {l : List (ZMod p)} (h01 : ∀ x ∈ l, x = 0 ∨ x = 1)
    (hone : (1 : ZMod p) ∈ l) (hlen : l.length < p) : l.sum ≠ 0 := by
  have hpos : 0 < (l.filter (fun x => decide (x = 1))).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hone, by simp⟩)
  have hlt : (l.filter (fun x => decide (x = 1))).length < p :=
    lt_of_le_of_lt (List.length_filter_le _ _) hlen
  haveI : NeZero p := ⟨by omega⟩
  rw [sum_eq_ones_length h01]
  intro hzero
  have hval := ZMod.val_cast_of_lt hlt
  rw [hzero, ZMod.val_zero] at hval
  omega

/-- The evaluated messages of a circuit that land on a given key of a stateful bus — the list
    `Circuit.sideEffects` sums the multiplicities of. -/
def keyMessages (circuit : Circuit p) (bs : BusSemantics p) (a : Variable → ZMod p)
    (key : BusMessage p) : List (BusInteraction (ZMod p)) :=
  (circuit.busInteractions.map (fun bi => bi.eval a)).filter
    (fun m => bs.isStateful m.busId && decide ((m.busId, m.payload) = key))

theorem sideEffects_eq_keyMessages_sum (circuit : Circuit p) (bs : BusSemantics p)
    (a : Variable → ZMod p) (key : BusMessage p) :
    circuit.sideEffects bs a key =
      ((keyMessages circuit bs a key).map (fun m => m.multiplicity)).sum :=
  rfl

theorem mem_keyMessages {circuit : Circuit p} {bs : BusSemantics p} {a : Variable → ZMod p}
    {key : BusMessage p} {m : BusInteraction (ZMod p)} (hm : m ∈ keyMessages circuit bs a key) :
    (∃ bi ∈ circuit.busInteractions, bi.eval a = m) ∧ (m.busId, m.payload) = key := by
  obtain ⟨hmem, hfilter⟩ := List.mem_filter.mp hm
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hmem
  exact ⟨⟨bi, hbi, rfl⟩, of_decide_eq_true ((Bool.and_eq_true _ _).mp hfilter).2⟩

/-- A nonzero net multiplicity is witnessed by an active message on that key. -/
theorem exists_active_of_sideEffects_ne_zero {circuit : Circuit p} {bs : BusSemantics p}
    {a : Variable → ZMod p} {key : BusMessage p} (h : circuit.sideEffects bs a key ≠ 0) :
    ∃ bi ∈ circuit.busInteractions, (bi.eval a).multiplicity ≠ 0 ∧
      ((bi.eval a).busId, (bi.eval a).payload) = key := by
  rw [sideEffects_eq_keyMessages_sum] at h
  by_contra hcon
  refine h (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨⟨bi, hbi, rfl⟩, hkey⟩ := mem_keyMessages hm
  by_contra hz
  exact hcon ⟨bi, hbi, hz, hkey⟩

/-- Under the multiplicity discipline, a *send* on a stateful key is either canceled by a
    receive of the very same tuple, or leaves a nonzero net multiplicity. -/
theorem exists_recv_or_sideEffects_ne_zero {circuit : Circuit p} {bs : BusSemantics p}
    {a : Variable → ZMod p} (hsat : circuit.satisfies bs a)
    (hdisc : MultiplicityDiscipline circuit bs) (hlen : circuit.busInteractions.length < p)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ circuit.busInteractions)
    (hs : bs.isStateful (bi.eval a).busId = true) (hone : (bi.eval a).multiplicity = 1) :
    (∃ bi' ∈ circuit.busInteractions, (bi'.eval a).multiplicity = -1 ∧
        ((bi'.eval a).busId, (bi'.eval a).payload)
          = ((bi.eval a).busId, (bi.eval a).payload)) ∨
      circuit.sideEffects bs a ((bi.eval a).busId, (bi.eval a).payload) ≠ 0 := by
  by_cases hrecv : ∃ bi' ∈ circuit.busInteractions, (bi'.eval a).multiplicity = -1 ∧
      ((bi'.eval a).busId, (bi'.eval a).payload) = ((bi.eval a).busId, (bi.eval a).payload)
  · exact Or.inl hrecv
  refine Or.inr ?_
  set key : BusMessage p := ((bi.eval a).busId, (bi.eval a).payload) with hkey
  rw [sideEffects_eq_keyMessages_sum]
  refine sum_ne_zero_of_zero_one (fun x hx => ?_) ?_ ?_
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨bi', hbi', rfl⟩, hk⟩ := mem_keyMessages hm
    by_cases hz : (bi'.eval a).multiplicity = 0
    · exact Or.inl hz
    rcases hdisc a hsat bi' hbi' hz with h1 | ⟨_, hneg⟩
    · exact Or.inr h1
    · exact absurd ⟨bi', hbi', hneg, hk⟩ hrecv
  · refine List.mem_map.mpr ⟨bi.eval a, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨bi, hbi, rfl⟩, ?_⟩,
      hone⟩
    rw [Bool.and_eq_true]
    exact ⟨hs, by simp [hkey]⟩
  · have hle : (keyMessages circuit bs a key).length ≤ circuit.busInteractions.length := by
      simpa [keyMessages] using
        List.length_filter_le (fun m => bs.isStateful m.busId && decide ((m.busId, m.payload) = key))
          (circuit.busInteractions.map (fun bi => bi.eval a))
    simpa using lt_of_le_of_lt hle hlen

/-- OpenVM: the Spec's invariants clause crosses `ConcreteEquiv` once the optimized circuit
    obeys the multiplicity discipline. A send whose net contribution cancels must be canceled
    by a *receive* of the identical tuple, and `accepts` already forces receives to carry
    bytes; a send that leaves a net contribution is matched by an active message of the
    reference circuit on the same tuple. -/
theorem openVm_guaranteesInvariants_of_concreteEquiv (busMap : OpenVM.BusMap)
    (entryPc : Option (ZMod p)) {A B : Circuit p}
    (h : WitnessedBy (OpenVM.openVmBusSemantics p busMap entryPc) A B)
    (hA : A.guaranteesInvariants (OpenVM.openVmBusSemantics p busMap entryPc))
    (hdisc : MultiplicityDiscipline B (OpenVM.openVmBusSemantics p busMap entryPc))
    (hlen : B.busInteractions.length < p) :
    B.guaranteesInvariants (OpenVM.openVmBusSemantics p busMap entryPc) := by
  intro b hbsat bi hbi
  show (bi.eval b).multiplicity ≠ 0 →
    OpenVM.maintainsInvariants busMap (bi.eval b)
  intro hz
  haveI : Fact (1 < p) := ⟨lt_of_le_of_lt (List.length_pos_of_mem hbi) hlen⟩
  have hacc : OpenVM.accepts busMap (bi.eval b) := hbsat.2 bi hbi hz
  obtain ⟨t, hbus⟩ := openVm_busMap_isSome_of_accepts hacc
  have hpm : (bi.eval b).multiplicity = 1 ∨
      (t.isStateful = true ∧ (bi.eval b).multiplicity = -1) := by
    refine (hdisc b hbsat bi hbi hz).imp id (fun hr => ⟨?_, hr.2⟩)
    have : (OpenVM.openVmBusSemantics p busMap entryPc).isStateful (bi.eval b).busId
        = t.isStateful := by
      show (match busMap (bi.eval b).busId with
        | some u => u.isStateful | none => false) = t.isStateful
      rw [hbus]
    exact this ▸ hr.1
  have hstateless : t.isStateful = false → (bi.eval b).multiplicity = 1 := fun hf =>
    hpm.resolve_right (fun hr => by rw [hr.1] at hf; exact Bool.noConfusion hf)
  unfold OpenVM.maintainsInvariants
  rw [hbus]
  cases t with
  | pcLookup => exact hstateless rfl
  | variableRangeChecker => exact hstateless rfl
  | bitwiseLookup => exact hstateless rfl
  | tupleRangeChecker s1 s2 => exact hstateless rfl
  | executionBridge => exact hpm.imp id And.right
  | memory =>
    refine ⟨hpm.imp id And.right, ?_⟩
    cases hmp : OpenVM.memoryPayload? (bi.eval b).payload with
    | none => trivial
    | some f =>
      intro hchk d hd
      rcases hpm with hone | ⟨-, hneg⟩
      · -- A send: canceled by a receive of the same tuple, or matched on the reference side.
        have hstf : (OpenVM.openVmBusSemantics p busMap entryPc).isStateful
            (bi.eval b).busId = true := by
          show (match busMap (bi.eval b).busId with
            | some u => u.isStateful | none => false) = true
          rw [hbus]
          rfl
        have hnegz : ∀ m : BusInteraction (ZMod p), m.multiplicity = -1 → m.multiplicity ≠ 0 :=
          fun m hm hc => one_ne_zero (α := ZMod p) (neg_eq_zero.mp (hm ▸ hc))
        rcases exists_recv_or_sideEffects_ne_zero hbsat hdisc hlen hbi hstf hone with
          ⟨bi', hbi', hneg', hk⟩ | hne
        · have hbid : (bi'.eval b).busId = (bi.eval b).busId := congrArg Prod.fst hk
          have hpay : (bi'.eval b).payload = (bi.eval b).payload := congrArg Prod.snd hk
          exact openVm_accepts_memory_recv_bytes busMap _ (hbsat.2 bi' hbi' (hnegz _ hneg'))
            (hbid ▸ hbus) hneg' f (hpay ▸ hmp) hchk d hd
        · obtain ⟨a, hasat, heff, -⟩ := h b hbsat
          have hne' : A.sideEffects (OpenVM.openVmBusSemantics p busMap entryPc) a
              ((bi.eval b).busId, (bi.eval b).payload) ≠ 0 := by
            rw [congrFun heff]; exact hne
          obtain ⟨bi', hbi', hz', hk⟩ := exists_active_of_sideEffects_ne_zero hne'
          have hinv := hA a hasat bi' hbi' hz'
          have hbid : (bi'.eval a).busId = (bi.eval b).busId := congrArg Prod.fst hk
          have hpay : (bi'.eval a).payload = (bi.eval b).payload := congrArg Prod.snd hk
          have hinv' : OpenVM.maintainsInvariants busMap (bi'.eval a) := hinv
          unfold OpenVM.maintainsInvariants at hinv'
          rw [hbid, hbus, hpay, hmp] at hinv'
          exact hinv'.2 hchk d hd
      · exact openVm_accepts_memory_recv_bytes busMap _ hacc hbus hneg f hmp hchk d hd

end ApcOptimizer.Interface
