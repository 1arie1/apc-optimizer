import ApcOptimizer.InterfaceEncoding.Spec
import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Proof machinery for the Layer-1 (transfer) theorems of
`ApcOptimizer/InterfaceEncoding.lean`. Not part of the audited surface. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

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

/-- An interface message comes from evaluating one of the circuit's interactions. -/
theorem exists_interaction_of_mem_activeStateful {circuit : Circuit p} {bs : BusSemantics p}
    {a : Variable → ZMod p} {m : BusInteraction (ZMod p)}
    (hm : m ∈ activeStateful circuit bs a) :
    ∃ bi ∈ circuit.busInteractions, bi.eval a = m := by
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hm
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hmem
  exact ⟨bi, hbi, rfl⟩

/-- Lists related by an index bijection with pointwise-equal entries are permutations. -/
theorem perm_of_get_equiv {α : Type _} {l₁ l₂ : List α}
    (e : Fin l₁.length ≃ Fin l₂.length)
    (h : ∀ i, l₁.get i = l₂.get (e i)) : l₁.Perm l₂ := by
  have h₁ : l₁ = (List.finRange l₁.length).map (l₂.get ∘ ⇑e) := by
    rw [← List.ofFn_eq_map,
      show l₂.get ∘ ⇑e = l₁.get from funext fun i => (h i).symm, List.ofFn_get]
  have h₂ : l₂ = (List.finRange l₂.length).map l₂.get := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hstep : ((List.finRange l₁.length).map ⇑e).Perm (List.finRange l₂.length) := by
    refine (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange _).map e.injective) (List.nodup_finRange _)).mpr fun j => ?_
    exact ⟨fun _ => List.mem_finRange j,
      fun _ => List.mem_map.mpr ⟨e.symm j, List.mem_finRange _, e.apply_symm_apply j⟩⟩
  have hmain := hstep.map l₂.get
  rw [List.map_map, ← h₂] at hmain
  exact h₁.symm ▸ hmain

theorem interfaceMatch_of_paired {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : PairedMatch bs A B a b) : InterfaceMatch bs A B a b := by
  obtain ⟨e, he⟩ := h
  exact perm_of_get_equiv e he

/-- OpenVM's `accepts` grants the recv-byte invariant (`RecvBytes` in
    `ApcOptimizer/InterfaceEncoding.lean`, stated unfolded here). -/
theorem openVm_accepts_memory_recv_bytes (busMap : OpenVM.BusMap)
    (m : BusInteraction (ZMod p)) (hacc : OpenVM.accepts busMap m) :
    busMap m.busId = some .memory → m.multiplicity = -1 →
      ∀ f, OpenVM.memoryPayload? m.payload = some f →
        f.isByteChecked → ∀ d ∈ f.data, OpenVM.isByte d := by
  intro hbus hmult f hf
  unfold OpenVM.accepts at hacc
  split at hacc
  -- every non-memory arm carries an equation on `busMap m.busId` contradicting `hbus`;
  -- the memory arm reduces `hacc` to the inner match on `memoryPayload?`
  all_goals
    first
      | (rw [hf] at hacc; exact hacc hmult)
      | simp_all

end ApcOptimizer.Interface
