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

/-- Reindexing an `ofFn` list by a bijection permutes it. -/
theorem perm_ofFn_comp_equiv {γ : Type _} {m n : ℕ} (e : Fin m ≃ Fin n) (F : Fin n → γ) :
    (List.ofFn (F ∘ ⇑e)).Perm (List.ofFn F) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_map]
  refine List.Perm.map F ?_
  refine (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange _).map e.injective) (List.nodup_finRange _)).mpr fun j => ?_
  exact ⟨fun _ => List.mem_finRange j,
    fun _ => List.mem_map.mpr ⟨e.symm j, List.mem_finRange _, e.apply_symm_apply j⟩⟩

/-- Two mapped lists whose entries agree pointwise along an index bijection are
    permutations. -/
theorem perm_map_of_get_equiv {α β γ : Type _} {l₁ : List α} {l₂ : List β}
    {f : α → γ} {g : β → γ} (e : Fin l₁.length ≃ Fin l₂.length)
    (h : ∀ i, f (l₁.get i) = g (l₂.get (e i))) : (l₁.map f).Perm (l₂.map g) := by
  have h₁ : l₁.map f = List.ofFn ((g ∘ l₂.get) ∘ ⇑e) := by
    conv_lhs => rw [← List.ofFn_get l₁]
    rw [List.map_ofFn]
    exact congrArg _ (funext fun i => h i)
  have h₂ : l₂.map g = List.ofFn (g ∘ l₂.get) := by
    conv_lhs => rw [← List.ofFn_get l₂]
    rw [List.map_ofFn]
  rw [h₁, h₂]
  exact perm_ofFn_comp_equiv e (g ∘ l₂.get)

/-- The interface data is the evaluation of the syntactic stateful sublist, filtered to the
    active messages. -/
theorem activeStateful_eq_statefulEval (circuit : Circuit p) (bs : BusSemantics p)
    (a : Variable → ZMod p) :
    activeStateful circuit bs a
      = ((statefulInteractions circuit bs).map (fun bi => bi.eval a)).filter
          (fun m => decide (m.multiplicity ≠ 0)) := by
  unfold activeStateful statefulInteractions
  rw [List.filter_map, List.filter_map, List.filter_filter]
  exact congrArg _ (List.filter_congr fun bi _ => rfl)

/-- A circuit-level alignment induces the per-run interface match: the aligned evaluations
    are permutations, and activity coincides per pair (the messages are equal, multiplicity
    included), so the active filters stay matched. -/
theorem interfaceMatch_of_aligned {bs : BusSemantics p} {A B : Circuit p}
    {σ : Fin (statefulInteractions A bs).length ≃ Fin (statefulInteractions B bs).length}
    {a b : Variable → ZMod p} (h : AlignedMatch bs A B σ a b) :
    InterfaceMatch bs A B a b := by
  unfold InterfaceMatch
  rw [activeStateful_eq_statefulEval, activeStateful_eq_statefulEval]
  exact (perm_map_of_get_equiv
    (f := fun bi : BusInteraction (Expression p) => bi.eval a)
    (g := fun bi : BusInteraction (Expression p) => bi.eval b) σ h).filter _

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
