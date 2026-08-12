import ApcOptimizer.InterfaceEncoding.Spec

set_option autoImplicit false

/-! Proof machinery for the Layer-2 (closure) theorems of
`ApcOptimizer/InterfaceEncoding.lean`. Not part of the audited surface. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

theorem excessAt_le_entryMS_of_closes {shape : MemoryBusShape} {E : MemEnv p}
    {M : Multiset (BusInteraction (ZMod p))} (h : Closes shape E M)
    (addr : List (Option (ZMod p))) : excessAt shape addr M ≤ E.entryMS addr := by
  unfold excessAt
  rw [tsub_le_iff_right]
  calc (recvsAt shape addr M).map BusInteraction.payload
      ≤ (recvsAt shape addr M).map BusInteraction.payload + E.exitMS addr :=
        self_le_add_right _ _
    _ = (sendsAt shape addr M).map BusInteraction.payload + E.entryMS addr := h addr
    _ = E.entryMS addr + (sendsAt shape addr M).map BusInteraction.payload :=
        add_comm _ _

/-- A multiset of at most one element is an `Option`'s multiset. -/
theorem exists_option_rep {α : Type _} {s : Multiset α} (h : Multiset.card s ≤ 1) :
    ∃ o : Option α, s = o.elim 0 (fun x => {x}) := by
  rcases Nat.lt_or_ge (Multiset.card s) 1 with h0 | h1
  · exact ⟨none, Multiset.card_eq_zero.mp (Nat.lt_one_iff.mp h0)⟩
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp (le_antisymm h h1)
    exact ⟨some x, hx⟩

/-- Per address, both truncated differences of the payload multisets are `Option`-sized:
    the receive side by the window-atomicity rely, the send side because equinumerosity
    makes the two differences equinumerous (`card (a - b) + card b = card (a ∪ b)` and
    union is commutative). -/
theorem env_reps_of_admissible {shape : MemoryBusShape}
    {M : Multiset (BusInteraction (ZMod p))}
    (hM : admissibleMemoryBusM shape M)
    (hbal : ∀ addr : List (Option (ZMod p)),
      Multiset.card (recvsAt shape addr M) = Multiset.card (sendsAt shape addr M)) :
    ∀ addr : List (Option (ZMod p)),
      ∃ (e x : Option (List (ZMod p))),
        (recvsAt shape addr M).map BusInteraction.payload
            - (sendsAt shape addr M).map BusInteraction.payload
          = e.elim 0 (fun P => {P}) ∧
        (sendsAt shape addr M).map BusInteraction.payload
            - (recvsAt shape addr M).map BusInteraction.payload
          = x.elim 0 (fun P => {P}) := by
  intro addr
  set R := (recvsAt shape addr M).map BusInteraction.payload with hR
  set S := (sendsAt shape addr M).map BusInteraction.payload with hS
  have hRS : Multiset.card (R - S) ≤ 1 := hM addr
  have hcard : Multiset.card R = Multiset.card S := by
    rw [hR, hS, Multiset.card_map, Multiset.card_map, hbal addr]
  have hcard_sub : Multiset.card (S - R) = Multiset.card (R - S) := by
    have h1 : Multiset.card (R - S) + Multiset.card S
        = Multiset.card (S - R) + Multiset.card R := by
      rw [← Multiset.card_add, ← Multiset.card_add, ← Multiset.union_def,
        ← Multiset.union_def, Multiset.union_comm]
    omega
  have hSR : Multiset.card (S - R) ≤ 1 := by rw [hcard_sub]; exact hRS
  obtain ⟨e, he⟩ := exists_option_rep hRS
  obtain ⟨x, hx⟩ := exists_option_rep hSR
  exact ⟨e, x, he, hx⟩

/-- `s + (t - s) = t + (s - t)` — both sides are the union. -/
theorem add_sub_comm_union {α : Type _} [DecidableEq α] (s t : Multiset α) :
    s + (t - s) = t + (s - t) := by
  rw [add_comm, add_comm t, ← Multiset.union_def, ← Multiset.union_def]
  exact Multiset.union_comm _ _

/-- A closing environment's entry record is pinned by any excess payload. -/
theorem entry_eq_of_mem_excess {shape : MemoryBusShape} {E : MemEnv p}
    {M : Multiset (BusInteraction (ZMod p))} (h : Closes shape E M)
    {addr : List (Option (ZMod p))} {P : List (ZMod p)}
    (hP : P ∈ excessAt shape addr M) : E.entry addr = some P := by
  have hmem : P ∈ E.entryMS addr :=
    Multiset.mem_of_le (excessAt_le_entryMS_of_closes h addr) hP
  unfold MemEnv.entryMS at hmem
  cases hE : E.entry addr with
  | none => rw [hE, Option.elim_none] at hmem; exact absurd hmem (by simp)
  | some Q =>
    rw [hE, Option.elim_some] at hmem
    rw [Multiset.mem_singleton.mp hmem]

/-- The first receive of an address group presented in timestamp order matches no send, so
    its payload sits in the excess (the counting steps of `admissibleMemoryBusM_copies`,
    needing no admissibility hypothesis). -/
theorem recv_zero_in_excess {k : ℕ} (shape : MemoryBusShape)
    {M : Multiset (BusInteraction (ZMod p))} {addr : List (Option (ZMod p))}
    (send recv : Fin k → BusInteraction (ZMod p))
    (hsend : sendsAt shape addr M = Multiset.map send ↑(List.finRange k))
    (hrecv : recvsAt shape addr M = Multiset.map recv ↑(List.finRange k))
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hpay : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hmono : StrictMono fun i => tsVal (send i))
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i)) (h0 : 0 < k) :
    (recv ⟨0, h0⟩).payload ∈ excessAt shape addr M := by
  rw [excessAt, hsend, hrecv, Multiset.map_map, Multiset.map_map]
  -- receive 0 matches no send: anything it copied would have to be even earlier
  have h0un : ∀ j : Fin k, (recv ⟨0, h0⟩).payload ≠ (send j).payload := by
    intro j hj
    have h2 := hlt ⟨0, h0⟩
    rw [hpay _ _ hj] at h2
    exact absurd (hmono.lt_iff_lt.mp h2) (by simp [Fin.lt_def])
  rw [← Multiset.count_pos, Multiset.count_sub]
  have hz : Multiset.count ((recv ⟨0, h0⟩).payload)
      (Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hmem
    exact h0un j hj.symm
  have hpos : 0 < Multiset.count ((recv ⟨0, h0⟩).payload)
      (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)) := by
    refine Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨⟨0, h0⟩, ?_, rfl⟩)
    rw [Multiset.mem_coe]
    exact List.mem_finRange _
  omega

/-- Interface-matched runs place *equal* traffic multisets on every bus. -/
theorem busTraffic_eq_of_interfaceMatch {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b) (busId : Nat) :
    busTraffic A bs busId a = busTraffic B bs busId b :=
  Multiset.coe_eq_coe.mpr (h.filter _)

end ApcOptimizer.Interface
