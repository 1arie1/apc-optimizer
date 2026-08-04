import ApcOptimizer.MemoryBus
import ApcOptimizer.Implementation.MemoryBusCascade

set_option autoImplicit false

/-! # Order-free (multiset) memory-bus discipline

`admissibleMemoryBusM` is a candidate order-free replacement for the positional
`admissibleMemoryBus` (`ApcOptimizer/MemoryBus.lean`): a property of the *multiset* of evaluated
messages, invariant under any reordering of the bus-interaction list
(`admissibleMemoryBusM_perm`). Per evaluated address it states exactly what multiset bus balance
plus window atomicity provide: the receives' payload multiset exceeds the sends' by at most one
(the entry receive). `admissibleMemoryBusM_copies` is the consumption form: presenting one
address group as `k` accesses with strictly increasing send timestamps and the per-access
LessThan bound, every interior receive is forced to copy the previous send's payload
(via `cascade_forced`). -/

variable {p : ℕ}

/-! ## Multiset counting helpers -/

theorem two_le_card_of_mem_of_mem {α : Type*} {s : Multiset α} {a b : α}
    (hne : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) : 2 ≤ Multiset.card s := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hbt : b ∈ t := by
    rcases Multiset.mem_cons.mp hb with h | h
    · exact absurd h.symm hne
    · exact h
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hbt
  rw [Multiset.card_cons, Multiset.card_cons]
  omega

theorem two_le_card_of_two_le_count {α : Type*} [DecidableEq α] {s : Multiset α} {a : α}
    (h : 2 ≤ Multiset.count a s) : 2 ≤ Multiset.card s :=
  le_trans h (Multiset.count_le_card a s)

/-- Two distinct indices with equal images give a count of at least two in the image multiset. -/
theorem two_le_count_map_finRange {k : ℕ} {α : Type*} [DecidableEq α]
    (g : Fin k → α) {i i' : Fin k} (hne : i ≠ i') (h : g i = g i') :
    2 ≤ Multiset.count (g i) (Multiset.map g ↑(List.finRange k)) := by
  have hi : i ∈ (↑(List.finRange k) : Multiset (Fin k)) := by
    rw [Multiset.mem_coe]; exact List.mem_finRange i
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hi
  have hi' : i' ∈ t := by
    have hmem : i' ∈ (↑(List.finRange k) : Multiset (Fin k)) := by
      rw [Multiset.mem_coe]; exact List.mem_finRange i'
    rw [ht] at hmem
    rcases Multiset.mem_cons.mp hmem with hh | hh
    · exact absurd hh (Ne.symm hne)
    · exact hh
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hi'
  rw [ht, hu, Multiset.map_cons, Multiset.map_cons, Multiset.count_cons_self]
  have hpos : 0 < Multiset.count (g i) (g i' ::ₘ Multiset.map g u) := by
    rw [h, Multiset.count_cons_self]
    omega
  omega

/-! ## The order-free discipline -/

/-- The active `getPrevious` messages of `M` at evaluated address `addr`. -/
def recvsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)

/-- The active `setNew` messages of `M` at evaluated address `addr`. -/
def sendsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = shape.setNewMult ∧ shape.address m = addr)

/-- Order-free memory-bus discipline: at every evaluated address, the receives' payload multiset
    exceeds the sends' payload multiset by at most one element — the entry receive. This is the
    multiset shadow of bus balance plus window atomicity, and (unlike `admissibleMemoryBus`)
    mentions no ordering of the interaction list. -/
def admissibleMemoryBusM (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)),
    Multiset.card
      ((recvsAt shape addr M).map BusInteraction.payload
        - (sendsAt shape addr M).map BusInteraction.payload) ≤ 1

/-- The point of the definition: the discipline is invariant under reordering the interaction
    list. -/
theorem admissibleMemoryBusM_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    admissibleMemoryBusM shape (L : Multiset (BusInteraction (ZMod p))) ↔
      admissibleMemoryBusM shape (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

/-! ## Consumption -/

/-- Consumption form (the order-free `admissibleMemoryBus.consecutive`): present one address
    group as `k` accesses — access `i` receiving `recv i` and sending `send i` — with strictly
    increasing send timestamps and the LessThan bound, where the timestamp is computed from the
    payload alone. Then every interior receive copies the previous send's payload. -/
theorem admissibleMemoryBusM_copies {k : ℕ} (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p))) (addr : List (Option (ZMod p)))
    (hM : admissibleMemoryBusM shape M)
    (send recv : Fin k → BusInteraction (ZMod p))
    (hsend : sendsAt shape addr M = Multiset.map send ↑(List.finRange k))
    (hrecv : recvsAt shape addr M = Multiset.map recv ↑(List.finRange k))
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hpay : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hmono : StrictMono fun i => tsVal (send i))
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i)) :
    ∀ i : Fin k, 0 < i.val →
      (recv i).payload
        = (send ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).payload := by
  -- the group's payload budget, in composed-map form
  have hE := hM addr
  rw [hsend, hrecv, Multiset.map_map, Multiset.map_map] at hE
  -- send payloads are pairwise distinct (their timestamps are)
  have hgin : Function.Injective (BusInteraction.payload ∘ send) := by
    intro j j' hjj
    exact hmono.injective (hpay _ _ hjj)
  -- a receive's payload can only equal an earlier send's payload
  have hmatch_lt : ∀ i j : Fin k, (recv i).payload = (send j).payload → j < i := by
    intro i j hij
    have h1 : tsVal (recv i) = tsVal (send j) := hpay _ _ hij
    have h2 := hlt i
    rw [h1] at h2
    exact hmono.lt_iff_lt.mp h2
  -- count facts
  have hsend_le_one : ∀ P, Multiset.count P
      (Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) ≤ 1 := by
    intro P
    have hnd : (Multiset.map (BusInteraction.payload ∘ send)
        (↑(List.finRange k) : Multiset (Fin k))).Nodup := by
      refine Multiset.Nodup.map hgin ?_
      rw [Multiset.coe_nodup]; exact List.nodup_finRange k
    exact Multiset.nodup_iff_count_le_one.mp hnd P
  have hrecv_ge_one : ∀ i : Fin k, 1 ≤ Multiset.count ((recv i).payload)
      (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)) := by
    intro i
    refine Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨i, ?_, rfl⟩)
    rw [Multiset.mem_coe]; exact List.mem_finRange i
  have hsend_zero : ∀ (P : List (ZMod p)), (∀ j, P ≠ (send j).payload) →
      Multiset.count P (Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) = 0 := by
    intro P hP
    rw [Multiset.count_eq_zero]
    intro hmem
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hmem
    exact hP j hj.symm
  -- an unmatched receive's payload lands in the excess multiset
  have hexcess : ∀ i : Fin k, (∀ j, (recv i).payload ≠ (send j).payload) →
      (recv i).payload ∈
        (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)
          - Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) := by
    intro i hi
    rw [← Multiset.count_pos, Multiset.count_sub, hsend_zero _ hi]
    have := hrecv_ge_one i
    omega
  -- index 0's receive is unmatched: anything it copied would have to be even earlier
  have h0un : ∀ (hk : 0 < k) (j : Fin k), (recv ⟨0, hk⟩).payload ≠ (send j).payload := by
    intro hk j hj
    have h2 := hmatch_lt ⟨0, hk⟩ j hj
    rw [Fin.lt_def] at h2
    exact Nat.not_lt_zero j.val h2
  -- the forced matching
  have hforced := cascade_forced (fun i => tsVal (send i)) (fun i => tsVal (recv i)) hmono hlt
    (fun i => if h : ∃ j, (recv i).payload = (send j).payload then some h.choose else none)
    (by -- ts-keyed
      intro a b hab
      dsimp only at hab
      by_cases hex : ∃ j, (recv a).payload = (send j).payload
      · rw [dif_pos hex, Option.some_inj] at hab
        have hspec := hex.choose_spec
        rw [hab] at hspec
        exact hpay _ _ hspec
      · rw [dif_neg hex] at hab
        exact absurd hab (by simp))
    (by -- injective
      intro a a' c ha ha'
      dsimp only at ha ha'
      by_cases hexa : ∃ j, (recv a).payload = (send j).payload
      case neg => rw [dif_neg hexa] at ha; exact absurd ha (by simp)
      by_cases hexa' : ∃ j, (recv a').payload = (send j).payload
      case neg => rw [dif_neg hexa'] at ha'; exact absurd ha' (by simp)
      rw [dif_pos hexa, Option.some_inj] at ha
      rw [dif_pos hexa', Option.some_inj] at ha'
      by_contra hne
      have hsa := hexa.choose_spec
      have hsa' := hexa'.choose_spec
      rw [ha] at hsa
      rw [ha'] at hsa'
      -- both receives copy send c's payload: excess at that payload plus the entry payload
      have hpp : (recv a).payload = (recv a').payload := hsa.trans hsa'.symm
      have hc2 : 2 ≤ Multiset.count ((recv a).payload)
          (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)) :=
        two_le_count_map_finRange (BusInteraction.payload ∘ recv) hne hpp
      have hPmem : (recv a).payload ∈
          (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)
            - Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) := by
        rw [← Multiset.count_pos, Multiset.count_sub]
        have hle := hsend_le_one ((recv a).payload)
        omega
      have h0mem := hexcess ⟨0, a.pos⟩ (h0un a.pos)
      have hne0 : (recv a).payload ≠ (recv ⟨0, a.pos⟩).payload := by
        intro heq
        rw [heq] at hsa
        exact h0un a.pos c hsa
      exact absurd (two_le_card_of_mem_of_mem hne0 hPmem h0mem) (by omega))
    (by -- at most one entry
      intro a a' ha ha'
      dsimp only at ha ha'
      by_cases hexa : ∃ j, (recv a).payload = (send j).payload
      case pos => rw [dif_pos hexa] at ha; exact absurd ha (by simp)
      by_cases hexa' : ∃ j, (recv a').payload = (send j).payload
      case pos => rw [dif_pos hexa'] at ha'; exact absurd ha' (by simp)
      by_contra hne
      have hua : ∀ j, (recv a).payload ≠ (send j).payload := fun j hj => hexa ⟨j, hj⟩
      have hua' : ∀ j, (recv a').payload ≠ (send j).payload := fun j hj => hexa' ⟨j, hj⟩
      have hma := hexcess a hua
      have hma' := hexcess a' hua'
      by_cases hpp : (recv a).payload = (recv a').payload
      · -- identical unmatched payloads at two indices: excess count ≥ 2
        have hc2 : 2 ≤ Multiset.count ((recv a).payload)
            (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)) :=
          two_le_count_map_finRange (BusInteraction.payload ∘ recv) hne hpp
        have h2E : 2 ≤ Multiset.count ((recv a).payload)
            (Multiset.map (BusInteraction.payload ∘ recv) ↑(List.finRange k)
              - Multiset.map (BusInteraction.payload ∘ send) ↑(List.finRange k)) := by
          rw [Multiset.count_sub, hsend_zero _ hua]
          omega
        exact absurd (two_le_card_of_two_le_count h2E) (by omega)
      · exact absurd (two_le_card_of_mem_of_mem hpp hma hma') (by omega))
  -- extract the payload equality from the forced cascade
  intro i hi
  have hf := hforced i
  rw [if_pos hi] at hf
  dsimp only at hf
  by_cases hex : ∃ j, (recv i).payload = (send j).payload
  · rw [dif_pos hex, Option.some_inj] at hf
    have hspec := hex.choose_spec
    rw [hf] at hspec
    exact hspec
  · rw [dif_neg hex] at hf
    exact absurd hf (by simp)

/-! ## The canonical order witnesses the positional discipline

`interleaveAccesses` is the canonical access order: all `n` accesses of a bus in one global list
— sorted by send timestamp on the caller's side — with each receive immediately before its own
send (`r_0, s_0, r_1, s_1, …`). The order is global and address-blind: under any fixed
evaluation, each evaluated-address group is a subsequence of it, so it inherits the order
property whatever the aliasing turns out to be. `interleaveAccesses_admissibleMemoryBus` then
shows the positional discipline holds in this order given only the per-group copying fact
("every receive copies the latest same-address send before it", the conclusion of
`admissibleMemoryBusM_copies`): the only decompositions the discipline constrains are
group-consecutive send/receive pairs. -/

/-- The canonical interleaving `r_0, s_0, r_1, s_1, …` of `n` accesses. -/
def interleaveAccesses {α : Type*} {n : ℕ} (recv send : Fin n → α) : List α :=
  List.ofFn fun m : Fin (2 * n) =>
    if m.val % 2 = 0 then recv ⟨m.val / 2, by have := m.isLt; omega⟩
    else send ⟨m.val / 2, by have := m.isLt; omega⟩

theorem interleaveAccesses_length {α : Type*} {n : ℕ} (recv send : Fin n → α) :
    (interleaveAccesses recv send).length = 2 * n := by
  simp [interleaveAccesses]

theorem interleaveAccesses_getElem?_even {α : Type*} {n : ℕ} (recv send : Fin n → α)
    (i : Fin n) : (interleaveAccesses recv send)[2 * i.val]? = some (recv i) := by
  have hlt : 2 * i.val < 2 * n := by have := i.isLt; omega
  simp only [interleaveAccesses]
  rw [List.getElem?_ofFn, dif_pos hlt]
  have hd : 2 * i.val / 2 = i.val := by omega
  simp [hd]

theorem interleaveAccesses_getElem?_odd {α : Type*} {n : ℕ} (recv send : Fin n → α)
    (i : Fin n) : (interleaveAccesses recv send)[2 * i.val + 1]? = some (send i) := by
  have hlt : 2 * i.val + 1 < 2 * n := by have := i.isLt; omega
  simp only [interleaveAccesses]
  rw [List.getElem?_ofFn, dif_pos hlt]
  have hd : (2 * i.val + 1) / 2 = i.val := by omega
  simp [hd]

/-- Every position of the interleaving is a receive at an even index or a send at an odd one. -/
theorem interleaveAccesses_getElem?_cases {α : Type*} {n : ℕ} (recv send : Fin n → α)
    (m : ℕ) (hm : m < 2 * n) :
    (∃ i : Fin n, m = 2 * i.val ∧ (interleaveAccesses recv send)[m]? = some (recv i)) ∨
    (∃ i : Fin n, m = 2 * i.val + 1 ∧ (interleaveAccesses recv send)[m]? = some (send i)) := by
  by_cases h : m % 2 = 0
  · obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t := ⟨m / 2, by omega⟩
    have htn : t < n := by omega
    exact Or.inl ⟨⟨t, htn⟩, rfl, interleaveAccesses_getElem?_even recv send ⟨t, htn⟩⟩
  · obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    have htn : t < n := by omega
    exact Or.inr ⟨⟨t, htn⟩, rfl, interleaveAccesses_getElem?_odd recv send ⟨t, htn⟩⟩

/-! Positions of a `pre ++ S :: mid ++ R :: post` decomposition, in proof-free `getElem?` form.
The term parses as `(pre ++ (S :: mid)) ++ (R :: post)`, so the outer append peels first. -/

theorem getElem?_split_left {α : Type*} (pre mid post : List α) (S R : α) :
    (pre ++ S :: mid ++ R :: post)[pre.length]? = some S := by
  rw [List.getElem?_append_left
      (by simp only [List.length_append, List.length_cons]; omega),
    List.getElem?_append_right (le_refl pre.length), Nat.sub_self]
  exact List.getElem?_cons_zero

theorem getElem?_split_right {α : Type*} (pre mid post : List α) (S R : α) :
    (pre ++ S :: mid ++ R :: post)[pre.length + mid.length + 1]? = some R := by
  have hlen : (pre ++ S :: mid).length = pre.length + mid.length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  rw [List.getElem?_append_right (le_of_eq hlen), hlen, Nat.sub_self]
  exact List.getElem?_cons_zero

theorem getElem?_split_mid {α : Type*} (pre mid post : List α) (S R : α) (t : ℕ)
    (h1 : pre.length < t) (h2 : t < pre.length + mid.length + 1) {x : α}
    (hx : (pre ++ S :: mid ++ R :: post)[t]? = some x) : x ∈ mid := by
  rw [List.getElem?_append_left
      (by simp only [List.length_append, List.length_cons]; omega),
    List.getElem?_append_right (by omega)] at hx
  obtain ⟨k, hk⟩ : ∃ k, t - pre.length = k + 1 := ⟨t - pre.length - 1, by omega⟩
  rw [hk, List.getElem?_cons_succ] at hx
  exact List.mem_of_getElem? hx

/-- In the canonical order, the positional discipline reduces to per-group copying: given that
    every receive copies the latest same-address send before it (in access order), the whole
    interleaved list is `admissibleMemoryBus`. No aliasing assumption: `hcopy` speaks about the
    evaluated addresses, and each address group is a subsequence of the global order. -/
theorem interleaveAccesses_admissibleMemoryBus {n : ℕ} (shape : MemoryBusShape)
    (recv send : Fin n → BusInteraction (ZMod p))
    (hrm : ∀ i, (recv i).multiplicity = -shape.setNewMult)
    (hsm : ∀ i, (send i).multiplicity = shape.setNewMult)
    (hmne : -shape.setNewMult ≠ (shape.setNewMult : ZMod p))
    (hcopy : ∀ i j : Fin n, i < j → shape.address (send i) = shape.address (recv j) →
      (∀ m : Fin n, i < m → m < j → shape.address (send m) ≠ shape.address (recv j)) →
      (send i).payload = (recv j).payload) :
    admissibleMemoryBus shape (interleaveAccesses recv send) := by
  intro pre mid post S R hsplit hS hR haddrSR hmid
  have hlen2 : 2 * n = pre.length + mid.length + post.length + 2 := by
    have hh := congrArg List.length hsplit
    rw [interleaveAccesses_length] at hh
    simp [List.length_append] at hh
    omega
  have hSpos : (interleaveAccesses recv send)[pre.length]? = some S := by
    rw [hsplit]; exact getElem?_split_left pre mid post S R
  have hRpos : (interleaveAccesses recv send)[pre.length + mid.length + 1]? = some R := by
    rw [hsplit]; exact getElem?_split_right pre mid post S R
  rcases interleaveAccesses_getElem?_cases recv send pre.length (by omega)
    with ⟨t, -, htS⟩ | ⟨t, hta, htS⟩
  · -- S at an even position would be a receive: multiplicity clash
    rw [hSpos, Option.some_inj] at htS
    rw [htS, hrm t] at hS
    exact absurd hS hmne
  -- S = send t, at position 2t+1
  rw [hSpos, Option.some_inj] at htS
  rcases interleaveAccesses_getElem?_cases recv send (pre.length + mid.length + 1) (by omega)
    with ⟨u, hua, huR⟩ | ⟨u, -, huR⟩
  · -- R = recv u, at position 2u: the constrained pair
    rw [hRpos, Option.some_inj] at huR
    have htu : t < u := by rw [Fin.lt_def]; omega
    have hmids : ∀ m : Fin n, t < m → m < u →
        shape.address (send m) ≠ shape.address (recv u) := by
      intro m hm1 hm2 haddrm
      rw [Fin.lt_def] at hm1 hm2
      have hposm : (interleaveAccesses recv send)[2 * m.val + 1]? = some (send m) :=
        interleaveAccesses_getElem?_odd recv send m
      rw [hsplit] at hposm
      have hmem : send m ∈ mid :=
        getElem?_split_mid pre mid post S R (2 * m.val + 1) (by omega) (by omega) hposm
      have hmul : (send m).multiplicity ≠ 0 := by
        rw [hsm m]
        intro h0
        exact hmne (by rw [h0, neg_zero])
      have haddreq : shape.address (send m) = shape.address S := by
        rw [haddrm, ← huR, ← haddrSR]
      exact hmid (send m) hmem hmul haddreq
    have haddrtu : shape.address (send t) = shape.address (recv u) := by
      rw [← htS, ← huR]; exact haddrSR
    have hpay := hcopy t u htu haddrtu hmids
    rw [htS, huR]
    exact hpay
  · -- R at an odd position would be a send: multiplicity clash
    rw [hRpos, Option.some_inj] at huR
    rw [huR, hsm u] at hR
    exact absurd hR.symm hmne

/-! ## Glue: from the multiset discipline to the positional one

`interleaveAccesses_admissibleMemoryBus_of_M` composes the chain: an order-free
`admissibleMemoryBusM` multiset whose send/receive fibers are the access families, globally
increasing send timestamps, and the per-access LessThan bound make the canonical order
positionally `admissibleMemoryBus`. The address-group enumeration is a `filter` of the global
index order — a subsequence, inheriting its monotonicity under whatever aliasing the evaluated
addresses realize. -/

theorem pairwise_lt_finRange (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_finRange]
  exact Fin.mk_lt_mk.mpr hij

/-- Bridge from the order-free rely to the positional discipline on the canonical order. `M` is
    any message multiset whose active send/receive fibers are exactly the access families —
    e.g. a circuit's active stateful messages on this bus. -/
theorem interleaveAccesses_admissibleMemoryBus_of_M {n : ℕ} (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p)))
    (recv send : Fin n → BusInteraction (ZMod p))
    (hM : admissibleMemoryBusM shape M)
    (hMsends : M.filter (fun m => m.multiplicity = shape.setNewMult)
      = Multiset.map send ↑(List.finRange n))
    (hMrecvs : M.filter (fun m => m.multiplicity = -shape.setNewMult)
      = Multiset.map recv ↑(List.finRange n))
    (hmne : -shape.setNewMult ≠ (shape.setNewMult : ZMod p))
    (haddr : ∀ i, shape.address (recv i) = shape.address (send i))
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hpay : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hmono : StrictMono fun i => tsVal (send i))
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i)) :
    admissibleMemoryBus shape (interleaveAccesses recv send) := by
  -- the families' multiplicities, read off the fiber presentations
  have hsm : ∀ i, (send i).multiplicity = shape.setNewMult := by
    intro i
    have hmem : send i ∈ M.filter (fun m => m.multiplicity = shape.setNewMult) := by
      rw [hMsends]
      exact Multiset.mem_map.mpr ⟨i, by rw [Multiset.mem_coe]; exact List.mem_finRange i, rfl⟩
    exact Multiset.of_mem_filter (p := fun m : BusInteraction (ZMod p) => m.multiplicity = shape.setNewMult) hmem
  have hrm : ∀ i, (recv i).multiplicity = -shape.setNewMult := by
    intro i
    have hmem : recv i ∈ M.filter (fun m => m.multiplicity = -shape.setNewMult) := by
      rw [hMrecvs]
      exact Multiset.mem_map.mpr ⟨i, by rw [Multiset.mem_coe]; exact List.mem_finRange i, rfl⟩
    exact Multiset.of_mem_filter (p := fun m : BusInteraction (ZMod p) => m.multiplicity = -shape.setNewMult) hmem
  refine interleaveAccesses_admissibleMemoryBus shape recv send hrm hsm hmne ?_
  intro i j hij haij hbetween
  -- enumerate the address group of `recv j` as a sorted sublist of the global index order
  set l : List (Fin n) :=
    (List.finRange n).filter
      (fun m => decide (shape.address (send m) = shape.address (recv j))) with hl
  have hmem_l : ∀ m : Fin n, m ∈ l ↔ shape.address (send m) = shape.address (recv j) := by
    intro m
    rw [hl, List.mem_filter, decide_eq_true_eq]
    simp [List.mem_finRange]
  have hgetmono : StrictMono l.get := by
    intro q q' hqq
    have hpw := (pairwise_lt_finRange n).filter
      (fun m => decide (shape.address (send m) = shape.address (recv j)))
    rw [← hl, List.pairwise_iff_getElem] at hpw
    exact hpw q.val q'.val q.isLt q'.isLt hqq
  -- the group presentations of the multiset fibers
  have hfl : Multiset.filter (fun m => shape.address (send m) = shape.address (recv j))
      (↑(List.finRange n) : Multiset (Fin n)) = (↑l : Multiset (Fin n)) := by
    rw [hl]
    rfl
  have hlpres : Multiset.map l.get ↑(List.finRange l.length) = (↑l : Multiset (Fin n)) := by
    calc Multiset.map l.get ↑(List.finRange l.length)
        = (↑((List.finRange l.length).map l.get) : Multiset (Fin n)) := rfl
      _ = ↑l := by rw [← List.ofFn_eq_map, List.ofFn_get]
  have hsendsAt : sendsAt shape (shape.address (recv j)) M
      = Multiset.map (fun q => send (l.get q)) ↑(List.finRange l.length) := by
    have h1 : sendsAt shape (shape.address (recv j)) M
        = Multiset.filter (fun m => shape.address m = shape.address (recv j))
            (Multiset.filter (fun m => m.multiplicity = shape.setNewMult) M) := by
      simp only [sendsAt]
      rw [Multiset.filter_filter]
      exact Multiset.filter_congr fun m _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [h1, hMsends, Multiset.filter_map]
    have h2 : Multiset.filter ((fun m => shape.address m = shape.address (recv j)) ∘ send)
        (↑(List.finRange n) : Multiset (Fin n)) = ↑l := by
      rw [← hfl]
      rfl
    rw [h2, ← hlpres, Multiset.map_map]
    rfl
  have hrecvsAt : recvsAt shape (shape.address (recv j)) M
      = Multiset.map (fun q => recv (l.get q)) ↑(List.finRange l.length) := by
    have h1 : recvsAt shape (shape.address (recv j)) M
        = Multiset.filter (fun m => shape.address m = shape.address (recv j))
            (Multiset.filter (fun m => m.multiplicity = -shape.setNewMult) M) := by
      simp only [recvsAt]
      rw [Multiset.filter_filter]
      exact Multiset.filter_congr fun m _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [h1, hMrecvs, Multiset.filter_map]
    have h2 : Multiset.filter ((fun m => shape.address m = shape.address (recv j)) ∘ recv)
        (↑(List.finRange n) : Multiset (Fin n)) = ↑l := by
      rw [← hfl]
      exact Multiset.filter_congr fun m _ => by
        simp only [Function.comp_apply]
        rw [haddr m]
    rw [h2, ← hlpres, Multiset.map_map]
    rfl
  have hcopies := admissibleMemoryBusM_copies shape M (shape.address (recv j)) hM
    (fun q => send (l.get q)) (fun q => recv (l.get q)) hsendsAt hrecvsAt tsVal hpay
    (hmono.comp hgetmono) (fun q => hlt (l.get q))
  -- locate `i` and `j` in the group enumeration
  obtain ⟨qi, hqi⟩ := List.mem_iff_get.mp ((hmem_l i).mpr haij)
  obtain ⟨qj, hqj⟩ := List.mem_iff_get.mp ((hmem_l j).mpr (haddr j).symm)
  have hqij : qi < qj := by
    have hiff := hgetmono.lt_iff_lt (a := qi) (b := qj)
    rw [hqi, hqj] at hiff
    exact hiff.mp hij
  have hq0 : 0 < qj.val := by
    have h := hqij
    rw [Fin.lt_def] at h
    omega
  have hq'lt : qj.val - 1 < l.length := Nat.lt_of_le_of_lt (Nat.sub_le qj.val 1) qj.isLt
  -- the group predecessor of `j` is `i`: anything strictly between would violate `hbetween`
  have hpred : l.get ⟨qj.val - 1, hq'lt⟩ = i := by
    rcases Nat.lt_or_ge qi.val (qj.val - 1) with hlt1 | hge
    · exfalso
      have hm1 : i < l.get ⟨qj.val - 1, hq'lt⟩ := by
        rw [← hqi]
        exact hgetmono hlt1
      have hm2 : l.get ⟨qj.val - 1, hq'lt⟩ < j := by
        rw [← hqj]
        have hv : qj.val - 1 < qj.val := by omega
        exact hgetmono hv
      have hmA : shape.address (send (l.get ⟨qj.val - 1, hq'lt⟩)) = shape.address (recv j) :=
        (hmem_l _).mp (List.get_mem l _)
      exact hbetween _ hm1 hm2 hmA
    · have hq : qi = (⟨qj.val - 1, hq'lt⟩ : Fin l.length) := by
        have h := hqij
        rw [Fin.lt_def] at h
        exact Fin.ext (show qi.val = qj.val - 1 by omega)
      rw [← hq]
      exact hqi
  have hc : (recv (l.get qj)).payload = (send (l.get ⟨qj.val - 1, hq'lt⟩)).payload :=
    hcopies qj hq0
  rw [hqj, hpred] at hc
  exact hc.symm
