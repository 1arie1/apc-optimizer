import ApcOptimizer.InterfaceEncoding.Equiv
import ApcOptimizer.Implementation.MemoryBusMultiset

set_option autoImplicit false

/-! # Closure semantics: the interface observable is the whole memory behavior

`Transfer.lean` moves equivalence from the abstract to the concrete semantics; this file
justifies the observable itself — why "identical bus traffic" captures everything memory can
do. A memory *environment* (`MemEnv`) is what surrounds one block's window on one
memory-shaped bus: per evaluated address, the record the block's entry receive reads from
outside and the record it leaves behind for the outside to consume. Traffic *closes* with an
environment when, per address, consumption balances production (`Closes`).

Three results give the story its precise form. `admissibleMemoryBusM_of_closes` /
`exists_closes_of_admissible`: the audited window-atomicity rely says exactly "the traffic
admits an environment". `closes_recv_determined` (memory determinism): under any closing
environment, the nondeterministic receive payloads are a *function* of the environment and
the send history — the first receive reads the environment's entry record, and every later
receive copies the previous send. `interfaceMatch_closes_iff`: interface-matched runs close
with *the same* environments. Together: no memory environment can observe a difference
between interface-matched runs, or supply data distinguishing them — identical traffic means
identical closed compositions.

The alternative — an operational memory oracle stepping accesses in timestamp order — would
need a linear order on records and the TS_BOUND wrap-free arithmetic, machinery the interface
encoding deliberately avoids; here timestamp order enters only as the same abstract
presentation hypotheses `admissibleMemoryBusM_copies` already takes. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-- A memory environment for one memory-shaped bus, as seen through a block's window: per
    evaluated address, the record entering the block from outside (consumed by the entry
    receive) and the record the block leaves behind (its exit send). `Option`-valued per
    address — window atomicity is structural in the type. The execution bridge is the
    single-cell case (`addressFields = []`). -/
structure MemEnv (p : ℕ) where
  /-- The record the environment supplies at an address, if any. -/
  entry : List (Option (ZMod p)) → Option (List (ZMod p))
  /-- The record the environment consumes at an address, if any. -/
  exit : List (Option (ZMod p)) → Option (List (ZMod p))

/-- The entry record at an address, as a multiset (`0` or a singleton). -/
def MemEnv.entryMS (E : MemEnv p) (addr : List (Option (ZMod p))) :
    Multiset (List (ZMod p)) :=
  (E.entry addr).elim 0 (fun P => {P})

/-- The exit record at an address, as a multiset (`0` or a singleton). -/
def MemEnv.exitMS (E : MemEnv p) (addr : List (Option (ZMod p))) :
    Multiset (List (ZMod p)) :=
  (E.exit addr).elim 0 (fun P => {P})

/-- Traffic `M` closes with environment `E`: per address, consumption balances production —
    every received record is a sent record or the environment's entry record, and every sent
    record is received or left to the environment. -/
def Closes (shape : MemoryBusShape) (E : MemEnv p)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)),
    (recvsAt shape addr M).map BusInteraction.payload + E.exitMS addr
      = (sendsAt shape addr M).map BusInteraction.payload + E.entryMS addr

/-- The traffic a run places on one bus — a projection of the interface data. -/
def busTraffic (circuit : Circuit p) (bs : BusSemantics p) (busId : Nat)
    (a : Variable → ZMod p) : Multiset (BusInteraction (ZMod p)) :=
  ↑((activeStateful circuit bs a).filter (fun m => m.busId = busId))

/-! ## Closure and the audited rely -/

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

/-- Closing with some environment entails the audited window-atomicity rely: the environment
    supplies at most one record per address, so the receives' excess is at most one. -/
theorem admissibleMemoryBusM_of_closes {shape : MemoryBusShape} {E : MemEnv p}
    {M : Multiset (BusInteraction (ZMod p))} (h : Closes shape E M) :
    admissibleMemoryBusM shape M := by
  intro addr
  refine le_trans (Multiset.card_le_card (excessAt_le_entryMS_of_closes h addr)) ?_
  unfold MemEnv.entryMS
  cases E.entry addr <;> simp

/-- A multiset of at most one element is an `Option`'s multiset. -/
theorem exists_option_rep {α : Type _} {s : Multiset α} (h : Multiset.card s ≤ 1) :
    ∃ o : Option α, s = o.elim 0 (fun x => {x}) := by
  rcases Nat.lt_or_ge (Multiset.card s) 1 with h0 | h1
  · exact ⟨none, Multiset.card_eq_zero.mp (Nat.lt_one_iff.mp h0)⟩
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp (le_antisymm h h1)
    exact ⟨some x, hx⟩

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
  have hrep : ∀ addr : List (Option (ZMod p)),
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
    -- `card (a - b) + card b = card (a ∪ b)` and union is commutative, so with equal
    -- cardinalities the two truncated differences are equinumerous
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
  choose e x he hx using hrep
  refine ⟨⟨e, x⟩, fun addr => ?_⟩
  show (recvsAt shape addr M).map BusInteraction.payload + (x addr).elim 0 (fun P => {P})
      = (sendsAt shape addr M).map BusInteraction.payload + (e addr).elim 0 (fun P => {P})
  rw [← hx addr, ← he addr,
    add_comm ((recvsAt shape addr M).map BusInteraction.payload) _,
    add_comm ((sendsAt shape addr M).map BusInteraction.payload) _,
    ← Multiset.union_def, ← Multiset.union_def]
  exact Multiset.union_comm _ _

/-! ## Memory determinism under a closing environment -/

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

/-! ## Interface-matched runs have identical closed compositions -/

/-- Interface-matched runs place *equal* traffic multisets on every bus. -/
theorem busTraffic_eq_of_interfaceMatch {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b) (busId : Nat) :
    busTraffic A bs busId a = busTraffic B bs busId b :=
  Multiset.coe_eq_coe.mpr (h.filter _)

/-- Interface-matched runs close with the same environments, on every memory-shaped bus: no
    environment can observe a difference or supply data distinguishing the two runs. -/
theorem interfaceMatch_closes_iff {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatch bs A B a b)
    (shape : MemoryBusShape) (busId : Nat) (E : MemEnv p) :
    Closes shape E (busTraffic A bs busId a) ↔ Closes shape E (busTraffic B bs busId b) := by
  rw [busTraffic_eq_of_interfaceMatch h busId]

end ApcOptimizer.Interface
