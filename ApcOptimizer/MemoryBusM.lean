import ApcOptimizer.MemoryBus
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics

set_option autoImplicit false

/-! # Order-free memory-bus discipline (PROPOSED audited replacement)

Proposed replacement for `admissibleMemoryBus` (`ApcOptimizer/MemoryBus.lean`) and for the
`admissible` fields of the OpenVM and SP1 semantics. Draft for review: on adoption,
`admissibleMemoryBusM` and its helpers merge into `MemoryBus.lean` (replacing
`admissibleMemoryBus`), the two `BusSemantics` instances change in place, and this file
disappears. Nothing here is consumed by the optimizer yet.

`admissibleMemoryBusM` is a property of the *multiset* of evaluated messages — it assumes
nothing about the order of the bus-interaction list (`admissibleMemoryBusM_perm`, and for the
full instances `OpenVM.openVmAdmissibleM_perm` / `SP1.sp1AdmissibleM_perm`). Per evaluated
address it asserts the multiset shadow of two system-level facts:

1. **Bus balance** — a received record is a sent record: matched receives consume send payload
   tuples injectively (the defining property of the global bus argument).
2. **Window atomicity** — per address, at most one record enters the block from outside (the
   entry receive); every other receive consumes an in-block send.

Together: at every address, the receives' payload multiset exceeds the sends' by at most one
element. Grouping is by *evaluated* address, so the statement is independent of how symbolic
addresses alias.

Contrast with the positional `admissibleMemoryBus`, which additionally trusts that the input
list is ordered by time and asserts payload copying between list-adjacent pairs. Under this
proposal that positional discipline becomes a *theorem* on the canonical access order
(`Implementation/MemoryBusMultiset.lean`, `interleaveAccesses_admissibleMemoryBus_of_M`), with
the forced-matching reasoning (`cascade_forced`) carried by machine-checked pass code instead of
by the audited assumption. The execution-bridge caveat is unchanged: treating it as a
single-cell memory bus still assumes the prover chooses to prove consecutive cycles. -/

variable {p : ℕ}

/-- The `getPrevious` messages of `M` at evaluated address `addr`. -/
def recvsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)

/-- The `setNew` messages of `M` at evaluated address `addr`. -/
def sendsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = shape.setNewMult ∧ shape.address m = addr)

/-- Order-free memory-bus discipline: at every evaluated address, the receives' payload multiset
    exceeds the sends' payload multiset by at most one element — the entry receive. -/
def admissibleMemoryBusM (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)),
    Multiset.card
      ((recvsAt shape addr M).map BusInteraction.payload
        - (sendsAt shape addr M).map BusInteraction.payload) ≤ 1

/-- The discipline is invariant under reordering the interaction list. -/
theorem admissibleMemoryBusM_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    admissibleMemoryBusM shape (L : Multiset (BusInteraction (ZMod p))) ↔
      admissibleMemoryBusM shape (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

namespace ApcOptimizer.OpenVM

/-- Proposed `admissible` for OpenVM: the order-free memory discipline per declared memory-shaped
    bus, plus the x0 convention. A one-token change from `openVmBusSemantics.admissible`. -/
def openVmAdmissibleM (busMap : BusMap) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  (∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
    admissibleMemoryBusM shape
      (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
  ∧ x0ReturnsZero busMap msgs

/-- The proposed OpenVM semantics: `openVmBusSemantics` with only `admissible` swapped. -/
def openVmBusSemanticsM (p : ℕ) (busMap : BusMap := defaultBusMap) : BusSemantics p :=
  { openVmBusSemantics p busMap with admissible := openVmAdmissibleM busMap }

/-- Auditor sanity: the whole proposed OpenVM rely is order-free. -/
theorem openVmAdmissibleM_perm (busMap : BusMap)
    {msgs msgs' : List (BusInteraction (ZMod p))} (h : msgs.Perm msgs') :
    openVmAdmissibleM busMap msgs ↔ openVmAdmissibleM busMap msgs' := by
  unfold openVmAdmissibleM x0ReturnsZero
  refine and_congr ?_ ?_
  · refine forall_congr' fun busId => forall_congr' fun shape => imp_congr Iff.rfl ?_
    exact admissibleMemoryBusM_perm shape (h.filter _)
  · exact forall_congr' fun m => imp_congr h.mem_iff Iff.rfl

end ApcOptimizer.OpenVM

namespace ApcOptimizer.SP1

/-- Proposed `admissible` for SP1: the order-free memory discipline per declared memory-shaped
    bus, plus the x0 convention. A one-token change from `sp1BusSemantics.admissible`. -/
def sp1AdmissibleM (busMap : BusMap) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  (∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
    admissibleMemoryBusM shape
      (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
  ∧ x0ReturnsZero busMap msgs

/-- The proposed SP1 semantics: `sp1BusSemantics` with only `admissible` swapped. -/
def sp1BusSemanticsM (p : ℕ) (busMap : BusMap := defaultBusMap) : BusSemantics p :=
  { sp1BusSemantics p busMap with admissible := sp1AdmissibleM busMap }

/-- Auditor sanity: the whole proposed SP1 rely is order-free. -/
theorem sp1AdmissibleM_perm (busMap : BusMap)
    {msgs msgs' : List (BusInteraction (ZMod p))} (h : msgs.Perm msgs') :
    sp1AdmissibleM busMap msgs ↔ sp1AdmissibleM busMap msgs' := by
  unfold sp1AdmissibleM x0ReturnsZero
  refine and_congr ?_ ?_
  · refine forall_congr' fun busId => forall_congr' fun shape => imp_congr Iff.rfl ?_
    exact admissibleMemoryBusM_perm shape (h.filter _)
  · exact forall_congr' fun m => imp_congr h.mem_iff Iff.rfl

end ApcOptimizer.SP1
