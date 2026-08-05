import ApcOptimizer.Implementation.OptimizerPasses.OneHotAnnihilate
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning

Impl-only recognisers: fixed-zero data-limb recogniser `denseCellZeroExprs` and filter predicate
`denseZeroPred`. Candidate collection, transform, proof, and wiring in `Proofs/ZeroRegister.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- For a memory message pinned to a fixed-zero cell (declared `zeroCell` shape, nonzero-constant
    multiplicity, and every fixed-address field matching), returns its data-slot expressions — each
    forced to `0`. Empty otherwise. -/
def denseCellZeroExprs (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  match facts.zeroCell bi.busId with
  | none => []
  | some (addrReq, dataSlots) =>
    match bi.multiplicity.constValue? with
    | none => []
    | some c =>
      if decide (c ≠ 0) &&
          addrReq.all (fun ar => decide (bi.payload[ar.1]? = some (DenseExpr.const ar.2))) then
        dataSlots.map (fun slot => (bi.payload[slot]?).getD (DenseExpr.const 0))
      else []

/-- Keep a candidate iff it is non-trivial and not already present. Every variable of a candidate
    occurs in the system by construction (it comes from an interaction payload), so no occurrence
    test is needed — see `denseZeroRegisterNew_vars`. -/
def denseZeroPred (cs : List (DenseExpr p)) (c : DenseExpr p) : Bool :=
  !c.normalize.fold.isConstZero && !cs.contains c

/-! ## Prepared per-invocation form

`facts.zeroCell` depends only on the bus id, and on OpenVM it allocates a `ZMod` ring dictionary per
call (the pinned address constants are `OfNat` numerals), so it must not run per interaction. -/

/-- One bus's fixed-zero-cell shape with the pinned address constants already wrapped as
    expressions: `(slot, const value)` pairs plus the data slots. -/
abbrev DenseZeroCell (p : ℕ) := List (Nat × DenseExpr p) × List Nat

/-- Add an interaction's bus id to the seen set. -/
def denseBusIdStep (ids : List Nat) (bi : BusInteraction (DenseExpr p)) : List Nat :=
  if ids.contains bi.busId then ids else bi.busId :: ids

/-- The distinct bus ids of an interaction list (one entry per bus in the system, so the
    `contains` stays on a handful of elements). -/
def denseBusIds (bis : List (BusInteraction (DenseExpr p))) : List Nat :=
  bis.foldl denseBusIdStep []

/-- `facts.zeroCell`, evaluated once per distinct bus id and kept only for the buses that declare a
    cell (typically just the memory bus). An empty table means the pass cannot fire. -/
def denseZeroCellTable (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) : List (Nat × DenseZeroCell p) :=
  (denseBusIds bis).filterMap (fun id =>
    match facts.zeroCell id with
    | none => none
    | some (addrReq, dataSlots) =>
      some (id, (addrReq.map (fun ar => (ar.1, DenseExpr.const ar.2)), dataSlots)))

/-- Whether every prepared address slot of `addr` holds exactly its pinned expression. -/
def denseAddrPinned (payload : List (DenseExpr p)) : List (Nat × DenseExpr p) → Bool
  | [] => true
  | (k, e) :: rest =>
    match payload[k]? with
    | none => false
    | some e' => e' == e && denseAddrPinned payload rest

/-- The data-slot expressions of `bi` that `keep` accepts, prepended to `acc`, if `bi` is an active
    message pinned to a fixed-zero cell of one of the `tbl` buses; `acc` otherwise. -/
def denseZeroCellEmit (tbl : List (Nat × DenseZeroCell p)) (keep : DenseExpr p → Bool)
    (bi : BusInteraction (DenseExpr p)) (acc : List (DenseExpr p)) : List (DenseExpr p) :=
  match tbl with
  | [] => acc
  | (id, addr, slots) :: rest =>
    if bi.busId == id then
      match bi.multiplicity.constValue? with
      | none => acc
      | some c =>
        if !zmodIsZero c && denseAddrPinned bi.payload addr then
          slots.foldl (fun a slot =>
            match bi.payload[slot]? with
            | some e => if keep e then e :: a else a
            | none => a) acc
        else acc
    else denseZeroCellEmit rest keep bi acc

end ApcOptimizer.Dense
