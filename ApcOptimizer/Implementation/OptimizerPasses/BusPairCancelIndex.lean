import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelJustify
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Hash index and entailed-equality maps for `busPairCancel`

Per-invocation hash-indexing and entailed-equality machinery: `densePayloadHash`/`denseAddrHash`/
`denseRecvIndexAll` (receive-candidate index), `DenseVarCsIdx`, `DenseEqConstraintMap`, and
`densePayloadEntailedEq`. Impl-only (soundness in `Proofs/BusPairCancelIndex.lean`).

`denseRecvIndexAll` folds with `foldr` so bucket lists hold **ascending** positions — load-bearing,
since `denseFirstMatchAt` picks the first `i < j` match by scanning a bucket in list order. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The distinct bus ids of an interaction list, in `List.dedup` order (last occurrence wins), built
    without materializing one id per interaction. -/
def denseBusIdsOf (bis : List (BusInteraction (DenseExpr p))) : List Nat :=
  bis.foldr (fun bi acc => if acc.contains bi.busId then acc else bi.busId :: acc) []

/-- Structural hash of a payload (order-sensitive). -/
def densePayloadHash (pl : List (DenseExpr p)) : UInt64 :=
  pl.foldl (fun h e => mixHash h e.bHash) 7

/-- Structural hash of a payload's address slots (over `shape.addressFields`): the aggressive
    receive-index key, where value slots may differ syntactically but addresses must not. -/
def denseAddrHash (shape : MemoryBusShape) (pl : List (DenseExpr p)) : UInt64 :=
  shape.addressFields.foldl (fun h slot => mixHash h ((pl[slot]?).elim 5 DenseExpr.bHash)) 7

def denseRecvIndexGo {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (ops : DenseZModOps p) (arr : Array (BusInteraction (DenseExpr p))) :
    Nat → Std.HashMap UInt64 (List Nat) → Std.HashMap UInt64 (List Nat)
  | 0, m => m
  | n + 1, m =>
    denseRecvIndexGo facts aggressive ops arr n
      (match arr[n]? with
       | none => m
       | some bi =>
         match facts.memShape bi.busId with
         | some shape =>
           if decide (denseMultConst bi = some (denseGetPreviousMult ops shape)) then
             let h := mixHash (hash bi.busId)
               (if aggressive then denseAddrHash shape bi.payload else densePayloadHash bi.payload)
             m.insert h (n :: m.getD h [])
           else m
         | none => m)

/-- Ascending positions of the candidate receives (multiplicity `-shape.setNewMult`) on every
    memory-shaped bus, keyed by bus id mixed with the payload hash (`densePayloadHash`, or
    `denseAddrHash` when `aggressive`). One build serves the whole sweep. -/
def denseRecvIndexAll {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (ops : DenseZModOps p) (arr : Array (BusInteraction (DenseExpr p))) :
    Std.HashMap UInt64 (List Nat) :=
  denseRecvIndexGo facts aggressive ops arr arr.size ∅

/-- Does any position hold a send whose receive bucket is non-empty? A cheap over-approximation of
    "this invocation can accept a drop", short-circuiting at the first hit. It decides only whether
    the per-invocation indexes are built eagerly (`denseThunkIf`), so it carries no obligation: a
    wrong answer costs time, never soundness. -/
def denseAnyCandGo {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (ops : DenseZModOps p) (idx : Std.HashMap UInt64 (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) : Nat → Bool
  | 0 => false
  | n + 1 =>
    (match arr[n]? with
     | some bi =>
       match facts.memShape bi.busId with
       | some shape =>
         decide (denseMultConst bi = some (denseSetNewMult ops shape)) &&
           !(idx.getD (mixHash (hash bi.busId)
               (if aggressive then denseAddrHash shape bi.payload
                else densePayloadHash bi.payload)) []).isEmpty
       | none => false
     | none => false)
      || denseAnyCandGo facts aggressive ops idx arr n

def denseAnyCandidate {bs : BusSemantics p} (facts : BusFacts p bs) (aggressive : Bool)
    (ops : DenseZModOps p) (idx : Std.HashMap UInt64 (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) : Bool :=
  denseAnyCandGo facts aggressive ops idx arr arr.size

/-- A per-variable candidate-constraint index: for each variable, the constraints (in traversal
    order) known to mention it. -/
structure DenseVarCsIdx (p : ℕ) where
  map : Std.HashMap VarId (List (DenseExpr p))

namespace DenseVarCsIdx

def empty : DenseVarCsIdx p where
  map := ∅

/-- Append `c` at the end of `x`'s bucket (so buckets stay in traversal order), capped at
    `maxDeepConstraints`. -/
def insertC (I : DenseVarCsIdx p) (x : VarId) (c : DenseExpr p) : DenseVarCsIdx p :=
  match I.map[x]? with
  | none => { map := I.map.insert x [c] }
  | some old =>
    if old.length < maxDeepConstraints then { map := I.map.insert x (old ++ [c]) }
    else I

/-- Record `c` under each of its variables. -/
def addConstraint (I : DenseVarCsIdx p) (c : DenseExpr p) : DenseVarCsIdx p :=
  c.vars.dedup.foldl (fun I x => I.insertC x c) I

def addAll : DenseVarCsIdx p → List (DenseExpr p) → DenseVarCsIdx p
  | I, [] => I
  | I, c :: rest => addAll (I.addConstraint c) rest

def build (constraints : List (DenseExpr p)) : DenseVarCsIdx p :=
  addAll empty constraints

def lookup (I : DenseVarCsIdx p) (x : VarId) : List (DenseExpr p) :=
  (I.map[x]?).getD []

end DenseVarCsIdx

/-- A hash index of normalized constraints, bucketed by `DenseExpr.bHash` of the normalized form. -/
structure DenseEqConstraintMap (p : ℕ) where
  map : Std.HashMap UInt64 (List (DenseExpr p))

namespace DenseEqConstraintMap

def empty : DenseEqConstraintMap p where
  map := ∅

def insertNorm (M : DenseEqConstraintMap p) (n : DenseExpr p) : DenseEqConstraintMap p where
  map := M.map.insert n.bHash (n :: (M.map[n.bHash]?).getD [])

def addAll : DenseEqConstraintMap p → List (DenseExpr p) → DenseEqConstraintMap p
  | M, [] => M
  | M, c :: rest => addAll (M.insertNorm c.normalize) rest

def build (constraints : List (DenseExpr p)) : DenseEqConstraintMap p :=
  addAll empty constraints

/-- Is (the normalized) `d` one of the normalized constraints? -/
def test (M : DenseEqConstraintMap p) (d : DenseExpr p) : Bool :=
  match M.map[d.bHash]? with
  | some ns => ns.any (fun n => decide (n = d))
  | none => false

end DenseEqConstraintMap

/-- Slot-wise payload match with an entailed-equality escape hatch: each slot pair is syntactically
    equal, or its normalized difference (either orientation) is a normalized constraint. `M` is
    forced only at the first syntactic mismatch. -/
def densePayloadEntailedEq (M : Thunk (DenseEqConstraintMap p)) :
    List (DenseExpr p) → List (DenseExpr p) → Bool
  | [], [] => true
  | e :: es, e' :: es' =>
    (decide (e = e') || M.get.test (denseEqExpr e e').normalize
      || M.get.test (denseEqExpr e' e).normalize) && densePayloadEntailedEq M es es'
  | _, _ => false

end ApcOptimizer.Dense
