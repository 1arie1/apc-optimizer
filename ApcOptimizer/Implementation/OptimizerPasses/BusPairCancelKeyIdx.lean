import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqPre

set_option autoImplicit false

/-! # Constant-address-key position index for `busPairCancel`'s region scans

The mid/shield scans walked every position of their region per candidate pair — with tens of
thousands of accepted drops each re-scanning an `O(prefix)` region, the scan *volume* dominated
the pass. For a candidate whose address slots are all constants, a message can only fail the
region tests if it is on the same bus and either shares the candidate's constant address key or
has a non-constant key: every other position is refuted by the bus-id or constant-disequality arm
and contributes the identity to the scan fold. `DenseKeyIdx` buckets each bus's positions by
constant address key (plus a `sym` list for non-constant keys), so the sparse scans below visit
only the same-key and symbolic positions. `Proofs/BusPairCancelKeyIdx.lean` proves the builder
sound and packages the sparse results back into the full-region forms (`denseRegionTests`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The all-constant address key of an interaction under a shape (`none` if any address slot is
    missing or non-constant). -/
def denseAddrKeyOf (shape : MemoryBusShape) (bi : BusInteraction (DenseExpr p)) :
    Option (List (ZMod p)) :=
  shape.addressFields.foldr (fun slot acc =>
    match acc, (bi.payload[slot]?).bind DenseExpr.constValue? with
    | some ks, some c => some (c :: ks)
    | _, _ => none) (some [])

def denseKeyHash (k : List (ZMod p)) : UInt64 :=
  k.foldl (fun h c => mixHash h (hash c.val)) 7

/-- Per-bus constant-key position index: `byKey` buckets the bus's all-constant-key positions by
    key hash, `sym` lists its non-constant-key positions; both ascending. -/
structure DenseKeyIdx (p : ℕ) where
  byKey : Std.HashMap UInt64 (List Nat)
  sym : List Nat

/-- Insert one position (front of its bucket; the builder folds positions descending). -/
def denseKeyIdxAdd (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (pos : Nat) (idx : DenseKeyIdx p) :
    DenseKeyIdx p :=
  match arr[pos]? with
  | some m =>
    if m.busId = busId then
      match denseAddrKeyOf shape m with
      | some k =>
          let h := denseKeyHash k
          { idx with byKey := idx.byKey.insert h (pos :: idx.byKey.getD h []) }
      | none => { idx with sym := pos :: idx.sym }
    else idx
  | none => idx

def denseKeyIdxBuild (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) : DenseKeyIdx p :=
  (List.range arr.size).foldr (denseKeyIdxAdd shape busId arr) ⟨∅, []⟩

def denseMergeAsc : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: denseMergeAsc xs (y :: ys) else y :: denseMergeAsc (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-! ## The sparse scans -/

/-- `denseLiveAllSegP` restricted to a position list. -/
def denseLiveAllSparse {α : Type} (preArr : Array α) (alive : Array Bool)
    (P : α → Bool) : List Nat → Bool
  | [] => true
  | pos :: rest =>
    (if alive[pos]?.getD false then (preArr[pos]?).elim true P else true)
      && denseLiveAllSparse preArr alive P rest

/-- `denseShieldScanSegP` restricted to a position list. -/
def denseShieldScanSparse {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) : List Nat → Bool × Bool
  | [] => (false, true)
  | pos :: rest =>
    let r := denseShieldScanSparse P Q preArr alive rest
    if alive[pos]?.getD false then
      match preArr[pos]? with
      | some m0 => (r.1 || Q m0, r.2 && (P m0 || r.1))
      | none => r
    else r

end ApcOptimizer.Dense
