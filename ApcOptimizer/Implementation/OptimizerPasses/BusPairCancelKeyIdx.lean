import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqPre

set_option autoImplicit false

/-! # Constant-address-key position index for `busPairCancel`'s region scans

The mid/shield scans walked every position of their region per candidate pair — with tens of
thousands of accepted drops each re-scanning an `O(prefix)` region, the scan *volume* dominated
the pass. For a candidate whose address slots are all constants, a message can only fail the
region tests if it is on the same bus and either shares the candidate's constant address key or
has a non-constant key: every other position is refuted by the bus-id or constant-disequality arm
and contributes the identity to the scan fold. `DenseKeyIdx` buckets each bus's positions by
constant address key (plus a `sym` list for non-constant keys, and both as arrays), so the scans
below visit only the same-key and symbolic positions — and the shield stops at the first position
that decides it. `Proofs/BusPairCancelKeyIdx.lean` proves the builder sound and packages the scan
results back into the full-region forms (`denseRegionTests`). -/

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
  /-- `byKey`/`sym` as ascending arrays: the runtime walks these (`denseLiveAllGated`,
      `denseShieldEarly`) instead of materializing a filtered list per candidate. -/
  byKeyA : Std.HashMap UInt64 (Array Nat)
  symA : Array Nat

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
  let idx := (List.range arr.size).foldr (denseKeyIdxAdd shape busId arr) ⟨∅, [], ∅, #[]⟩
  { idx with byKeyA := idx.byKey.map (fun _ l => l.toArray), symA := idx.sym.toArray }

/-! ## The index scans

The mid test walks the index arrays with a window gate; the shield walks them **descending with an
early exit**, since its verdict is decided by the topmost visited live position `q` with
`¬P q ∨ Q q` (`ok = P q`, `true` when there is none — `denseShieldScanSegP_true_of`), so the
positions below the last provable receive are never tested. Both walks re-check the position window
at every entry, so the index needs no range search. -/

/-- `P` at every live entry of `a` (indices `[0, n)`) whose position lies in `[lo, hi)`. -/
def denseLiveAllGated {α : Type} (P : α → Bool) (preArr : Array α) (alive : Array Bool)
    (a : Array Nat) (lo hi : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    (match a[n]? with
     | some pos =>
       if decide (lo ≤ pos) && decide (pos < hi) && alive[pos]?.getD false then
         (preArr[pos]?).elim true P
       else true
     | none => true)
      && denseLiveAllGated P preArr alive a lo hi n

/-- One descending step of the shield: `some v` when position `pos` decides it (`v = P pos`), `none`
    when `pos` is outside the window, dead, or refuted without being a provable receive. -/
@[inline] def denseShieldDecide {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    (bound pos : Nat) : Option Bool :=
  if decide (pos < bound) && alive[pos]?.getD false then
    match preArr[pos]? with
    | some m =>
      match P m with
      | false => some false
      | true => if Q m then some true else none
    | none => none
  else none

/-- Descending early-exit shield over the entries of the two ascending arrays below `bound`: the
    larger of the two current tails is tested first, so entries are visited in descending position
    order and the walk stops at the topmost deciding one. `fuel` bounds the walk (`nb + ns`). -/
def denseShieldEarly {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    (b s : Array Nat) (bound : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, nb, ns =>
    match (if 0 < nb then b[nb - 1]? else none), (if 0 < ns then s[ns - 1]? else none) with
    | none, none => true
    | some pb, none =>
      match denseShieldDecide P Q preArr alive bound pb with
      | some v => v
      | none => denseShieldEarly P Q preArr alive b s bound fuel (nb - 1) ns
    | none, some ps =>
      match denseShieldDecide P Q preArr alive bound ps with
      | some v => v
      | none => denseShieldEarly P Q preArr alive b s bound fuel nb (ns - 1)
    | some pb, some ps =>
      if ps ≤ pb then
        match denseShieldDecide P Q preArr alive bound pb with
        | some v => v
        | none => denseShieldEarly P Q preArr alive b s bound fuel (nb - 1) ns
      else
        match denseShieldDecide P Q preArr alive bound ps with
        | some v => v
        | none => denseShieldEarly P Q preArr alive b s bound fuel nb (ns - 1)

/-- Descending early-exit shield over the whole segment `[0, n)` — the symbolic-key fallback, which
    has no index to walk. -/
def denseShieldEarlySeg {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    (bound : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    match denseShieldDecide P Q preArr alive bound n with
    | some v => v
    | none => denseShieldEarlySeg P Q preArr alive bound n

end ApcOptimizer.Dense
