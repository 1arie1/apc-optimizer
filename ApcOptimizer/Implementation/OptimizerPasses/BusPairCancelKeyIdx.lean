import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqPre

set_option autoImplicit false

/-! # Address-key position index for `busPairCancel`'s region scans

A message can only fail a candidate's region tests if it is on the candidate's bus: every other
position is refuted by the bus-id arm and contributes the identity to the scan fold. For a candidate
whose address slots are all constants, it must in addition share the candidate's constant address
key or have a non-constant one, since a differing constant key is refuted by the constant-disequality
arm. `DenseKeyIdx` therefore indexes each bus's positions three ways — by constant address key
(`byKey`), the non-constant-key ones (`sym`), and all of them (`all`, what a candidate with a
non-constant key of its own scans) — so a scan visits only positions that can decide it. The walks
are bounded to the position window by `denseLowerBound`, and the shield stops at the first position
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

/-- Per-bus position index: `byKey` buckets the bus's all-constant-key positions by key hash, `sym`
    lists its non-constant-key positions, `all` every position on the bus (what a candidate with a
    non-constant key of its own must scan); all ascending. -/
structure DenseKeyIdx (p : ℕ) where
  byKey : Std.HashMap UInt64 (List Nat)
  sym : List Nat
  all : List Nat
  /-- `byKey`/`sym`/`all` as ascending arrays: the runtime walks these (`denseLiveAllGated`,
      `denseShieldEarly`) instead of materializing a filtered list per candidate. -/
  byKeyA : Std.HashMap UInt64 (Array Nat)
  symA : Array Nat
  allA : Array Nat

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
          { idx with byKey := idx.byKey.insert h (pos :: idx.byKey.getD h []),
                     all := pos :: idx.all }
      | none => { idx with sym := pos :: idx.sym, all := pos :: idx.all }
    else idx
  | none => idx

def denseKeyIdxBuild (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) : DenseKeyIdx p :=
  let idx := (List.range arr.size).foldr (denseKeyIdxAdd shape busId arr) ⟨∅, [], [], ∅, #[], #[]⟩
  { idx with byKeyA := idx.byKey.map (fun _ l => l.toArray), symA := idx.sym.toArray,
             allA := idx.all.toArray }

/-! ## Windowed access to the ascending index arrays

Every scan below runs over a position window (`[lo, hi)` for the mid test, `[0, bound)` for the
shield). The arrays are ascending, so the window is a contiguous index range, and the walks are
bounded by `denseLowerBound` instead of testing every entry: entries outside the range fail the
scan's own gate by sortedness, so bounding them away is value-identical. -/

/-- Binary search in the ascending `a` over index range `[lo, hi)`. -/
def denseLowerBoundGo (a : Array Nat) (x lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]?).getD 0 < x then denseLowerBoundGo a x (mid + 1) hi
    else denseLowerBoundGo a x lo mid
  else lo
  termination_by hi - lo
  decreasing_by all_goals omega

/-- The first index of the ascending `a` whose entry is `≥ x` (`a.size` if there is none). -/
def denseLowerBound (a : Array Nat) (x : Nat) : Nat := denseLowerBoundGo a x 0 a.size

/-! ## The index scans

The mid test walks the index arrays over the window's index range; the shield walks them
**descending from the window's top with an early exit**, since its verdict is decided by the topmost
visited live position `q` with `¬P q ∨ Q q` (`ok = P q`, `true` when there is none —
`denseShieldScanSegP_true_of`), so the positions below the last provable receive are never tested.
Both walks re-check the window at every entry, so the bounds only need to be sound, not tight. -/

/-- `P` at every live entry of `a` (indices `[start, n)`) whose position lies in `[lo, hi)`. The
    caller passes `start = denseLowerBound a lo` and `n = denseLowerBound a hi`, so the walk covers
    exactly the entries the window gate can accept. -/
@[specialize] def denseLiveAllGated {α : Type} (P : α → Bool) (preArr : Array α) (alive : Array Bool)
    (a : Array Nat) (lo hi start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    if n < start then true
    else
      (match a[n]? with
       | some pos =>
         if decide (lo ≤ pos) && decide (pos < hi) && alive[pos]?.getD false then
           (preArr[pos]?).elim true P
         else true
       | none => true)
        && denseLiveAllGated P preArr alive a lo hi start n

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
@[specialize] def denseShieldEarly {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
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

/-- Both region tests for one candidate over its two scan arrays: the mid walk over the index range
    the window `[i + 1, j)` maps to, and the descending shield below `i`. The shield's bounds sit
    inside the `&&`, so a failed mid test skips them. -/
@[inline] def denseScanDecide {α : Type} (Pmid Ppre Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) (b s : Array Nat) (i j : Nat) : Bool :=
  (denseLiveAllGated Pmid preArr alive b (i + 1) j (denseLowerBound b (i + 1))
      (denseLowerBound b j)
    && denseLiveAllGated Pmid preArr alive s (i + 1) j (denseLowerBound s (i + 1))
        (denseLowerBound s j))
  && (let nb := denseLowerBound b i
      let ns := denseLowerBound s i
      denseShieldEarly Ppre Q preArr alive b s i (nb + ns) nb ns)

end ApcOptimizer.Dense
