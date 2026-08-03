import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainTable

set_option autoImplicit false

/-! # Dense `domainFold`, with compiled value-only evaluation

The hot evaluators (`denseGroupSurvivorsEV`, `denseConstOnSurvsV`) compile the group's covered
constraints once (via `DomainTable.lean`'s `IExpr`) and evaluate every enumerated point by index,
value-only (`List (ZMod p)` points, no `VarId` per point). Runs with at least
`domainFoldTargetIndexThreshold` candidate groups use the index-preserving indexed loop; fewer use
the direct loop. Runtime only — correctness is in `Proofs/DomainFold.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only eager enumeration of a group's domain -/

/-- Cartesian product of the group's per-variable domain values, value-only (each point a
    `List (ZMod p)` in the input domain-list order). -/
def denseAssignmentsV : List (List (ZMod p)) → List (List (ZMod p))
  | [] => [[]]
  | d :: rest => (denseAssignmentsV rest).flatMap (fun a => d.map (fun v => v :: a))

/-! ## The group's survivor filter, compiled once per target -/

/-- Whether every compiled covered constraint `ces` zeroes at point `pt`. -/
def denseSurvZeroCWV (ops : DenseZModOps p) (isZero : ZMod p → Bool) (ces : List (IExpr p))
    (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie))

/-- The surviving group values, value-only: covered constraints `es` compiled once over key list
    `xs`, every enumerated point checked by index. Falls back to the uncompiled filter only if
    compilation fails (dead for a covered set, kept for totality). -/
def denseGroupSurvivorsEV (es : List (DenseExpr p)) (xs : List VarId)
    (domVals : List (List (ZMod p))) : List (List (ZMod p)) :=
  match denseCompileEs xs es with
  | some ces =>
    let ops : DenseZModOps p := denseZModOps
    let dec : DecidableEq (ZMod p) := inferInstance
    let isZero : ZMod p → Bool := fun v => @decide (v = ops.zero) (dec v ops.zero)
    let surv : DenseSurvV p := ⟨fun pt => denseSurvZeroCWV ops isZero ces pt⟩
    (denseAssignmentsV domVals).filter surv.run
  | none =>
    (denseAssignmentsV domVals).filter
      (fun a => es.all (fun c => decide (c.eval (denseEnvOfKeysV xs a) = 0)))

/-! ## `constOnSurvs`, compiled per candidate node -/

/-- `some c` if `e` evaluates to the same constant `c` on every survivor, else `none`. `e` is
    compiled once over key list `xs` and every survivor checked by index (uncompiled fallback kept
    for totality). -/
def denseConstOnSurvsV (xs : List VarId) (survsV : List (List (ZMod p))) (e : DenseExpr p) :
    Option (ZMod p) :=
  match survsV with
  | [] => none
  | s₀ :: rest =>
    match denseCompileE xs e with
    | some ie =>
      let ops : DenseZModOps p := denseZModOps
      let v₀ := denseIExprEvalWithV ops s₀ ie
      if (s₀ :: rest).all (fun s => decide (denseIExprEvalWithV ops s ie = v₀))
      then some v₀ else none
    | none =>
      let v₀ := e.eval (denseEnvOfKeysV xs s₀)
      if (s₀ :: rest).all (fun s => decide (e.eval (denseEnvOfKeysV xs s) = v₀))
      then some v₀ else none

/-! ## The dense fold rewrite, value-only -/

/-- The recursive fold core, value-only survivors: replace every maximal wholly-in-group
    subexpression that is constant on the survivors by that constant; recurse otherwise. -/
def denseFoldRewriteGoV (xs : List VarId) (survsV : List (List (ZMod p))) :
    DenseExpr p → DenseExpr p
  | .const c => .const c
  | .var y => .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then
        match denseConstOnSurvsV xs survsV (.add a b) with
        | some c => .const c
        | none => .add (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
      else .add (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then
        match denseConstOnSurvsV xs survsV (.mul a b) with
        | some c => .const c
        | none => .mul (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)
      else .mul (denseFoldRewriteGoV xs survsV a) (denseFoldRewriteGoV xs survsV b)

/-- The fold rewrite, gated. -/
def denseFoldRewriteV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs || e.hasConstFoldableNode then denseFoldRewriteGoV xs survsV e else e

/-! ## The folded output -/

/-- Fold every non-covered constraint and every bus interaction; keep the covered (domain-pinning)
    constraints verbatim. -/
def denseFoldOutV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map (denseFoldRewriteV xs survsV)
        ++ denseCoveredCsOf d xs,
    busInteractions := d.busInteractions.map
      (fun bi => { bi with
        multiplicity := denseFoldRewriteV xs survsV bi.multiplicity,
        payload := bi.payload.map (denseFoldRewriteV xs survsV) }) }

/-! ## The no-op gates, value-only -/

/-- Does this expression have a maximal wholly-in-group subexpression that folds to a constant
    (value-only survivors)? Purely an efficiency gate. -/
def DenseExpr.hasFoldableV (xs : List VarId) (survsV : List (List (ZMod p))) : DenseExpr p → Bool
  | .const _ => false
  | .var _ => false
  | .add a b =>
      ((DenseExpr.add a b).varsInF xs && (denseConstOnSurvsV xs survsV (.add a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV
  | .mul a b =>
      ((DenseExpr.mul a b).varsInF xs && (denseConstOnSurvsV xs survsV (.mul a b)).isSome) ||
        a.hasFoldableV xs survsV || b.hasFoldableV xs survsV

/-- Does the fold change anything? The direct path's no-op efficiency gate; `csRest` is the
    caller's precomputed non-covered constraint list. -/
def denseSystemHasFoldableWV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) (csRest : List (DenseExpr p)) : Bool :=
  csRest.any (fun c => c.hasFoldableV xs survsV) ||
    d.busInteractions.any (fun bi =>
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV))

/-- The indexed path's no-op gate: scans only the items sharing a variable with `xs` through the
    prebuilt inverted indexes. -/
def denseSystemHasFoldableIdxV (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : Bool :=
  (((xs.flatMap (fun v => fidx.idx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arr.size then
      let c := fidx.arr[i]
      !denseCoveredBy xs c && c.hasFoldableV xs survsV
    else false)) ||
  (((xs.flatMap (fun v => fidx.bisIdx.buckets.getD v [])).foldl (·.insert ·)
      (∅ : Std.HashSet Nat)).toList.any (fun i =>
    if h : i < fidx.arrBis.size then
      let bi := fidx.arrBis[i]
      bi.multiplicity.hasFoldableV xs survsV || bi.payload.any (fun e => e.hasFoldableV xs survsV)
    else false))

/-! ## The direct (unindexed) fold loop

For runs with fewer than `domainFoldTargetIndexThreshold` candidate groups. -/

/-- One checked fold for a candidate group, given the covered set `es` and its complement `csRest`
    (the non-covered constraints, feeding the no-op gate). -/
def denseFoldStepWithV (d : DenseConstraintSystem p) (xs : List VarId)
    (es : List (DenseExpr p)) (csRest : List (DenseExpr p)) :
    DenseConstraintSystem p :=
  match denseGroupDoms es xs with
  | none => d
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableWV d xs survsV csRest then
        denseFoldOutV d xs survsV
      else d
    else d

/-- The direct fold loop: one `partition` per target splits the covered set `es` and complement
    `csRest`, no index. -/
def denseFoldLoopDirectV : List (List VarId) → DenseConstraintSystem p → DenseConstraintSystem p
  | [], d => d
  | xs :: rest, d =>
    match d.algebraicConstraints.partition (denseCoveredBy xs) with
    | (es, csRest) => denseFoldLoopDirectV rest (denseFoldStepWithV d xs es csRest)

/-! ## The index-preserving indexed-path rewrite

The indexed path uses an `anyVarIn`-only gate feeding an order- and length-preserving in-place fold,
so `DenseFoldIdx.refresh` keeps both inverted indexes without rebuilding across an accepted fold
(positions never move); `denseFoldOutIdxV` computes that fold sparsely, touching only bucketed
candidate positions. -/

/-- The indexed-path fold rewrite, gated by `anyVarIn` alone: an expression sharing no variable with
    the group is returned untouched, letting `denseFoldOutIdxV` skip it. -/
def denseFoldRewriteIdxV (xs : List VarId) (survsV : List (List (ZMod p)))
    (e : DenseExpr p) : DenseExpr p :=
  if e.anyVarIn xs then denseFoldRewriteGoV xs survsV e else e

/-- The in-place fold, order- and length-preserving: fold every non-covered constraint and bus
    interaction in place, keep the covered (domain-pinning) constraints verbatim in place. Positions
    never move and rewrites only shrink variable sets, so an accepted fold can refresh the index
    without rebuild. -/
def denseFoldOutInPlaceV (d : DenseConstraintSystem p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map
      (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c),
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
      payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) }) }

/-- The deduplicated set of bucket positions for the variables of `xs` — the positions an accepted
    fold can possibly touch. -/
def denseTouchedSet (idx : DenseCovIndex) (xs : List VarId) : Std.HashSet Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])).foldl (·.insert ·) ∅

/-- `denseFoldOutInPlaceV` computed sparsely: only candidate positions (bucketed under a variable of
    `xs`) are rewritten; all others pass through unchanged by position. -/
def denseFoldOutIdxV (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseConstraintSystem p :=
  let touchedCs : Std.HashSet Nat := denseTouchedSet fidx.idx xs
  let touchedBis : Std.HashSet Nat := denseTouchedSet fidx.bisIdx xs
  { algebraicConstraints := d.algebraicConstraints.zipIdx.map (fun ci =>
      if touchedCs.contains ci.2 then
        (if denseCoveredBy xs ci.1 then ci.1 else denseFoldRewriteIdxV xs survsV ci.1)
      else ci.1),
    busInteractions := d.busInteractions.zipIdx.map (fun bii =>
      if touchedBis.contains bii.2 then
        { bii.1 with
          multiplicity := denseFoldRewriteIdxV xs survsV bii.1.multiplicity,
          payload := bii.1.payload.map (denseFoldRewriteIdxV xs survsV) }
      else bii.1) }

/-! ## The indexed fold loop

For runs with at least `domainFoldTargetIndexThreshold` candidate groups; the covered set is served
from the prebuilt `DenseFoldIdx`, refreshed (no rebuild) only on an accepted fold. -/

/-- One checked fold served from the prebuilt covered-constraint index; an accepted fold is computed
    sparsely (`denseFoldOutIdxV`) and the index refreshed without rebuild (`fidx.refresh`). -/
def denseFoldStepV (d : DenseConstraintSystem p) (fidx : DenseFoldIdx p) (xs : List VarId) :
    DenseConstraintSystem p × DenseFoldIdx p :=
  let es := denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs
  match denseGroupDoms es xs with
  | none => (d, fidx)
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableIdxV fidx xs survsV then
        let ro := denseFoldOutIdxV d fidx xs survsV
        (ro, fidx.refresh ro)
      else (d, fidx)
    else (d, fidx)

/-- Process the candidate groups sequentially, threading and refreshing the index. -/
def denseFoldLoopV : List (List VarId) → DenseConstraintSystem p → DenseFoldIdx p →
    DenseConstraintSystem p
  | [], d, _ => d
  | xs :: rest, d, fidx =>
    let r := denseFoldStepV d fidx xs
    denseFoldLoopV rest r.1 r.2

/-! ## The array-native indexed fold loop (runtime twin)

`denseFoldLoopV` threads the *list* system `d` and re-materializes it per accepted fold:
`denseFoldOutIdxV` maps over `d.algebraicConstraints.zipIdx` / `d.busInteractions.zipIdx` (each an
O(system) `toArray` + rebuild) and `DenseFoldIdx.refresh` converts the folded lists back to arrays.
The twin below threads only the `DenseFoldIdx` (already array-backed) and applies an accepted fold
with `Array.modify` at the touched positions — O(touched) per accept — materializing lists once at
the pass exit. `denseDomainFoldFV_eq_fast` (`Proofs/DomainFold.lean`) proves it equal to
`denseDomainFoldFV` and installs it with `@[csimp]`. -/

/-- `denseFoldOutIdxV` + `refresh`, array-native: modify only the touched positions, in place. -/
def denseFoldOutArrV (fidx : DenseFoldIdx p) (xs : List VarId)
    (survsV : List (List (ZMod p))) : DenseFoldIdx p :=
  match fidx with
  | ⟨idx, arr, bisIdx, arrBis⟩ =>
    ⟨idx,
     (denseTouchedSet idx xs).toList.foldl
       (fun a i => a.modify i
         (fun c => if denseCoveredBy xs c then c else denseFoldRewriteIdxV xs survsV c)) arr,
     bisIdx,
     (denseTouchedSet bisIdx xs).toList.foldl
       (fun a i => a.modify i
         (fun bi => { bi with
           multiplicity := denseFoldRewriteIdxV xs survsV bi.multiplicity,
           payload := bi.payload.map (denseFoldRewriteIdxV xs survsV) })) arrBis⟩

/-- `denseFoldStepV`, array-native: the identical probe/gate served from the shared index, with an
    accepted fold applied sparsely by `denseFoldOutArrV`. -/
def denseFoldStepArrV (fidx : DenseFoldIdx p) (xs : List VarId) : DenseFoldIdx p :=
  let es := denseCoveredIdx fidx.idx fidx.arr (denseCoveredBy xs) xs
  match denseGroupDoms es xs with
  | none => fidx
  | some doms =>
    if (doms.map (fun yd => yd.2.length)).prod ≤ 256 then
      let survsV := denseGroupSurvivorsEV es xs (doms.map Prod.snd)
      if 1 ≤ survsV.length && denseSystemHasFoldableIdxV fidx xs survsV then
        denseFoldOutArrV fidx xs survsV
      else fidx
    else fidx

/-- Process the candidate groups sequentially, array-native. -/
def denseFoldLoopArrV : List (List VarId) → DenseFoldIdx p → DenseFoldIdx p
  | [], fidx => fidx
  | xs :: rest, fidx => denseFoldLoopArrV rest (denseFoldStepArrV fidx xs)

/-! ## The candidate group list -/

/-- The candidate fold targets: every constraint's 2–8-distinct-variable group all of whose
    variables occur in some single-variable constraint (`denseSvSet`), sorted by `VarId.index` and
    deduplicated. -/
def denseTargetsV (d : DenseConstraintSystem p) : List (List VarId) :=
  let svSet := denseSvSet d
  dedupHash (d.algebraicConstraints.filterMap (fun c =>
    let vs := HashedDedup.hashedDedup (hash ·) c.vars
    if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
      some (vs.mergeSort (fun a b => compare a.index b.index != .gt))
    else none))

/-! ## The pass -/

/-- Domain-constant subexpression folding: for a group of variables pinned to finite domains by
    "covered" constraints, enumerates the surviving joint assignments and replaces every
    wholly-in-group subexpression that is constant across all survivors by that constant. E.g. if
    the covered constraints force `x + y = 1` on every survivor, each `x + y` subterm folds to `1`. -/
def denseDomainFoldFV (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldTargetIndexThreshold ≤ targets.length then
      denseFoldLoopV targets d (DenseFoldIdx.mk' d)
    else denseFoldLoopDirectV targets d
  else d

/-! ## The redesigned engine

One invocation builds three index-keyed tables (`dfScanGo`, `dfCsBuckets`, `dfDoms`) and then walks
the targets, folding each item at most once per target through the fused gate-and-rewrite traversal
`dfGo`. See `domainFoldRedesign.md`. -/

/-- Insert into a `VarId.index`-ascending, duplicate-free list; `none` if `v` is already there, so a
    repeated occurrence costs a walk and no allocation. -/
def dfInsVar (v : VarId) : List VarId → Option (List VarId)
  | [] => some [v]
  | x :: rest =>
    if v.index < x.index then some (v :: x :: rest)
    else if v.index == x.index then none
    else (dfInsVar v rest).map (x :: ·)

/-- Is the list longer than `cap`? Walks at most `cap + 1` cells. -/
def dfLongerThan (cap : Nat) : List VarId → Bool
  | [] => false
  | _ :: rest => match cap with
    | 0 => true
    | cap + 1 => dfLongerThan cap rest

/-- The distinct variables of `e`, ascending by `VarId.index`; `none` once past `cap` of them, so
    oversized items abort instead of being fully deduplicated. -/
def dfVarsGo (cap : Nat) : DenseExpr p → Option (List VarId) → Option (List VarId)
  | _, none => none
  | .const _, acc => acc
  | .var i, some acc =>
      match dfInsVar i acc with
      | none => some acc
      | some a => if dfLongerThan cap a then none else some a
  | .add a b, acc => dfVarsGo cap b (dfVarsGo cap a acc)
  | .mul a b, acc => dfVarsGo cap b (dfVarsGo cap a acc)

/-- The largest index of an ascending `VarId` list. -/
def dfLastIdx : List VarId → Nat
  | [] => 0
  | [x] => x.index
  | _ :: rest => dfLastIdx rest

/-- One traversal of the constraints: the single-variable constraints' `(position, variable)` in
    reverse order (both `denseSvSet` and the domain sources), the 2–8-variable target candidate keys
    in reverse order (already in `denseVarSetKey` form), and the largest index seen. -/
def dfScanGo : List (DenseExpr p) → Nat → Nat → List (Nat × VarId) → List (List VarId) →
    Array (Option (List VarId)) → Nat × List (Nat × VarId) × List (List VarId) ×
      Array (Option (List VarId))
  | [], _, mx, sv, cand, dvs => (mx, sv, cand, dvs)
  | c :: rest, q, mx, sv, cand, dvs =>
    match dfVarsGo 8 c (some []) with
    | some [x] => dfScanGo rest (q + 1) (max mx x.index) ((q, x) :: sv) cand (dvs.push (some [x]))
    | some (x :: y :: more) =>
        dfScanGo rest (q + 1) (max mx (dfLastIdx (x :: y :: more))) sv ((x :: y :: more) :: cand)
          (dvs.push (some (x :: y :: more)))
    | some [] => dfScanGo rest (q + 1) mx sv cand (dvs.push (some []))
    | none => dfScanGo rest (q + 1) mx sv cand (dvs.push none)

/-- Mark a variable list in an index-keyed `Bool` table. -/
def dfMarkVars (vs : List VarId) (a : Array Bool) : Array Bool :=
  match vs with
  | [] => a
  | v :: rest => dfMarkVars rest (a.setIfInBounds v.index true)

/-- Mark every variable of every target key. -/
def dfMarkKeys (ks : List (Array VarId)) (a : Array Bool) : Array Bool :=
  match ks with
  | [] => a
  | k :: rest => dfMarkKeys rest (dfMarkVars k.toList a)

/-- The target keys: the candidates all of whose variables are `isSv`, deduplicated keeping each
    key's last occurrence (`dedupHash`'s order) — the input is the *reversed* candidate list, and the
    seen set is bucketed by the key's smallest variable index, so no key is ever hashed. -/
def dfDedupKeys (isSv : Array Bool) : List (List VarId) → Array (List (List VarId)) →
    List (Array VarId) → List (Array VarId)
  | [], _, acc => acc
  | vs :: rest, buckets, acc =>
    let h := (vs.head?.map VarId.index).getD 0
    let b := buckets.getD h []
    if b.contains vs then dfDedupKeys isSv rest buckets acc
    else
      let buckets := buckets.setIfInBounds h (vs :: b)
      if vs.all (fun v => isSv.getD v.index false) then
        dfDedupKeys isSv rest buckets (vs.toArray :: acc)
      else dfDedupKeys isSv rest buckets acc

/-- Push item position `q` under every target variable `e` mentions; duplicates are dropped against
    the bucket's last entry, so each bucket is strictly ascending. -/
def dfBucketGo (isTgt : Array Bool) (q : Nat) : DenseExpr p → Array (Array Nat) → Array (Array Nat)
  | .const _, bs => bs
  | .var v, bs =>
      if isTgt.getD v.index false then
        bs.modify v.index (fun b => if b.back? == some q then b else b.push q)
      else bs
  | .add a b, bs => dfBucketGo isTgt q b (dfBucketGo isTgt q a bs)
  | .mul a b, bs => dfBucketGo isTgt q b (dfBucketGo isTgt q a bs)

/-- Push `q` under every target variable of a known distinct-variable list. -/
def dfBucketVars (isTgt : Array Bool) (q : Nat) : List VarId → Array (Array Nat) →
    Array (Array Nat)
  | [], bs => bs
  | v :: rest, bs =>
      dfBucketVars isTgt q rest
        (if isTgt.getD v.index false then bs.modify v.index (fun b => b.push q) else bs)

/-- The constraint buckets, served from the scan's per-constraint distinct-variable lists; only the
    items the scan gave up on (over the 8-variable cap) are walked again. -/
def dfCsBuckets (isTgt : Array Bool) (dvs : Array (Option (List VarId))) :
    Nat → List (DenseExpr p) → Array (Array Nat) → Array (Array Nat)
  | _, [], bs => bs
  | q, c :: rest, bs =>
    match dvs.getD q none with
    | some vs => dfCsBuckets isTgt dvs (q + 1) rest (dfBucketVars isTgt q vs bs)
    | none => dfCsBuckets isTgt dvs (q + 1) rest (dfBucketGo isTgt q c bs)

def dfBiBucketGo (isTgt : Array Bool) (q : Nat) : List (DenseExpr p) → Array (Array Nat) →
    Array (Array Nat)
  | [], bs => bs
  | e :: rest, bs => dfBiBucketGo isTgt q rest (dfBucketGo isTgt q e bs)

def dfBisBuckets (isTgt : Array Bool) : Nat → List (BusInteraction (DenseExpr p)) →
    Array (Array Nat) → Array (Array Nat)
  | _, [], bs => bs
  | q, bi :: rest, bs =>
      dfBisBuckets isTgt (q + 1) rest
        (dfBiBucketGo isTgt q bi.payload (dfBucketGo isTgt q bi.multiplicity bs))

/-- The domain table and the 1-based source positions, from the single-variable constraints in
    position order: one `denseRootsIn` per target variable (first roots win), none for a variable no
    target needs. -/
def dfDoms (cs : Array (DenseExpr p)) (isTgt : Array Bool) (sv : List (Nat × VarId))
    (doms : Array (Option (List (ZMod p)))) (src : Array Nat) :
    Array (Option (List (ZMod p))) × Array Nat :=
  match sv with
  | [] => (doms, src)
  | (q, x) :: rest =>
    if isTgt.getD x.index false && (doms.getD x.index none).isNone then
      match (if h : q < cs.size then denseRootsIn x cs[q] else none) with
      | some ds =>
          dfDoms cs isTgt rest (doms.setIfInBounds x.index (some ds))
            (src.setIfInBounds x.index (q + 1))
      | none => dfDoms cs isTgt rest doms src
    else dfDoms cs isTgt rest doms src

/-! ### Per-target key lookup and the covered test -/

/-- The position of `y` in the ascending key array, or `none`. -/
def dfSlotGo (keys : Array VarId) (y : Nat) (j : Nat) : Option Nat :=
  if h : j < keys.size then
    let k := keys[j].index
    if k == y then some j else if y < k then none else dfSlotGo keys y (j + 1)
  else none
termination_by keys.size - j
decreasing_by all_goals omega

/-- `0` if a non-key variable occurs, `2` if every variable is a key and at least one occurs, `1` if
    variable-free — one short-circuiting walk for `denseCoveredBy`'s two. -/
def dfCovGo (keys : Array VarId) : DenseExpr p → Nat
  | .const _ => 1
  | .var y => if (dfSlotGo keys y.index 0).isSome then 2 else 0
  | .add a b | .mul a b =>
      let ra := dfCovGo keys a
      if ra == 0 then 0 else
      let rb := dfCovGo keys b
      if rb == 0 then 0 else max ra rb

def dfCoveredBy (keys : Array VarId) (c : DenseExpr p) : Bool := dfCovGo keys c == 2

/-! ### The survivor enumeration -/

/-- Compile `e` positionally against the key array. -/
def dfCompile (keys : Array VarId) : DenseExpr p → Option (IExpr p)
  | .const n => some (.const n)
  | .var y => (dfSlotGo keys y.index 0).map .ix
  | .add a b =>
      match dfCompile keys a, dfCompile keys b with
      | some ia, some ib => some (.add ia ib)
      | _, _ => none
  | .mul a b =>
      match dfCompile keys a, dfCompile keys b with
      | some ia, some ib => some (.mul ia ib)
      | _, _ => none

/-- The largest key position a compiled expression reads — the level at which it becomes fully
    assigned, keys being assigned in increasing order. `none` if it reads none. -/
def dfMaxIx : IExpr p → Option Nat
  | .const _ => none
  | .ix i => some i
  | .add a b | .mul a b =>
      match dfMaxIx a, dfMaxIx b with
      | some x, some y => some (max x y)
      | some x, none => some x
      | none, r => r

/-- Re-index a compiled filter for evaluation at its own level `m`: a partial point is the assigned
    prefix in *reverse* order (newest first), so key `i` sits at offset `m - i` and `.ix 0` is the
    value being assigned. -/
def dfShift (m : Nat) : IExpr p → IExpr p
  | .const n => .const n
  | .ix i => .ix (m - i)
  | .add a b => .add (dfShift m a) (dfShift m b)
  | .mul a b => .mul (dfShift m a) (dfShift m b)

/-- Evaluate a level-shifted filter on `v :: pt` without building the cons cell. Calls the field
    primitives directly: a `DenseZModOps` field is a closure, and this is the hottest loop of the
    pass. -/
def dfEvalCons (zero v : ZMod p) (pt : List (ZMod p)) : IExpr p → ZMod p
  | .const n => n
  | .ix 0 => v
  | .ix (i + 1) => denseLookupIxV zero pt i
  | .add a b => zmodAddP (dfEvalCons zero v pt a) (dfEvalCons zero v pt b)
  | .mul a b => zmodMulP (dfEvalCons zero v pt a) (dfEvalCons zero v pt b)

/-- Do all of this level's filters vanish on `v :: pt`? Closure-free. -/
def dfAllZero (zero v : ZMod p) (pt : List (ZMod p)) : List (IExpr p) → Bool
  | [] => true
  | ie :: rest => zmodIsZero (dfEvalCons zero v pt ie) && dfAllZero zero v pt rest

/-- Extend one partial point by every domain value, keeping those that pass this level's filters. -/
def dfExtOne (zero : ZMod p) (ies : List (IExpr p)) (pt : List (ZMod p)) :
    List (ZMod p) → Array (List (ZMod p)) → Array (List (ZMod p))
  | [], out => out
  | v :: vs, out =>
      dfExtOne zero ies pt vs (if dfAllZero zero v pt ies then out.push (v :: pt) else out)

def dfExtLevel (zero : ZMod p) (ies : List (IExpr p)) (dom : List (ZMod p))
    (i : Nat) (pts : Array (List (ZMod p))) (out : Array (List (ZMod p))) :
    Array (List (ZMod p)) :=
  if h : i < pts.size then
    dfExtLevel zero ies dom (i + 1) pts (dfExtOne zero ies pts[i] dom out)
  else out
termination_by pts.size - i
decreasing_by all_goals omega

/-- The surviving joint assignments, as reversed prefixes: each partial point is shared by every
    extension of it (one cons per surviving point, no allocation for a rejected one), and every
    filter is checked the moment its largest-index variable is assigned. -/
def dfEnumGo (zero : ZMod p) (byLevel : Array (List (IExpr p))) (doms : Array (List (ZMod p)))
    (k : Nat) (j : Nat) (pts : Array (List (ZMod p))) : Array (List (ZMod p)) :=
  if pts.isEmpty then pts
  else if h : j < k then
    dfEnumGo zero byLevel doms k (j + 1)
      (dfExtLevel zero (byLevel.getD j []) (doms.getD j []) 0 pts #[])
  else pts
termination_by k - j
decreasing_by all_goals omega

/-! ### The fused gate-and-rewrite traversal -/

/-- A subexpression's rewrite together with its value across the survivors: `out` mentions a non-key
    variable, `uni` is constant on every survivor, `vec` holds the per-survivor values and is
    normalized (never constant). `out` — by far the most common result — carries nothing, and a
    folded node's rewrite is always `.const c`, so it is rebuilt on demand rather than stored:
    together that leaves the traversal allocation-free at every node it does not change. -/
inductive DfRes (p : ℕ) where
  | out
  | outCh (e : DenseExpr p)
  | uni (c : ZMod p) (fold : Bool)
  | vec (a : Array (ZMod p)) (e? : Option (DenseExpr p))

def DfRes.e? : DfRes p → Option (DenseExpr p)
  | .out => none
  | .outCh e => some e
  | .uni c fold => if fold then some (.const c) else none
  | .vec _ e? => e?

/-- `decide (a = b)` for `p = 0`, where `ZMod.val` is `Int.natAbs` and identifies `1` with `-1`;
    kept in its own function so its dictionary stays off `dfEqZ`. Dead at runtime (`p` is prime). -/
def dfEqSlow (a b : ZMod p) : Bool := decide (a = b)

/-- Dictionary-free `ZMod` equality; see `zmodIsOne`. -/
def dfEqZ (a b : ZMod p) : Bool := if p = 0 then dfEqSlow a b else a.val == b.val

/-- The constant value of a survivor vector, if it has one. -/
def dfUni (a : Array (ZMod p)) : Option (ZMod p) :=
  if h : 0 < a.size then
    let c := a[0]
    if a.all (fun v => dfEqZ v c) then some c else none
  else none

/-- Rebuild a node only if a child changed. -/
@[inline] def dfRebuild (isAdd : Bool) (a b : DenseExpr p) (ra rb : Option (DenseExpr p)) :
    Option (DenseExpr p) :=
  match ra, rb with
  | none, none => none
  | _, _ => some (if isAdd then .add (ra.getD a) (rb.getD b) else .mul (ra.getD a) (rb.getD b))

/-- The field primitive selected by the node kind (see `dfEvalCons` on why not `DenseZModOps`). -/
@[inline] def dfOp (isAdd : Bool) (x y : ZMod p) : ZMod p :=
  if isAdd then zmodAddP x y else zmodMulP x y

/-- Combine an operation node's children: a `uni` result *is* "constant on every survivor", so the
    node folds to that constant. -/
@[inline] def dfComb (isAdd : Bool) (a b : DenseExpr p) (ra rb : DfRes p) : DfRes p :=
  match ra, rb with
  | .uni x _, .uni y _ => .uni (dfOp isAdd x y) true
  | .uni x _, .vec vb eb =>
      let s := vb.map (fun v => dfOp isAdd x v)
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ra.e? eb)
  | .vec va ea, .uni y _ =>
      let s := va.map (fun v => dfOp isAdd v y)
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ea rb.e?)
  | .vec va ea, .vec vb eb =>
      let s := Array.zipWith (dfOp isAdd) va vb
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ea eb)
  | _, _ =>
      match dfRebuild isAdd a b ra.e? rb.e? with
      | none => .out
      | some e => .outCh e

/-- The per-target fold context: the keys and each key's precomputed survivor column
    classification. -/
structure DfCtx (p : ℕ) where
  keys : Array VarId
  colRes : Array (DfRes p)

/-- The fused walk: one pass computes every node's survivor value and the rewrite in which every
    maximal constant in-key subexpression is replaced by its constant. -/
def dfGo (ctx : DfCtx p) : DenseExpr p → DfRes p
  | .const c => .uni c false
  | .var y =>
      match dfSlotGo ctx.keys y.index 0 with
      | some j => ctx.colRes.getD j .out
      | none => .out
  | .add a b => dfComb true a b (dfGo ctx a) (dfGo ctx b)
  | .mul a b => dfComb false a b (dfGo ctx a) (dfGo ctx b)

/-- Fold one expression. -/
def dfRewrite (ctx : DfCtx p) (e : DenseExpr p) : Option (DenseExpr p) := (dfGo ctx e).e?

def dfRewriteList (ctx : DfCtx p) : List (DenseExpr p) → Option (List (DenseExpr p))
  | [] => none
  | e :: rest =>
    match dfRewrite ctx e, dfRewriteList ctx rest with
    | none, none => none
    | r, rs => some (r.getD e :: rs.getD rest)

def dfRewriteBi (ctx : DfCtx p) (bi : BusInteraction (DenseExpr p)) :
    Option (BusInteraction (DenseExpr p)) :=
  match dfRewrite ctx bi.multiplicity, dfRewriteList ctx bi.payload with
  | none, none => none
  | m, pl => some { bi with multiplicity := m.getD bi.multiplicity, payload := pl.getD bi.payload }

/-! ### The per-target step -/

/-- The per-invocation index: the two position bucket tables, the domain table and the 1-based
    domain-source positions, all keyed by `VarId.index`. -/
structure DfIdx (p : ℕ) where
  csB : Array (Array Nat)
  bisB : Array (Array Nat)
  doms : Array (Option (List (ZMod p)))
  src : Array Nat

/-- The nonempty buckets of the target's keys. -/
def dfSlices (buckets : Array (Array Nat)) (keys : Array VarId) : Array (Array Nat) :=
  keys.foldl (init := #[]) fun acc v =>
    let b := buckets.getD v.index #[]
    if b.isEmpty then acc else acc.push b

/-- The smallest unconsumed bucket head. -/
def dfMinHead (bs : Array (Array Nat)) (cur : Array Nat) (i : Nat) (best : Nat) (found : Bool) :
    Option Nat :=
  if h : i < bs.size then
    let b := bs[i]
    let c := cur.getD i 0
    if hc : c < b.size then
      let v := b[c]
      if !found || v < best then dfMinHead bs cur (i + 1) v true
      else dfMinHead bs cur (i + 1) best found
    else dfMinHead bs cur (i + 1) best found
  else if found then some best else none
termination_by bs.size - i
decreasing_by all_goals omega

/-- Consume `m` from every bucket whose head is `m`. -/
def dfAdvance (bs : Array (Array Nat)) (m : Nat) (i : Nat) (cur : Array Nat) : Array Nat :=
  if h : i < bs.size then
    let b := bs[i]
    let c := cur.getD i 0
    if hc : c < b.size then
      if b[c] == m then dfAdvance bs m (i + 1) (cur.setIfInBounds i (c + 1))
      else dfAdvance bs m (i + 1) cur
    else dfAdvance bs m (i + 1) cur
  else cur
termination_by bs.size - i
decreasing_by all_goals omega

def dfMergeGo (bs : Array (Array Nat)) (cur : Array Nat) (out : Array Nat) (fuel : Nat) :
    Array Nat :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
    match dfMinHead bs cur 0 0 false with
    | none => out
    | some m => dfMergeGo bs (dfAdvance bs m 0 cur) (out.push m) fuel

/-- The target's touched positions: the ascending, deduplicated union of its keys' buckets. -/
def dfTouched (buckets : Array (Array Nat)) (keys : Array VarId) : Array Nat :=
  let bs := dfSlices buckets keys
  dfMergeGo bs (Array.replicate bs.size 0) #[] (bs.foldl (fun n b => n + b.size) 0)

/-- The keys' domains, all-or-nothing. -/
def dfKeyDoms (doms : Array (Option (List (ZMod p)))) (keys : Array VarId) :
    Option (Array (List (ZMod p))) :=
  keys.foldl (init := some #[]) fun acc v =>
    match acc, doms.getD v.index none with
    | some a, some d => some (a.push d)
    | _, _ => none

/-- Is position `q` the domain source of one of the keys? Such a constraint is zero at every box
    point by construction, so it never rejects one. -/
def dfIsSrc (src : Array Nat) (keys : Array VarId) (q : Nat) : Bool :=
  keys.any (fun v => src.getD v.index 0 == q + 1)

/-- Walk the touched constraints once: which are covered (parallel to `touched`), and the compiled
    filters the enumeration needs (the covered ones that are not domain sources). -/
def dfCovScan (keys : Array VarId) (src : Array Nat) (cs : Array (DenseExpr p))
    (touched : Array Nat) (i : Nat) (mask : Array Bool) (filters : Array (Nat × IExpr p)) :
    Array Bool × Array (Nat × IExpr p) :=
  if h : i < touched.size then
    let q := touched[i]
    let c := cs.getD q (.const (zmodZeroP p))
    if dfCoveredBy keys c then
      if dfIsSrc src keys q then dfCovScan keys src cs touched (i + 1) (mask.push true) filters
      else
        match dfCompile keys c with
        | some ie =>
            let m := (dfMaxIx ie).getD 0
            dfCovScan keys src cs touched (i + 1) (mask.push true) (filters.push (m, dfShift m ie))
        | none => dfCovScan keys src cs touched (i + 1) (mask.push true) filters
    else dfCovScan keys src cs touched (i + 1) (mask.push false) filters
  else (mask, filters)
termination_by touched.size - i
decreasing_by all_goals omega

/-- Bucket the filters by the level at which they become fully assigned. -/
def dfLevels (k : Nat) (filters : Array (Nat × IExpr p)) : Array (List (IExpr p)) :=
  filters.foldl (init := Array.replicate k ([] : List (IExpr p)))
    fun a mie => a.modify (min mie.1 (k - 1)) (mie.2 :: ·)

/-- Each key's survivor column, classified once per target; a survivor is the reversed assignment,
    so key `j` sits at offset `k - 1 - j`. -/
def dfColRes (survs : Array (List (ZMod p))) (k : Nat) : Array (DfRes p) :=
  (Array.range k).map fun j =>
    let col := survs.map (fun s => denseLookupIxV (zmodZeroP p) s (k - 1 - j))
    match dfUni col with
    | some c => .uni c false
    | none => .vec col none

def dfCollectCs (ctx : DfCtx p) (cs : Array (DenseExpr p)) (touched : Array Nat)
    (mask : Array Bool) (i : Nat) (acc : Array (Nat × DenseExpr p)) : Array (Nat × DenseExpr p) :=
  if h : i < touched.size then
    let q := touched[i]
    if mask.getD i false then dfCollectCs ctx cs touched mask (i + 1) acc
    else
      match dfRewrite ctx (cs.getD q (.const (zmodZeroP p))) with
      | some e => dfCollectCs ctx cs touched mask (i + 1) (acc.push (q, e))
      | none => dfCollectCs ctx cs touched mask (i + 1) acc
  else acc
termination_by touched.size - i
decreasing_by all_goals omega

def dfCollectBis (ctx : DfCtx p) (bis : Array (BusInteraction (DenseExpr p))) (touched : Array Nat)
    (i : Nat) (acc : Array (Nat × BusInteraction (DenseExpr p))) :
    Array (Nat × BusInteraction (DenseExpr p)) :=
  if h : i < touched.size then
    let q := touched[i]
    if hq : q < bis.size then
      match dfRewriteBi ctx bis[q] with
      | some bi => dfCollectBis ctx bis touched (i + 1) (acc.push (q, bi))
      | none => dfCollectBis ctx bis touched (i + 1) acc
    else dfCollectBis ctx bis touched (i + 1) acc
  else acc
termination_by touched.size - i
decreasing_by all_goals omega

/-- One target: domains, box gate, survivors, and the items it rewrites. Reads the system arrays
    only — the caller applies the changes, so a rejected target costs no copy. -/
def dfPlan (ix : DfIdx p) (keys : Array VarId) (cs : Array (DenseExpr p))
    (bis : Array (BusInteraction (DenseExpr p))) :
    Array (Nat × DenseExpr p) × Array (Nat × BusInteraction (DenseExpr p)) :=
  match dfKeyDoms ix.doms keys with
  | none => (#[], #[])
  | some doms =>
    if doms.foldl (fun n d => n * d.length) 1 > 256 then (#[], #[])
    else
      let touchedCs := dfTouched ix.csB keys
      match dfCovScan keys ix.src cs touchedCs 0 #[] #[] with
      | (mask, filters) =>
        let survs := dfEnumGo (zmodZeroP p) (dfLevels keys.size filters) doms keys.size 0 #[[]]
        if survs.isEmpty then (#[], #[])
        else
          let ctx : DfCtx p := ⟨keys, dfColRes survs keys.size⟩
          (dfCollectCs ctx cs touchedCs mask 0 #[],
           dfCollectBis ctx bis (dfTouched ix.bisB keys) 0 #[])

def dfApplyCs (cs : Array (DenseExpr p)) (ch : List (Nat × DenseExpr p)) : Array (DenseExpr p) :=
  match ch with
  | [] => cs
  | (q, e) :: rest => dfApplyCs (cs.setIfInBounds q e) rest

def dfApplyBis (bis : Array (BusInteraction (DenseExpr p)))
    (ch : List (Nat × BusInteraction (DenseExpr p))) : Array (BusInteraction (DenseExpr p)) :=
  match ch with
  | [] => bis
  | (q, bi) :: rest => dfApplyBis (bis.setIfInBounds q bi) rest

/-- Process the targets in order, applying each accepted fold in place. -/
def dfLoop (ix : DfIdx p) (targets : List (Array VarId)) (cs : Array (DenseExpr p))
    (bis : Array (BusInteraction (DenseExpr p))) (ch : Bool) :
    Array (DenseExpr p) × Array (BusInteraction (DenseExpr p)) × Bool :=
  match targets with
  | [] => (cs, bis, ch)
  | keys :: rest =>
    match dfPlan ix keys cs bis with
    | (chCs, chBis) =>
      if chCs.isEmpty && chBis.isEmpty then dfLoop ix rest cs bis ch
      else dfLoop ix rest (dfApplyCs cs chCs.toList) (dfApplyBis bis chBis.toList) true

/-- Domain-constant subexpression folding; see `denseDomainFoldFV` for what the pass does and
    `domainFoldRedesign.md` for the engine. -/
def dfRun (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    match dfScanGo d.algebraicConstraints 0 0 [] [] #[] with
    | (mx, svRev, candRev, dvs) =>
      let n := mx + 1
      let targets := dfDedupKeys (dfMarkVars (svRev.map Prod.snd) (Array.replicate n false))
        candRev (Array.replicate n []) []
      match targets with
      | [] => d
      | _ =>
        let isTgt := dfMarkKeys targets (Array.replicate n false)
        let cs := d.algebraicConstraints.toArray
        match dfDoms cs isTgt svRev.reverse (Array.replicate n none) (Array.replicate n 0) with
        | (doms, src) =>
          let ix : DfIdx p :=
            ⟨dfCsBuckets isTgt dvs 0 d.algebraicConstraints (Array.replicate n #[]),
             dfBisBuckets isTgt 0 d.busInteractions (Array.replicate n #[]), doms, src⟩
          match dfLoop ix targets cs d.busInteractions.toArray false with
          | (cs', bis', true) =>
              { algebraicConstraints := cs'.toList, busInteractions := bis'.toList }
          | (_, _, false) => d
  else d

/-- `denseDomainFoldFV` with the array-native loop on the indexed path. Proven equal and installed
    by `denseDomainFoldFV_eq_fast` (`Proofs/DomainFold.lean`). -/
@[implemented_by dfRun]
def denseDomainFoldFVFast (pw : PrimeWitness p) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if pw.isPrime = true then
    let targets := denseTargetsV d
    if domainFoldTargetIndexThreshold ≤ targets.length then
      let fidx := denseFoldLoopArrV targets (DenseFoldIdx.mk' d)
      { algebraicConstraints := fidx.arr.toList, busInteractions := fidx.arrBis.toList }
    else denseFoldLoopDirectV targets d
  else d

end ApcOptimizer.Dense
