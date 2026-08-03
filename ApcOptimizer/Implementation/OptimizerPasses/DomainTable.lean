import ApcOptimizer.Implementation.OptimizerPasses.EnumEngine
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

set_option autoImplicit false

/-! # Dense finite-domain infrastructure

Finite domains per `VarId`, derived from product-of-affine-factor constraints (`denseRootsIn`) and
fact-bounded bus payload slots (`denseInteractionDomainF`), plus the inverted index and the
point-evaluation helpers the domain passes share. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense `rootsIn` -/

/-- `a⁻¹`, skipping `ZMod.inv`'s extended gcd for the overwhelmingly common monic coefficient
    (`ZMod.inv_one`). -/
def zmodInvFast (a : ZMod p) : ZMod p := if zmodIsOne a then a else a⁻¹

/-- Dictionary-free twin of `denseRootsOfTerms`: the original mentions `⁻¹`, `*`, `+`, `-` and two
    `≠`, so Lean builds the whole `CommRing (ZMod p)` chain at the head of *every* call — before it
    even looks at the term list. -/
def denseRootsOfTermsFast (i : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → Option (List (ZMod p))
  | [] => if zmodIsZero c then none else some []
  | [(j, a)] =>
      let r := zmodNegP (zmodMulP (zmodInvFast a) c)
      if j == i && !zmodIsZero a && zmodIsZero (zmodAddP (zmodMulP a r) c) then some [r] else none
  | _ :: _ :: _ => none

/-- Find the affine root of `c * v + i` if `[(j, a)]` is a single term `j = i` with `a ≠ 0`. -/
def denseRootsOfTerms (i : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → Option (List (ZMod p))
  | [] => if c = 0 then none else some []
  | [(j, a)] =>
      let r := -(a⁻¹ * c)
      if j = i ∧ a ≠ 0 ∧ a * r + c = 0 then some [r] else none
  | _ :: _ :: _ => none

theorem zmodInvFast_eq (a : ZMod p) : zmodInvFast a = a⁻¹ := by
  unfold zmodInvFast
  by_cases h : zmodIsOne a = true
  · rw [if_pos h]
    have ha : a = 1 := by simpa [zmodIsOne_eq] using h
    rw [ha, ZMod.inv_one]
  · rw [if_neg h]

theorem denseRootsOfTermsFast_eq (i : VarId) (c : ZMod p) :
    ∀ l : List (VarId × ZMod p), denseRootsOfTermsFast i c l = denseRootsOfTerms i c l := by
  intro l
  match l with
  | [] => simp [denseRootsOfTermsFast, denseRootsOfTerms, zmodIsZero_eq]
  | [(j, a)] =>
      simp only [denseRootsOfTermsFast, denseRootsOfTerms, zmodIsZero_eq, zmodNegP_eq, zmodMulP_eq,
        zmodAddP_eq, zmodInvFast_eq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      by_cases hj : j = i
      · by_cases ha : a = 0
        · simp [hj, ha]
        · by_cases hr : a * -(a⁻¹ * c) + c = 0
          · simp [hj, ha]
          · simp [hj, ha]
      · simp [hj]
  | _ :: _ :: _ => rfl

@[csimp] theorem denseRootsOfTerms_eq_fast : @denseRootsOfTerms = @denseRootsOfTermsFast := by
  funext q i c l
  exact (denseRootsOfTermsFast_eq i c l).symm

/-- The affine root of `i` in `e`, through `denseLinearize` + `DenseLinExpr.norm`. -/
def denseAffineRootsIn (i : VarId) (e : DenseExpr p) : Option (List (ZMod p)) :=
  (denseLinearize e).bind (fun l => denseRootsOfTerms i l.norm.const l.norm.terms)

/-- The roots of `i` in `e`: affine roots, recursing into a product's factors. -/
def denseRootsIn (i : VarId) : DenseExpr p → Option (List (ZMod p))
  | .const n => denseAffineRootsIn i (.const n)
  | .var j => denseAffineRootsIn i (.var j)
  | .add a b => denseAffineRootsIn i (.add a b)
  | .mul a b =>
    match denseAffineRootsIn i (.mul a b) with
    | some r => some r
    | none =>
      match denseRootsIn i a, denseRootsIn i b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

/-! ## The dense domain table -/

/-- Finite domains for `VarId`s (runtime-only; no soundness field). -/
structure DenseDomainTable (p : ℕ) where
  map : Std.HashMap VarId (FiniteDomain p)

def DenseDomainTable.empty : DenseDomainTable p := ⟨∅⟩

/-- Insert an entailed domain, keeping the smaller of two candidate domains. -/
def DenseDomainTable.insertEntry (T : DenseDomainTable p) (i : VarId) (d : FiniteDomain p) :
    DenseDomainTable p :=
  let keep : Bool := match T.map[i]? with
    | some d0 => decide (d.size < d0.size)
    | none => true
  if keep then ⟨T.map.insert i d⟩ else T

/-- The table's domains for a `VarId` list, all-or-nothing. -/
def DenseDomainTable.doms (T : DenseDomainTable p) :
    List VarId → Option (List (VarId × FiniteDomain p))
  | [] => some []
  | i :: is =>
    match T.map[i]?, T.doms is with
    | some d, some rest => some ((i, d) :: rest)
    | _, _ => none

/-! ## Constraint-sourced domains -/

/-- Insert `c`'s entailed domain for each variable in a given list. -/
def denseAddConstraintVars (c : DenseExpr p) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseRootsIn i c with
    | some d => denseAddConstraintVars c is (T.insertEntry i (.explicit d))
    | none => denseAddConstraintVars c is T

/-- Constraint-sourced domains: for each constraint with at most 3 distinct variables, insert the
    entailed domain of each. -/
def denseAddConstraintDoms : List (DenseExpr p) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | c :: rest, T =>
    let vs := c.vars.dedup
    denseAddConstraintDoms rest (if vs.length ≤ 3 then denseAddConstraintVars c vs T else T)

/-! ## Bus-sourced range domains -/

/-- The raw-variable payload entries of a dense interaction. -/
def densePayloadRawVars (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

/-- A bus obligation's range domain for `i`, via `denseInteractionBound`. -/
def denseInteractionDomainF (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option (FiniteDomain p) :=
  match denseInteractionBound bs facts bi i with
  | none => none
  | some bound => if bound ≤ maxDomainBound then some (.range bound) else none

/-- Insert `bi`'s entailed domain for each variable in a given list. -/
def denseAddBusVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    List VarId → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | i :: is, T =>
    match denseInteractionDomainF bs facts bi i with
    | some d => denseAddBusVars bs facts bi is (T.insertEntry i d)
    | none => denseAddBusVars bs facts bi is T

/-- Bus-sourced domains: for each interaction, insert the entailed domain of each raw-variable
    payload entry. -/
def denseAddBusDoms (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | bi :: rest, T =>
    denseAddBusDoms bs facts rest (denseAddBusVars bs facts bi (densePayloadRawVars bi).dedup T)

/-! ## Dense enumeration engine -/

def denseEnvOfFast : List (VarId × ZMod p) → VarId → ZMod p
  | [], _ => 0
  | (x, v) :: rest, y => if (y == x) = true then v else denseEnvOfFast rest y

/-! ### Boxed runtime twins of the point lookups

`p` is a runtime value, so the `0` in the miss case is a full `CommRing (ZMod p)` instance chain,
and Lean builds it at the head of each recursive step — once per list cell walked, not once per
lookup. Taking the zero as a parameter hoists it out of the walk. -/

def denseEnvOfW (zero : ZMod p) : List (VarId × ZMod p) → VarId → ZMod p
  | [], _ => zero
  | (x, v) :: rest, y => if (y == x) = true then v else denseEnvOfW zero rest y

theorem denseEnvOfW_eq (pt : List (VarId × ZMod p)) (y : VarId) :
    denseEnvOfW 0 pt y = denseEnvOfFast pt y := by
  induction pt with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨x, v⟩ := t
      simp only [denseEnvOfW, denseEnvOfFast, ih]

def denseEnvOfFastFast (pt : List (VarId × ZMod p)) (y : VarId) : ZMod p :=
  denseEnvOfW (zmodZeroP p) pt y

@[csimp] theorem denseEnvOfFast_eq_fast : @denseEnvOfFast = @denseEnvOfFastFast := by
  funext p pt y
  rw [denseEnvOfFastFast, zmodZeroP_eq]
  exact (denseEnvOfW_eq pt y).symm

def denseContainsFast (xs : List VarId) (y : VarId) : Bool :=
  match xs with
  | [] => false
  | x :: rest => (y == x) || denseContainsFast rest y

/-! ### Index-compiled evaluation over dense points -/

/-- Positional lookup in a dense assignment; ignores keys. -/
def denseLookupIx : List (VarId × ZMod p) → Nat → ZMod p
  | [], _ => 0
  | (_, v) :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIx rest i

/-- Boxed twin of `denseLookupIx`; see the note on `denseEnvOfW` above. -/
def denseLookupIxW (zero : ZMod p) : List (VarId × ZMod p) → Nat → ZMod p
  | [], _ => zero
  | (_, v) :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIxW zero rest i

theorem denseLookupIxW_eq (pt : List (VarId × ZMod p)) (i : Nat) :
    denseLookupIxW 0 pt i = denseLookupIx pt i := by
  induction pt generalizing i with
  | nil => rfl
  | cons t rest ih => cases i <;> simp only [denseLookupIxW, denseLookupIx, ih]

def denseLookupIxFast (pt : List (VarId × ZMod p)) (i : Nat) : ZMod p :=
  denseLookupIxW 0 pt i

@[csimp] theorem denseLookupIx_eq_fast : @denseLookupIx = @denseLookupIxFast := by
  funext p pt i
  exact (denseLookupIxW_eq pt i).symm

/-- Evaluate a compiled `IExpr` over a dense point; positional. -/
def denseIExprEvalWith (add mul : ZMod p → ZMod p → ZMod p) (pt : List (VarId × ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIx pt i
  | .add a b => add (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)
  | .mul a b => mul (denseIExprEvalWith add mul pt a) (denseIExprEvalWith add mul pt b)

/-- Boxed twin: takes the lookup zero too, so an evaluation costs one instance chain rather than
    one per `.ix` node. -/
def denseIExprEvalWithZ (add mul : ZMod p → ZMod p → ZMod p) (zero : ZMod p)
    (pt : List (VarId × ZMod p)) : IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIxW zero pt i
  | .add a b =>
      add (denseIExprEvalWithZ add mul zero pt a) (denseIExprEvalWithZ add mul zero pt b)
  | .mul a b =>
      mul (denseIExprEvalWithZ add mul zero pt a) (denseIExprEvalWithZ add mul zero pt b)

theorem denseIExprEvalWithZ_eq (add mul : ZMod p → ZMod p → ZMod p)
    (pt : List (VarId × ZMod p)) (ie : IExpr p) :
    denseIExprEvalWithZ add mul 0 pt ie = denseIExprEvalWith add mul pt ie := by
  induction ie with
  | const n => rfl
  | ix i => exact denseLookupIxW_eq pt i
  | add a b iha ihb => simp only [denseIExprEvalWithZ, denseIExprEvalWith, iha, ihb]
  | mul a b iha ihb => simp only [denseIExprEvalWithZ, denseIExprEvalWith, iha, ihb]

def denseIExprEvalWithFast (add mul : ZMod p → ZMod p → ZMod p) (pt : List (VarId × ZMod p))
    (ie : IExpr p) : ZMod p :=
  denseIExprEvalWithZ add mul 0 pt ie

@[csimp] theorem denseIExprEvalWith_eq_fast :
    @denseIExprEvalWith = @denseIExprEvalWithFast := by
  funext p add mul pt ie
  exact (denseIExprEvalWithZ_eq add mul pt ie).symm

/-! ### Compiling dense items to `IExpr`/`CBi` -/

/-- First position of `y` in dense `keys`. -/
def denseVarIx (keys : List VarId) (y : VarId) : Option Nat :=
  match keys with
  | [] => none
  | x :: rest => if (y == x) = true then some 0 else (denseVarIx rest y).map (· + 1)

/-- Compile a dense expression against dense `keys`. -/
def denseCompileE (keys : List VarId) : DenseExpr p → Option (IExpr p)
  | .const n => some (.const n)
  | .var y => (denseVarIx keys y).map .ix
  | .add a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.add ia ib)
    | _, _ => none
  | .mul a b =>
    match denseCompileE keys a, denseCompileE keys b with
    | some ia, some ib => some (.mul ia ib)
    | _, _ => none

/-- Compile a list of dense expressions, all-or-nothing. -/
def denseCompileEs (keys : List VarId) : List (DenseExpr p) → Option (List (IExpr p))
  | [] => some []
  | e :: rest =>
    match denseCompileE keys e, denseCompileEs keys rest with
    | some ie, some irest => some (ie :: irest)
    | _, _ => none

def denseCompileBi (keys : List VarId) (bi : BusInteraction (DenseExpr p)) : Option (CBi p) :=
  match denseCompileE keys bi.multiplicity, denseCompileEs keys bi.payload with
  | some m, some pl => some ⟨bi.busId, m, pl⟩
  | _, _ => none

/-- Compile a list of dense interactions, all-or-nothing. -/
def denseCompileBis (keys : List VarId) : List (BusInteraction (DenseExpr p)) →
    Option (List (CBi p))
  | [] => some []
  | bi :: rest =>
    match denseCompileBi keys bi, denseCompileBis keys rest with
    | some cbi, some crest => some (cbi :: crest)
    | _, _ => none

/-! ### `DenseExpr.eval` congruence -/

/-- `DenseExpr.eval` depends only on the values of the variables that occur. -/
theorem DenseExpr.eval_congr (e : DenseExpr p) (f g : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, f i = g i) : e.eval f = e.eval g := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]
  | mul a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at h
      simp only [DenseExpr.eval, iha (fun i hi => h i (Or.inl hi)), ihb (fun i hi => h i (Or.inr hi))]

/-! ## Dense `varsInF` -/

/-- Whether every variable of the expression lies in `xs`. -/
def DenseExpr.varsInF (xs : List VarId) : DenseExpr p → Bool
  | .const _ => true
  | .var y => denseContainsFast xs y
  | .add a b => a.varsInF xs && b.varsInF xs
  | .mul a b => a.varsInF xs && b.varsInF xs

def denseVarsInListF (xs : List VarId) : List VarId → Bool
  | [] => true
  | v :: vs => denseContainsFast xs v && denseVarsInListF xs vs

/-! ## Dense `biInformative` -/

/-- Whether a bus interaction is informative: some payload entry is neither a variable nor a known
    constant, or is a variable whose interaction bound is unknown. -/
def denseBiInformative (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.payload.any (fun e => !(e.isVar || e.constValue?.isSome)) ||
  bi.payload.any (fun e => match e with
    | .var i => (denseInteractionBound bs facts bi i).isNone
    | _ => false)

/-! ## Dense inverted index

The candidate list for a target is the union of the buckets under its variables plus the
variable-less positions. -/

structure DenseCovIndex where
  buckets : Std.HashMap VarId (List Nat)
  varless : List Nat

def denseBuildStep {α : Type} (varsOf : α → List VarId) (ai : α × Nat) (idx : DenseCovIndex) :
    DenseCovIndex :=
  match varsOf ai.1 with
  | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
  | vs => ⟨vs.foldl (fun m v => m.insert v (ai.2 :: m.getD v [])) idx.buckets, idx.varless⟩

def denseCovBuild {α : Type} (varsOf : α → List VarId) (items : List α) : DenseCovIndex :=
  items.zipIdx.foldr (denseBuildStep varsOf) ⟨∅, []⟩

/-- Build an index with each non-variable-less item stored under one anchor variable. -/
def denseAnchorBuildStep {α : Type} (varsOf : α → List VarId) (ai : α × Nat)
    (idx : DenseCovIndex) : DenseCovIndex :=
  match varsOf ai.1 with
  | [] => ⟨idx.buckets, ai.2 :: idx.varless⟩
  | v :: _ => ⟨idx.buckets.insert v (ai.2 :: idx.buckets.getD v []), idx.varless⟩

def denseAnchorCovBuild {α : Type} (varsOf : α → List VarId) (items : List α) : DenseCovIndex :=
  items.zipIdx.foldr (denseAnchorBuildStep varsOf) ⟨∅, []⟩

/-- The dense candidate positions for target `xs`. -/
def denseCandidates (idx : DenseCovIndex) (xs : List VarId) : List Nat :=
  (xs.flatMap (fun v => idx.buckets.getD v [])) ++ idx.varless

/-! ### `buildStep` bucket projection helpers -/

/-! ### Dense `ForcedIdx` and its correspondence -/

/-- A constraint and the target-planning data reused by every enumeration. -/
structure DenseConstraintPlan (p : ℕ) where
  expr : DenseExpr p
  vars : List VarId
  active : Bool

/-- A bus interaction and the target-planning data reused by every enumeration. -/
structure DenseBusPlan (p : ℕ) where
  interaction : BusInteraction (DenseExpr p)
  vars : List VarId
  usable : Bool
  informative : Bool
  domainRedundant : Bool

/-- Compact anchor buckets used by the read-only per-target gathers. -/
structure DenseArrayCovIndex where
  buckets : Std.HashMap VarId (Array Nat)
  varless : Array Nat

/-- Constraint anchors with inactive variable-free plans summarized once. -/
structure DenseConstraintCovIndex where
  buckets : Std.HashMap VarId (Array Nat)
  inactiveVarlessCount : Nat
  activeVarless : Array Nat

/-- The variable-free usable interactions' contribution to a gather, which is the same for every
    target: their count, their `informative`/`domainRedundant` folds, and the constant value of
    their obligations (`constOk`, false as soon as one of them is violated). -/
structure DenseBusVarlessSummary (p : ℕ) where
  count : Nat
  informative : Bool
  allDomainRedundant : Bool
  constOk : Bool

/-- The per-target index bundle (plain data; correctness via correspondence). -/
structure DenseForcedIdx (p : ℕ) where
  csIdx : DenseConstraintCovIndex
  arrCs : Array (DenseConstraintPlan p)
  bisIdx : DenseArrayCovIndex
  arrBis : Array (DenseBusPlan p)
  busVarless : DenseBusVarlessSummary p

/-- Canonical dedup key of a variable set: the sorted, duplicate-free `List VarId`, so the key is
    invariant under the order and multiplicity of `xs` and distinct variables never collide. -/
def denseVarSetKey (xs : List VarId) : List VarId :=
  xs.dedup.mergeSort (fun a b => compare a.index b.index != .gt)

/-! ### Regression guards: the key is an exact `VarId` set -/

private def egRegA : VarRegistry × VarId :=
  VarRegistry.empty.register { name := "x", powdrId? := some 1 }
private def egRegB : VarRegistry × VarId :=
  egRegA.1.register { name := "x", powdrId? := some 2 }
private def egA : VarId := egRegA.2
private def egB : VarId := egRegB.2

-- distinct equal-name variables get distinct singleton keys
#guard denseVarSetKey [egA] != denseVarSetKey [egB]
-- order-independence
#guard denseVarSetKey [egA, egB] == denseVarSetKey [egB, egA]
-- set semantics: duplicate ids collapse
#guard denseVarSetKey [egA, egA, egB] == denseVarSetKey [egA, egB]

/-- Apply a dense solution map to a system, unless it is empty. Kept as a standalone function so
    the solution map is computed exactly once (as the argument). -/
def applyσ (dσ : DenseSolved p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if dσ.map.isEmpty then d else d.substF dσ.fn

/-! ## Value-only positional lookup and compiled evaluation -/

/-- Positional lookup in a value-only point (position alone determines the value). -/
def denseLookupIxV (zero : ZMod p) : List (ZMod p) → Nat → ZMod p
  | [], _ => zero
  | v :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIxV zero rest i

/-- `IExpr.evalWith`, over a value-only point (hoisted `add`/`mul`). -/
def denseIExprEvalWithV (ops : DenseZModOps p) (pt : List (ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIxV ops.zero pt i
  | .add a b => ops.add (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)
  | .mul a b => ops.mul (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)

/-- Direct relation implemented by a compiled byte-bus predicate. -/
inductive DenseBytePredKind where
  | xor
  | pair
  | or
  | and

/-- An interaction whose obligation is discharged for every point: a bus that never violates, or one
    checked for arity only (the VMs' instruction-table lookups) at its declared arity. Compiling
    these to `.always` keeps the opaque `bs.violatesConstraint` — a payload list and a message record
    per enumerated point — out of the scan. -/
def denseBiAlwaysOk {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  facts.neverViolates bi.busId || facts.neverViolatesArity bi.busId bi.payload.length

/-- Value-only environment lookup against an explicit key list (fallback only; see above). -/
def denseEnvOfKeysV (keys : List VarId) (pt : List (ZMod p)) (y : VarId) : ZMod p :=
  match keys, pt with
  | [], _ => 0
  | _, [] => 0
  | x :: ks, v :: vs => if y == x then v else denseEnvOfKeysV ks vs y

/-- A per-target survivor predicate, boxed in a one-field structure so its setup (ring instances,
    compilation, `isZero` closure) runs once per target rather than being eta-expanded into the
    per-point call path. -/
structure DenseSurvV (p : ℕ) where
  /-- The per-point survivor test (see `DenseSurvV`). -/
  run : List (ZMod p) → Bool

/-- Is `op` a recognized byte-relation selector for `spec`? Every such op guarantees both operands
    are below `spec.bound` (`BusFacts.byteXorSpec_sound` / `byteBoolSound`). -/
def denseByteOpBounds (spec : ByteXorSpec p) (op : ZMod p) : Bool :=
  decide (op = spec.xorOp) || decide (op = spec.pairOp) ||
    spec.orOp.any (fun o => decide (op = o)) || spec.andOp.any (fun a => decide (op = a))

/-- The single-variable affine form `(x, a, b)` with `e = a·x + b` and `a ≠ 0`, or `none`. -/
def denseAffineOfExpr (e : DenseExpr p) : Option (VarId × ZMod p × ZMod p) :=
  (denseLinearize e).bind (fun l =>
    match l.norm.terms with
    | [(x, a)] => if a = 0 then none else some (x, a, l.norm.const)
    | _ => none)
