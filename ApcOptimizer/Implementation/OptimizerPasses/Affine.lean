import ApcOptimizer.Implementation.OptimizerPasses.Subst
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Dense affine forms (Gauss foundation)

`DenseLinExpr`/`denseLinearize`, the linear-form layer the Gauss pass builds on. `denseLinearize`
never compares variables (it only appends/scales term lists); the solver layer below does. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A dense linear form: a constant plus `(VarId, coefficient)` terms. -/
structure DenseLinExpr (p : ℕ) where
  const : ZMod p
  terms : List (VarId × ZMod p)

/-- Evaluate a dense linear form under a dense environment. -/
def DenseLinExpr.eval (l : DenseLinExpr p) (denv : VarId → ZMod p) : ZMod p :=
  l.const + (l.terms.map (fun t => t.2 * denv t.1)).sum

def DenseLinExpr.add (a b : DenseLinExpr p) : DenseLinExpr p :=
  ⟨a.const + b.const, a.terms ++ b.terms⟩

def DenseLinExpr.scale (k : ZMod p) (a : DenseLinExpr p) : DenseLinExpr p :=
  ⟨k * a.const, a.terms.map (fun t => (t.1, k * t.2))⟩

/-! ## Boxed runtime twins

`p` is a runtime value, so every `ZMod p` operation Lean compiles inline re-derives the whole
`CommRing (ZMod p)` instance chain — `ZMod.commRing` alone allocates nine closures. A `…With ops`
twin takes a `DenseZModOps p` (`Encoding.lean`) instead, so a traversal costs one instance chain
rather than one per element. Same pattern as `denseCoeffIdxWith` in `Gauss.lean`.

A twin gets a `@[csimp]` only when it loops: building a `DenseZModOps p` costs about one instance
chain itself, so for a function performing a single operation (`add`) the twin stays a plain helper
for callers that already hold an `ops`. -/

def DenseLinExpr.addWith (ops : DenseZModOps p) (a b : DenseLinExpr p) : DenseLinExpr p :=
  ⟨ops.add a.const b.const, a.terms ++ b.terms⟩

theorem DenseLinExpr.addWith_eq (ops : DenseZModOps p) (a b : DenseLinExpr p) :
    a.addWith ops b = a.add b := by
  simp only [DenseLinExpr.addWith, DenseLinExpr.add, ops.add_eq]

def denseScaleTermsWith (ops : DenseZModOps p) (k : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => []
  | t :: ts => (t.1, ops.mul k t.2) :: denseScaleTermsWith ops k ts

theorem denseScaleTermsWith_eq (ops : DenseZModOps p) (k : ZMod p)
    (l : List (VarId × ZMod p)) : denseScaleTermsWith ops k l = l.map (fun t => (t.1, k * t.2)) := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp only [denseScaleTermsWith, List.map_cons, ops.mul_eq, ih]

def DenseLinExpr.scaleWith (ops : DenseZModOps p) (k : ZMod p) (a : DenseLinExpr p) :
    DenseLinExpr p :=
  ⟨ops.mul k a.const, denseScaleTermsWith ops k a.terms⟩

def DenseLinExpr.scaleFast (k : ZMod p) (a : DenseLinExpr p) : DenseLinExpr p :=
  DenseLinExpr.scaleWith denseZModOps k a

theorem DenseLinExpr.scaleWith_eq (ops : DenseZModOps p) (k : ZMod p) (a : DenseLinExpr p) :
    a.scaleWith ops k = a.scale k := by
  simp only [DenseLinExpr.scaleWith, DenseLinExpr.scale, ops.mul_eq, denseScaleTermsWith_eq]

@[csimp] theorem DenseLinExpr.scale_eq_fast : @DenseLinExpr.scale = @DenseLinExpr.scaleFast := by
  funext p k a
  exact (DenseLinExpr.scaleWith_eq denseZModOps k a).symm

/-- Try to view a dense expression as a linear form (`none` on a variable×variable product). -/
def denseLinearize : DenseExpr p → Option (DenseLinExpr p)
  | .const n => some ⟨n, []⟩
  | .var i => some ⟨0, [(i, 1)]⟩
  | .add a b =>
      match denseLinearize a, denseLinearize b with
      | some la, some lb => some (la.add lb)
      | _, _ => none
  | .mul a b =>
      match denseLinearize a, denseLinearize b with
      | some la, some lb =>
          if la.terms.isEmpty then some (lb.scale la.const)
          else if lb.terms.isEmpty then some (la.scale lb.const)
          else none
      | _, _ => none

/-! ## Accumulator twin of `denseLinearize` (runtime `@[csimp]`)

`DenseLinExpr.add` appends the left form's terms, so a left-associated affine chain recopies its
prefix at every node — `O(terms²)`. `denseLinearizeAcc` builds the same list onto a suffix
(right subtree first), which costs one cons per term. Only `add` needs the accumulator; a `mul`
that linearizes has a term-free side, so it scales rather than concatenates. -/

/-- `l.map (fun t => (t.1, k * t.2)) ++ acc` in one pass, so the scaling `mul` branch below does
    not build an intermediate list only to copy it onto the accumulator. -/
def denseScaleAppend (k : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p) → List (VarId × ZMod p)
  | [], acc => acc
  | t :: ts, acc => (t.1, k * t.2) :: denseScaleAppend k ts acc

theorem denseScaleAppend_eq (k : ZMod p) (l acc : List (VarId × ZMod p)) :
    denseScaleAppend k l acc = l.map (fun t => (t.1, k * t.2)) ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons t ts ih => simp [denseScaleAppend, ih]

def denseLinearizeAcc : DenseExpr p → List (VarId × ZMod p) →
    Option (ZMod p × List (VarId × ZMod p))
  | .const n, acc => some (n, acc)
  | .var i, acc => some (0, (i, 1) :: acc)
  | .add a b, acc =>
      match denseLinearizeAcc b acc with
      | none => none
      | some (cb, acc') =>
        match denseLinearizeAcc a acc' with
        | none => none
        | some (ca, acc'') => some (ca + cb, acc'')
  | .mul a b, acc =>
      match denseLinearizeAcc a [], denseLinearizeAcc b [] with
      | some (ca, ta), some (cb, tb) =>
          if ta.isEmpty then some (ca * cb, denseScaleAppend ca tb acc)
          else if tb.isEmpty then some (cb * ca, denseScaleAppend cb ta acc)
          else none
      | _, _ => none

theorem denseLinearizeAcc_eq (e : DenseExpr p) (acc : List (VarId × ZMod p)) :
    denseLinearizeAcc e acc = (denseLinearize e).map (fun l => (l.const, l.terms ++ acc)) := by
  induction e generalizing acc with
  | const n => simp [denseLinearizeAcc, denseLinearize]
  | var i => simp [denseLinearizeAcc, denseLinearize]
  | add a b iha ihb =>
      simp only [denseLinearizeAcc, ihb acc]
      cases hb : denseLinearize b with
      | none => simp [denseLinearize, hb]
      | some lb =>
        simp only [Option.map_some, iha (lb.terms ++ acc)]
        cases ha : denseLinearize a with
        | none => simp [denseLinearize, ha, hb]
        | some la => simp [denseLinearize, ha, hb, DenseLinExpr.add, List.append_assoc]
  | mul a b iha ihb =>
      simp only [denseLinearizeAcc, iha [], ihb []]
      cases ha : denseLinearize a with
      | none => simp [denseLinearize, ha]
      | some la =>
        cases hb : denseLinearize b with
        | none => simp [denseLinearize, ha, hb]
        | some lb =>
          simp only [Option.map_some, List.append_nil]
          by_cases h1 : la.terms.isEmpty
          · simp [denseLinearize, ha, hb, h1, DenseLinExpr.scale, denseScaleAppend_eq]
          · by_cases h2 : lb.terms.isEmpty
            · simp [denseLinearize, ha, hb, h1, h2, DenseLinExpr.scale, denseScaleAppend_eq]
            · simp [denseLinearize, ha, hb, h1, h2]

/-- Boxed twin of `denseScaleAppend`; see the `…With` note above. -/
def denseScaleAppendWith (ops : DenseZModOps p) (k : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p) → List (VarId × ZMod p)
  | [], acc => acc
  | t :: ts, acc => (t.1, ops.mul k t.2) :: denseScaleAppendWith ops k ts acc

theorem denseScaleAppendWith_eq (ops : DenseZModOps p) (k : ZMod p)
    (l acc : List (VarId × ZMod p)) :
    denseScaleAppendWith ops k l acc = denseScaleAppend k l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons t ts ih => simp only [denseScaleAppendWith, denseScaleAppend, ops.mul_eq, ih]

def denseScaleAppendFast (k : ZMod p) (l acc : List (VarId × ZMod p)) :
    List (VarId × ZMod p) :=
  denseScaleAppendWith denseZModOps k l acc

@[csimp] theorem denseScaleAppend_eq_fast : @denseScaleAppend = @denseScaleAppendFast := by
  funext p k l acc
  exact (denseScaleAppendWith_eq denseZModOps k l acc).symm

/-- Boxed twin of `denseLinearizeAcc`: the `var` leaf alone needs `0` and `1`, i.e. two instance
    chains per variable occurrence in every expression the optimizer linearizes. -/
def denseLinearizeAccWith (ops : DenseZModOps p) : DenseExpr p → List (VarId × ZMod p) →
    Option (ZMod p × List (VarId × ZMod p))
  | .const n, acc => some (n, acc)
  | .var i, acc => some (ops.zero, (i, ops.one) :: acc)
  | .add a b, acc =>
      match denseLinearizeAccWith ops b acc with
      | none => none
      | some (cb, acc') =>
        match denseLinearizeAccWith ops a acc' with
        | none => none
        | some (ca, acc'') => some (ops.add ca cb, acc'')
  | .mul a b, acc =>
      match denseLinearizeAccWith ops a [], denseLinearizeAccWith ops b [] with
      | some (ca, ta), some (cb, tb) =>
          if ta.isEmpty then some (ops.mul ca cb, denseScaleAppendWith ops ca tb acc)
          else if tb.isEmpty then some (ops.mul cb ca, denseScaleAppendWith ops cb ta acc)
          else none
      | _, _ => none

theorem denseLinearizeAccWith_eq (ops : DenseZModOps p) (e : DenseExpr p) :
    ∀ acc, denseLinearizeAccWith ops e acc = denseLinearizeAcc e acc := by
  induction e with
  | const n => intro acc; rfl
  | var i => intro acc; simp only [denseLinearizeAccWith, denseLinearizeAcc, ops.zero_eq, ops.one_eq]
  | add a b iha ihb =>
      intro acc
      simp only [denseLinearizeAccWith, denseLinearizeAcc, ihb acc]
      cases denseLinearizeAcc b acc with
      | none => rfl
      | some rb => simp only [iha rb.2]; cases denseLinearizeAcc a rb.2 <;> simp [ops.add_eq]
  | mul a b iha ihb =>
      intro acc
      simp only [denseLinearizeAccWith, denseLinearizeAcc, iha [], ihb []]
      cases denseLinearizeAcc a [] with
      | none => rfl
      | some ra =>
        cases denseLinearizeAcc b [] with
        | none => rfl
        | some rb =>
          simp only [ops.mul_eq, denseScaleAppendWith_eq]

def denseLinearizeAccFast (e : DenseExpr p) (acc : List (VarId × ZMod p)) :
    Option (ZMod p × List (VarId × ZMod p)) :=
  denseLinearizeAccWith denseZModOps e acc

@[csimp] theorem denseLinearizeAcc_eq_fast : @denseLinearizeAcc = @denseLinearizeAccFast := by
  funext p e acc
  exact (denseLinearizeAccWith_eq denseZModOps e acc).symm

def denseLinearizeFast (e : DenseExpr p) : Option (DenseLinExpr p) :=
  (denseLinearizeAcc e []).map (fun r => ⟨r.1, r.2⟩)

@[csimp] theorem denseLinearize_eq_fast : @denseLinearize = @denseLinearizeFast := by
  funext p e
  show denseLinearize e = _
  simp only [denseLinearizeFast, denseLinearizeAcc_eq, Option.map_map, List.append_nil]
  cases denseLinearize e <;> rfl

/-- Turn a dense linear form back into a dense expression. -/
def DenseLinExpr.toExpr (l : DenseLinExpr p) : DenseExpr p :=
  l.terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) (.const l.const)

/-! # Dense affine solver (Gauss foundation, part 2)

`coeff`/`others`, `trySolve`/`trySolveUnit`, and the pivot enumerators
`densePm1PivotsOf`/`denseUnitPivotsOf`, which compare variables (filter on `t.1 = x`) and are
consumed by the Gauss proof (`Proofs/Gauss.lean`). -/

/-! ## `denseLinearize` introduces no new variable

Proved locally here (Normalize.lean sits downstream); consumed by `Proofs/Gauss.lean`. -/

/-- Every term variable of `denseLinearize e` occurs in `e`. -/
theorem denseLinearize_mem_vars (e : DenseExpr p) (l : DenseLinExpr p)
    (h : denseLinearize e = some l) : ∀ i ∈ l.terms.map Prod.fst, i ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [denseLinearize, Option.some.injEq] at h; subst h; simp
  | var y =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      intro x hx; simpa [DenseExpr.vars] using hx
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro x hx
          simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hx
          simp only [DenseExpr.vars, List.mem_append]
          exact hx.imp (iha la hla x) (ihb lb hlb x)
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro x hx
            have hst : (lb.scale la.const).terms.map Prod.fst = lb.terms.map Prod.fst := by
              simp [DenseLinExpr.scale, List.map_map, Function.comp_def]
            rw [hst] at hx
            exact List.mem_append.2 (Or.inr (ihb lb hlb x hx))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro x hx
              have hst : (la.scale lb.const).terms.map Prod.fst = la.terms.map Prod.fst := by
                simp [DenseLinExpr.scale, List.map_map, Function.comp_def]
              rw [hst] at hx
              exact List.mem_append.2 (Or.inl (iha la hla x hx))
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-! ## Coefficient / remainder of a dense linear form -/

/-- Total coefficient of `x` in a dense linear form. -/
def DenseLinExpr.coeff (l : DenseLinExpr p) (x : VarId) : ZMod p :=
  ((l.terms.filter (fun t => t.1 = x)).map Prod.snd).sum

/-- Boxed twin of `coeff`: one pass, no `filter`/`map` intermediates, one instance chain per call
    instead of one per term (`List.sum` needs `+` and `0`). -/
def denseCoeffSumWith (ops : DenseZModOps p) (x : VarId) : List (VarId × ZMod p) → ZMod p
  | [] => ops.zero
  | t :: ts =>
      if t.1 = x then ops.add t.2 (denseCoeffSumWith ops x ts) else denseCoeffSumWith ops x ts

theorem denseCoeffSumWith_eq (ops : DenseZModOps p) (x : VarId) (ts : List (VarId × ZMod p)) :
    denseCoeffSumWith ops x ts = ((ts.filter (fun t => t.1 = x)).map Prod.snd).sum := by
  induction ts with
  | nil => simp [denseCoeffSumWith, ops.zero_eq]
  | cons t rest ih =>
      by_cases hx : t.1 = x
      · rw [List.filter_cons_of_pos (by simpa using hx)]
        simp only [denseCoeffSumWith, if_pos hx, ih, List.map_cons, List.sum_cons, ops.add_eq]
      · rw [List.filter_cons_of_neg (by simpa using hx)]
        simp only [denseCoeffSumWith, if_neg hx, ih]

def DenseLinExpr.coeffFast (l : DenseLinExpr p) (x : VarId) : ZMod p :=
  denseCoeffSumWith denseZModOps x l.terms

@[csimp] theorem DenseLinExpr.coeff_eq_fast : @DenseLinExpr.coeff = @DenseLinExpr.coeffFast := by
  funext p l x
  exact (denseCoeffSumWith_eq denseZModOps x l.terms).symm

/-- The dense linear form with all `x` terms removed. -/
def DenseLinExpr.others (l : DenseLinExpr p) (x : VarId) : DenseLinExpr p :=
  ⟨l.const, l.terms.filter (fun t => t.1 ≠ x)⟩

/-- Partition a dense term-list evaluation by whether the variable is `x`. -/
theorem denseEval_terms_split (x : VarId) (denv : VarId → ZMod p)
    (terms : List (VarId × ZMod p)) :
    (terms.map (fun t => t.2 * denv t.1)).sum
    = ((terms.filter (fun t => t.1 = x)).map Prod.snd).sum * denv x
      + ((terms.filter (fun t => t.1 ≠ x)).map (fun t => t.2 * denv t.1)).sum := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
      by_cases hx : t.1 = x
      · rw [List.filter_cons_of_pos (by simpa using hx),
            List.filter_cons_of_neg (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, hx]
        ring
      · rw [List.filter_cons_of_neg (by simpa using hx),
            List.filter_cons_of_pos (by simpa using hx),
            List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        ring

/-- Coefficient/remainder decomposition of a dense linear form's evaluation. -/
theorem DenseLinExpr.eval_split (l : DenseLinExpr p) (x : VarId) (denv : VarId → ZMod p) :
    l.eval denv = l.coeff x * denv x + (l.others x).eval denv := by
  simp only [DenseLinExpr.eval, DenseLinExpr.coeff, DenseLinExpr.others,
    denseEval_terms_split x denv l.terms]
  ring

/-! ## Solving for a unit-coefficient variable -/

/-- Try to solve the dense linear form `= 0` for `v` when `v` has coefficient `±1`. -/
def DenseLinExpr.trySolve (l : DenseLinExpr p) (v : VarId) : Option (VarId × DenseExpr p) :=
  if l.coeff v = 1 then some (v, ((l.others v).scale (-1)).toExpr)
  else if l.coeff v = -1 then some (v, (l.others v).toExpr)
  else none

/-- Try to solve the dense linear form `= 0` for `v` when `v`'s coefficient is a *unit*. -/
def DenseLinExpr.trySolveUnit (l : DenseLinExpr p) (v : VarId) : Option (VarId × DenseExpr p) :=
  if l.coeff v * (l.coeff v)⁻¹ = 1 then
    some (v, ((l.others v).scale (-(l.coeff v)⁻¹)).toExpr)
  else none

/-! ## Occurrence-aware pivot enumeration -/

/-- All `±1`-coefficient pivots of one dense constraint. -/
def densePm1PivotsOf (c : DenseExpr p) : List (VarId × DenseExpr p) :=
  match denseLinearize c with
  | none => []
  | some l => (l.terms.map Prod.fst).filterMap l.trySolve

/-- Unit-coefficient pivots of one dense constraint, for variables with no `±1` solution. -/
def denseUnitPivotsOf (c : DenseExpr p) : List (VarId × DenseExpr p) :=
  match denseLinearize c with
  | none => []
  | some l =>
    (l.terms.map Prod.fst).filterMap (fun v =>
      match l.trySolve v with
      | some _ => none
      | none => l.trySolveUnit v)

/-! ## Affine-form evaluation

Eval-preservation identities for the dense affine layer (`add`/`scale`/`linearize`/`toExpr`). -/

theorem DenseLinExpr.add_eval (a b : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.add b).eval denv = a.eval denv + b.eval denv := by
  simp only [DenseLinExpr.add, DenseLinExpr.eval, List.map_append, List.sum_append]
  ring

theorem DenseLinExpr.scale_eval (k : ZMod p) (a : DenseLinExpr p) (denv : VarId → ZMod p) :
    (a.scale k).eval denv = k * a.eval denv := by
  simp only [DenseLinExpr.scale, DenseLinExpr.eval, List.map_map, mul_add]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp_apply]; ring

theorem denseLinearize_eval (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l)
    (denv : VarId → ZMod p) : e.eval denv = l.eval denv := by
  induction e generalizing l with
  | const n =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | var i =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      simp [DenseLinExpr.eval, DenseExpr.eval]
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          rw [DenseExpr.eval, iha la hla, ihb lb hlb, DenseLinExpr.add_eval]
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la =>
        cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          have hae : a.eval denv = la.eval denv := iha la hla
          have hbe : b.eval denv = lb.eval denv := ihb lb hlb
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            have hc : la.eval denv = la.const := by
              simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h1, List.map_nil, List.sum_nil,
                add_zero]
            rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc]
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              have hc : lb.eval denv = lb.const := by
                simp only [DenseLinExpr.eval, List.isEmpty_iff.1 h2, List.map_nil, List.sum_nil,
                  add_zero]
              rw [DenseExpr.eval, hae, hbe, DenseLinExpr.scale_eval, hc, mul_comm]
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

/-- Evaluating the linear-form-rebuilt expression folds back to the affine sum. -/
theorem denseToExpr_foldl_eval (denv : VarId → ZMod p) (terms : List (VarId × ZMod p)) :
    ∀ init : DenseExpr p,
      (terms.foldl (fun acc t => .add acc (.mul (.const t.2) (.var t.1))) init).eval denv
      = init.eval denv + (terms.map (fun t => t.2 * denv t.1)).sum := by
  induction terms with
  | nil => intro init; simp
  | cons t rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      simp only [DenseExpr.eval]
      ring

theorem DenseLinExpr.toExpr_eval (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    l.toExpr.eval denv = l.eval denv := by
  simp only [DenseLinExpr.toExpr, DenseLinExpr.eval, denseToExpr_foldl_eval, DenseExpr.eval]

end ApcOptimizer.Dense
