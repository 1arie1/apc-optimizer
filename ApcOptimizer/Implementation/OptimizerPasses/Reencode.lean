import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq

set_option autoImplicit false

/-! # Witness re-encoding — dense expression ops and the build/step/loop/pass layer.

Impl-only: no theorem is stated here. Correctness and the `ofExtending` wiring live in
`Proofs/Reencode.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Override `denv` on the keys of `pairs` (first match wins). -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

/-- `DenseExpr.eval` with the ring operations passed in. -/
def DenseExpr.evalWith (add mul : ZMod p → ZMod p → ZMod p) (denv : VarId → ZMod p) :
    DenseExpr p → ZMod p
  | .const n => n
  | .var i => denv i
  | .add a b => add (a.evalWith add mul denv) (b.evalWith add mul denv)
  | .mul a b => mul (a.evalWith add mul denv) (b.evalWith add mul denv)

/-- `DenseExpr.eval`, deriving the field operations once per call instead of per node. -/
def DenseExpr.evalFast (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  let addI : Add (ZMod p) := inferInstance
  let mulI : Mul (ZMod p) := inferInstance
  e.evalWith addI.add mulI.mul denv

/-- `b · (b − 1)`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-- Substitution defined only on the group `xs`, backed by `hm`. -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ### Boxed runtime twins

Each `ZMod p` literal Lean compiles inline rebuilds the whole `CommRing (ZMod p)` chain, and here
the literals sit inside `map`/`foldl`/`all` bodies, so they are rebuilt per element. A `let` does
not help — it is zeta-expanded back into the loop body — so the literal has to become a *parameter*
of the traversal, which is what the `…W` twins below do. -/

def denseBitBoxW (box : List (ZMod p)) (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, box))

def denseBitBoxFast (bits : List VarId) : List (VarId × List (ZMod p)) :=
  denseBitBoxW [0, 1] bits

@[csimp] theorem denseBitBox_eq_fast : @denseBitBox = @denseBitBoxFast := by
  funext p bits; rfl

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

def denseIndicatorExprW (one negOne : ZMod p) (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = one then .var bv.1
              else .add (.const one) (.mul (.const negOne) (.var bv.1)))) (.const one)

def denseIndicatorExprFast (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  denseIndicatorExprW 1 (-1) aβ

@[csimp] theorem denseIndicatorExpr_eq_fast :
    @denseIndicatorExpr = @denseIndicatorExprFast := by
  funext p aβ; rfl

/-- Interpolate a subexpression over the bit patterns from its precomputed per-pattern values. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- Take `cand` if its variables lie in the bits and it agrees with the substitution values on
    every pattern; otherwise fall back to the plain substitution `sub`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. -/
def denseGroupRewrite (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var y =>
      if denseContainsFast xs y then denseGroupRewriteCand bits σfn patts (.var y) else .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.add a b)
      else .add (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.mul a b)
      else .mul (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)

/-! ## The re-encoded system -/

/-- The re-encoded system: substitute the group everywhere, drop the now-covered constraints, and
    add booleanity constraints for the bits. -/
def denseReencodeOut (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))))
        ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity :=
        denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))
          bi.multiplicity,
      payload := bi.payload.map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))) }) }

/-! ## The group's surviving values -/

/-- All covered constraints zero at a point (ring ops hoisted out of the per-point eval). -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- Boxed twin of `denseSurvZeroCW`: this runs once per enumerated assignment, so the `0` would
    otherwise be rebuilt per constraint per point of the group's domain box. -/
def denseSurvZeroCWZ (add mul : ZMod p → ZMod p → ZMod p) (zero : ZMod p)
    (ces : List (IExpr p)) (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWithZ add mul zero a ie = zero))

theorem denseSurvZeroCWZ_eq (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p)) :
    denseSurvZeroCWZ add mul 0 ces = denseSurvZeroCW add mul ces := by
  funext a
  simp only [denseSurvZeroCWZ, denseSurvZeroCW, denseIExprEvalWithZ_eq]

def denseSurvZeroCWFast (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  denseSurvZeroCWZ add mul 0 ces a

@[csimp] theorem denseSurvZeroCW_eq_fast : @denseSurvZeroCW = @denseSurvZeroCWFast := by
  funext p add mul ces a
  exact (congrFun (denseSurvZeroCWZ_eq add mul ces) a).symm

/-- The surviving group values: enumerate the group's domains, keep those satisfying the covered
    constraints. -/
def denseGroupSurvivorsE (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    (denseAssignments doms).filter
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
  | none =>
    (denseAssignments doms).filter
      (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))

/-- Boxed twin. The `add`/`mul`/`zero` must be parameters of the function that *contains* the
    enumeration loop: the specializer inlines the predicate into the `filter`, and anything derived
    inside this function is then floated back into the loop body. -/
def denseGroupSurvivorsEW (add mul : ZMod p → ZMod p → ZMod p) (zero : ZMod p)
    (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces => (denseAssignments doms).filter (denseSurvZeroCWZ add mul zero ces)
  | none =>
    (denseAssignments doms).filter
      (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = zero)))

def denseGroupSurvivorsEFast (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  denseGroupSurvivorsEW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul 0
    es doms

@[csimp] theorem denseGroupSurvivorsE_eq_fast :
    @denseGroupSurvivorsE = @denseGroupSurvivorsEFast := by
  funext p es doms
  show denseGroupSurvivorsE es doms = denseGroupSurvivorsEW _ _ 0 es doms
  unfold denseGroupSurvivorsE denseGroupSurvivorsEW
  split
  · rw [denseSurvZeroCWZ_eq]
  · rfl

/-- `filter P l` if it keeps at most `cap` elements, `none` as soon as a `cap + 1`-st hit shows
    up — the tail is not scanned. -/
def denseFilterCap {α : Type} (P : α → Bool) : Nat → List α → Option (List α)
  | _, [] => some []
  | cap, x :: rest =>
    if P x then
      match cap with
      | 0 => none
      | cap + 1 =>
        match denseFilterCap P cap rest with
        | some l => some (x :: l)
        | none => none
    else denseFilterCap P cap rest

/-- `denseGroupSurvivorsE`, stopping as soon as more than `cap` survivors exist. The build uses
    `cap = 2 ^ (xs.length − 1)`: any larger survivor count makes `Nat.clog 2` reach the group
    size and the `k < xs.length` gate reject, so the outcome is the full enumeration's. -/
def denseGroupSurvivorsECap (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p)))
    (cap : Nat) : Option (List (List (VarId × ZMod p))) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    denseFilterCap
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
      cap (denseAssignments doms)
  | none =>
    denseFilterCap (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))
      cap (denseAssignments doms)

/-- Boxed twin of `denseGroupSurvivorsECap`; see `denseGroupSurvivorsEW`. -/
def denseGroupSurvivorsECapW (add mul : ZMod p → ZMod p → ZMod p) (zero : ZMod p)
    (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) (cap : Nat) :
    Option (List (List (VarId × ZMod p))) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    denseFilterCap (denseSurvZeroCWZ add mul zero ces) cap (denseAssignments doms)
  | none =>
    denseFilterCap (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = zero)))
      cap (denseAssignments doms)

def denseGroupSurvivorsECapFast (es : List (DenseExpr p))
    (doms : List (VarId × List (ZMod p))) (cap : Nat) :
    Option (List (List (VarId × ZMod p))) :=
  denseGroupSurvivorsECapW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul 0
    es doms cap

@[csimp] theorem denseGroupSurvivorsECap_eq_fast :
    @denseGroupSurvivorsECap = @denseGroupSurvivorsECapFast := by
  funext p es doms cap
  show denseGroupSurvivorsECap es doms cap = denseGroupSurvivorsECapW _ _ 0 es doms cap
  unfold denseGroupSurvivorsECap denseGroupSurvivorsECapW
  split
  · rw [denseSurvZeroCWZ_eq]
  · rfl

/-! ## The checked re-encoding certificate -/

/-- All checked side conditions for one re-encoding step. The freshness conjunct is deliberately
    last: it is the only `O(bits × system)` one, so short-circuiting runs it only for groups that
    already passed the cheap checks. -/
def denseCheckReencode (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  match denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => false
  | some doms =>
    let es := denseCoveredCsOf d xs
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    -- the substituted group variables only mention bits
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    -- completeness: every surviving group value is hit by some bit pattern
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    -- freshness: no bit occurs anywhere in the system
    bits.all (fun b =>
      d.algebraicConstraints.all (fun c => !c.mentions b) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b)))

/-! ### Compiled twin of the certificate

`denseCheckReencode` walks the whole system once per bit for the freshness conjunct and scans the
covered set twice; the twin computes the covered set once and decides freshness in a single walk
against the bit set. -/

theorem DenseExpr.mentionsAny_ofList_false_iff (bits : List VarId) (e : DenseExpr p) :
    e.mentionsAny (Std.HashSet.ofList bits) = false ↔ ∀ b ∈ bits, e.mentions b = false := by
  induction e with
  | const c => simp [DenseExpr.mentionsAny, DenseExpr.mentions]
  | var y =>
      simp only [DenseExpr.mentionsAny, DenseExpr.mentions, Std.HashSet.contains_ofList]
      constructor
      · intro h b hb
        cases hyb : y == b with
        | false => rfl
        | true =>
            rw [show y = b from eq_of_beq hyb] at h
            rw [List.contains_eq_mem, decide_eq_false_iff_not] at h
            exact absurd hb h
      · intro h
        rw [List.contains_eq_mem, decide_eq_false_iff_not]
        intro hy
        exact absurd (h y hy) (by simp)
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.mentionsAny, DenseExpr.mentions, Bool.or_eq_false_iff, iha, ihb]
      exact ⟨fun ⟨ha, hb⟩ x hx => ⟨ha x hx, hb x hx⟩,
        fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩⟩

theorem denseFreshFused_eq (d : DenseConstraintSystem p) (bits : List VarId) :
    (d.algebraicConstraints.all (fun c => !c.mentionsAny (Std.HashSet.ofList bits)) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentionsAny (Std.HashSet.ofList bits) &&
        bi.payload.all (fun e => !e.mentionsAny (Std.HashSet.ofList bits))))
      = bits.all (fun b =>
          d.algebraicConstraints.all (fun c => !c.mentions b) &&
          d.busInteractions.all (fun bi =>
            !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b))) := by
  have hiff : ∀ {a b : Bool}, ((a = true) ↔ (b = true)) → a = b := by
    intro a b h; cases a <;> cases b <;> simp_all
  apply hiff
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    DenseExpr.mentionsAny_ofList_false_iff]
  constructor
  · rintro ⟨hcs, hbis⟩ b hb
    exact ⟨fun c hc => hcs c hc b hb, fun bi hbi =>
      ⟨(hbis bi hbi).1 b hb, fun e he => (hbis bi hbi).2 e he b hb⟩⟩
  · intro h
    exact ⟨fun c hc b hb => (h b hb).1 c hc, fun bi hbi =>
      ⟨fun b hb => ((h b hb).2 bi hbi).1, fun e he b hb => ((h b hb).2 bi hbi).2 e he⟩⟩

/-- `denseCheckReencode` with the covered set shared between the domain and soundness conjuncts
    and the freshness conjunct decided in one system walk. -/
def denseCheckReencodeFast (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let es := denseCoveredCsOf d xs
  match denseGroupDoms es xs with
  | none => false
  | some doms =>
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    (d.algebraicConstraints.all (fun c => !c.mentionsAny (Std.HashSet.ofList bits)) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentionsAny (Std.HashSet.ofList bits) &&
        bi.payload.all (fun e => !e.mentionsAny (Std.HashSet.ofList bits))))

@[csimp] theorem denseCheckReencode_eq_fast : @denseCheckReencode = @denseCheckReencodeFast := by
  funext q d xs bits hm
  unfold denseCheckReencode denseCheckReencodeFast
  simp only [denseFreshFused_eq]

/-! ## Derived-variable methods for the fresh bits

Each bit is recovered from the group by a decision tree over the bit patterns: at the first
pattern whose interpolation image equals the group's values, output that pattern's bit. -/

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). -/
def denseImgVal (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (aβ : List (VarId × ZMod p)) (x : VarId) : ZMod p :=
  ((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. -/
def denseMatchCM (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) : DenseComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (denseMatchCM rest imgFn thenM elseM) elseM

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
def denseBitCM (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) : DenseComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest =>
      denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b)) (denseBitCM rest xs hm b)

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-- Does the expression share a variable with `xs`? -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ### Compiled twin of the system rewrite

`denseGroupRewrite` is the identity on an item that shares no variable with the group and has no
variable-free composite node (`denseGroupRewrite_eq_self`), so the compiled `denseReencodeOut`
guards every item with a read-only gate and rebuilds only the few that can change — the plain
definition rebuilds every expression of the system per accepted group. Installed with `@[csimp]`
below, so callers compile to the gated form while the proofs keep the plain `denseReencodeOut`. -/

theorem DenseExpr.varsInF_eq_false {xs : List VarId} {e : DenseExpr p}
    (hv : e.hasVar = true) (hs : e.sharesVarIn xs = false) : e.varsInF xs = false := by
  induction e with
  | const n => simp [DenseExpr.hasVar] at hv
  | var y =>
      simp only [DenseExpr.sharesVarIn] at hs
      simp [DenseExpr.varsInF, hs]
  | add a b iha ihb =>
      simp only [DenseExpr.hasVar, Bool.or_eq_true] at hv
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rcases hv with hv | hv
      · simp [DenseExpr.varsInF, iha hv hs.1]
      · simp [DenseExpr.varsInF, ihb hv hs.2]
  | mul a b iha ihb =>
      simp only [DenseExpr.hasVar, Bool.or_eq_true] at hv
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rcases hv with hv | hv
      · simp [DenseExpr.varsInF, iha hv hs.1]
      · simp [DenseExpr.varsInF, ihb hv hs.2]

theorem denseGroupRewrite_eq_self {xs bits : List VarId} {σfn : VarId → Option (DenseExpr p)}
    {patts : List (List (VarId × ZMod p))} {e : DenseExpr p}
    (hs : e.sharesVarIn xs = false) (hf : e.hasConstFoldableNode = false) :
    denseGroupRewrite xs bits σfn patts e = e := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [DenseExpr.sharesVarIn] at hs
      simp [denseGroupRewrite, hs]
  | add a b iha ihb =>
      simp only [DenseExpr.hasConstFoldableNode, Bool.or_eq_false_iff, Bool.not_eq_false'] at hf
      obtain ⟨⟨hv, hfa⟩, hfb⟩ := hf
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rw [denseGroupRewrite, if_neg (by
        rw [DenseExpr.varsInF_eq_false hv
          (by simp [DenseExpr.sharesVarIn, hs.1, hs.2])]; simp)]
      rw [iha hs.1 hfa, ihb hs.2 hfb]
  | mul a b iha ihb =>
      simp only [DenseExpr.hasConstFoldableNode, Bool.or_eq_false_iff, Bool.not_eq_false'] at hf
      obtain ⟨⟨hv, hfa⟩, hfb⟩ := hf
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rw [denseGroupRewrite, if_neg (by
        rw [DenseExpr.varsInF_eq_false hv
          (by simp [DenseExpr.sharesVarIn, hs.1, hs.2])]; simp)]
      rw [iha hs.1 hfa, ihb hs.2 hfb]

/-- `denseGroupRewrite` behind the read-only gate. -/
def denseGroupRewriteGate (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  if e.sharesVarIn xs || e.hasConstFoldableNode then denseGroupRewrite xs bits σfn patts e else e

theorem denseGroupRewriteGate_eq (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    denseGroupRewriteGate xs bits σfn patts = denseGroupRewrite xs bits σfn patts := by
  funext e
  unfold denseGroupRewriteGate
  split
  · rfl
  · next h =>
      rw [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true] at h
      exact (denseGroupRewrite_eq_self h.1 h.2).symm

/-- Per-interaction gate: an interaction none of whose expressions can change is kept as-is. -/
def denseBIRewriteGate (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (bi : BusInteraction (DenseExpr p)) :
    BusInteraction (DenseExpr p) :=
  if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
      || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
    { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
              payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
  else bi

theorem denseBIRewriteGate_eq (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    denseBIRewriteGate xs bits σfn patts
      = fun bi => { bi with
          multiplicity := denseGroupRewrite xs bits σfn patts bi.multiplicity,
          payload := bi.payload.map (denseGroupRewrite xs bits σfn patts) } := by
  funext bi
  unfold denseBIRewriteGate
  split
  · rw [denseGroupRewriteGate_eq]
  · next h =>
      rw [Bool.or_eq_true, not_or, Bool.or_eq_true, not_or,
        Bool.not_eq_true, Bool.not_eq_true, List.any_eq_true] at h
      obtain ⟨⟨hm, hf⟩, hp⟩ := h
      have hpl : bi.payload.map (denseGroupRewrite xs bits σfn patts) = bi.payload := by
        have hcg : bi.payload.map (denseGroupRewrite xs bits σfn patts) = bi.payload.map id :=
          List.map_congr_left (fun e he => by
            have he' : ¬(e.sharesVarIn xs = true ∨ e.hasConstFoldableNode = true) := fun hor =>
              hp ⟨e, he, by rw [Bool.or_eq_true]; exact hor⟩
            rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at he'
            exact denseGroupRewrite_eq_self he'.1 he'.2)
        rw [hcg, List.map_id]
      rw [denseGroupRewrite_eq_self hm hf, hpl]

/-- The gated twin of `denseReencodeOut`, with the substitution and pattern list hoisted out of the
    per-interaction closures. -/
def denseReencodeOutFast (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewriteGate xs bits σfn patts)) ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (denseBIRewriteGate xs bits σfn patts) }

@[csimp]
theorem denseReencodeOut_eq_fast : @denseReencodeOut = @denseReencodeOutFast := by
  funext p d xs bits hm
  simp only [denseReencodeOut, denseReencodeOutFast, denseBIRewriteGate_eq,
    denseGroupRewriteGate_eq]

/-! ### The rewrite fused with its degree gate

`denseReencodeStepCached` needs the rewritten system *and* `withinDegreeB` on it. Measured
separately those are two whole-system walks — the gate walk and a `DenseExpr.degree` walk over every
item of the output — and the second is redundant: the gate leaves most items untouched, and an
untouched item's degree is whatever it was in the input. So when the input system is already within
the bound, only the items the gate rewrote (and the fresh booleanity constraints) need measuring.
`denseMapOk` carries the resulting `Bool` alongside the mapped list in one tail-recursive pass;
`denseReencodeOutOk_snd` is where the input-within-bound side condition is discharged. -/

/-- Per-interaction gate paired with the degree test of the interaction it produced. -/
def denseBIGateDeg (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (bi : BusInteraction (DenseExpr p)) :
    BusInteraction (DenseExpr p) × Bool :=
  if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
      || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
    let bi' : BusInteraction (DenseExpr p) :=
      { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
                payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
    (bi', decide (bi'.multiplicity.degree ≤ dmax) &&
      bi'.payload.all (fun e => decide (e.degree ≤ dmax)))
  else (bi, true)

theorem denseBIGateDeg_fst (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (bi : BusInteraction (DenseExpr p)) :
    (denseBIGateDeg dmax xs bits σfn patts bi).1 = denseBIRewriteGate xs bits σfn patts bi := by
  unfold denseBIGateDeg denseBIRewriteGate
  split <;> rfl

/-- The bus side of the fused gate: an interaction none of whose expressions can change is kept
    as-is, and only the ones it rewrites are measured against the degree bound. -/
def denseGateBisGo (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p)) → Bool →
      List (BusInteraction (DenseExpr p)) × Bool
  | [], acc, ok => (acc.reverse, ok)
  | bi :: rest, acc, ok =>
      if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
          || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
        let bi' : BusInteraction (DenseExpr p) :=
          { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
                    payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
        denseGateBisGo dmax xs bits σfn patts rest (bi' :: acc)
          (ok && (decide (bi'.multiplicity.degree ≤ dmax) &&
            bi'.payload.all (fun e => decide (e.degree ≤ dmax))))
      else denseGateBisGo dmax xs bits σfn patts rest (bi :: acc) ok

theorem denseGateBisGo_eq (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    ∀ (l acc : List (BusInteraction (DenseExpr p))) (ok : Bool),
      denseGateBisGo dmax xs bits σfn patts l acc ok
        = (acc.reverse ++ l.map (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).1),
           ok && l.all (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).2)) := by
  intro l
  induction l with
  | nil => intro acc ok; simp [denseGateBisGo]
  | cons bi rest ih =>
      intro acc ok
      rw [denseGateBisGo]
      split
      · next h =>
          rw [ih]
          simp only [List.map_cons, List.all_cons, denseBIGateDeg, if_pos h,
            List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, Bool.and_assoc]
      · next h =>
          rw [ih]
          simp only [List.map_cons, List.all_cons, denseBIGateDeg, if_neg h,
            List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
            Bool.true_and]

/-- Two lists' `all` agree when the predicates agree pointwise on the members. -/
theorem List.all_congr_mem {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## Deferred materialisation: the loop's working system

`denseReencodeOut` rebuilds the whole constraint list on every accept in order to change a handful of
items. The working system below avoids that: a dropped constraint becomes `.const 0` in place, so
positions stay stable; the rewrite rebuilds cons cells only as far as `maxPos`, the last position that
*could* change, and shares the untouched tail; and the booleanity constraints are accumulated and
appended once, since appending them per accept would copy the whole spine and destroy that sharing.

`denseWorkView` is the system this represents. It drops the `.const 0` placeholders, so an accept is
`denseReencodeOut` on the view *followed by* dropping trivially-true constraints
(`denseWorkOut_view`) — and dropping those is already a verified transformation
(`DensePassCorrect.denseFilterConstraintsEntailed`), so both halves reuse existing correctness.

`lastPos`/`lastFold` are the bound: `DenseWorkBounded` says nothing past `maxPos` can change, which
is what licenses sharing the tail. They are maintained monotonically by the splice itself. -/

structure DenseReencodeWork (p : ℕ) where
  cs : List (DenseExpr p)
  bis : List (BusInteraction (DenseExpr p))
  bools : List (DenseExpr p)
  /-- Every bit minted so far. The step refuses a group meeting one, which is what keeps the
      accumulated `bools` inert (`denseBoolConstraint_inert`). -/
  bitSet : Std.HashSet VarId
  /-- For each variable, an upper bound on the positions of `cs` mentioning it. -/
  lastPos : Std.HashMap VarId Nat
  /-- An upper bound on the positions of `cs` carrying a variable-free composite node. -/
  lastFold : Nat
  /-- Whether `lastPos`/`lastFold` have been computed. They are seeded on the first accept rather than
      at pass entry (`denseWorkEnsureBounded`): an APC that never accepts would otherwise pay a full
      variable fold per cleanup cycle for a bound it never consults. -/
  bounded : Bool

def denseIsZero : DenseExpr p → Bool
  | .const n => n == 0
  | _ => false

/-- `denseIsZero` with the field zero as a parameter. The compiler floats the `0`'s whole
    `ZMod.commRing` chain to the head of `denseIsZero`, *before* the constructor test, so a caller
    scanning a list pays four dictionary constructions per item; binding the zero in the function
    that contains the scan hoists it out of the loop. -/
def denseIsZeroW (zero : ZMod p) : DenseExpr p → Bool
  | .const n => n == zero
  | _ => false

theorem denseIsZeroW_zero : denseIsZeroW (0 : ZMod p) = denseIsZero (p := p) := by
  funext e; cases e <;> rfl

def denseWorkView (w : DenseReencodeWork p) : DenseConstraintSystem p :=
  { algebraicConstraints := w.cs.filter (fun c => !denseIsZero c) ++ w.bools,
    busInteractions := w.bis }

/-- Boxed twin: `zero` must be a parameter of the function *containing* the scan. A `let` at the
    head of `denseWorkViewFast` is floated back into the `filter` body by the compiler (verified in
    the generated C), which is the whole cost being removed here. -/
def denseWorkViewW (zero : ZMod p) (w : DenseReencodeWork p) : DenseConstraintSystem p :=
  { algebraicConstraints := w.cs.filter (fun c => !denseIsZeroW zero c) ++ w.bools,
    busInteractions := w.bis }

def denseWorkViewFast (w : DenseReencodeWork p) : DenseConstraintSystem p := denseWorkViewW 0 w

@[csimp] theorem denseWorkView_eq_fast : @denseWorkView = @denseWorkViewFast := by
  funext p w
  simp only [denseWorkView, denseWorkViewFast, denseWorkViewW, denseIsZeroW_zero]

/-- One position's new content: the placeholder if the group covers it, else the gated rewrite. -/
def denseTombify (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (c : DenseExpr p) : DenseExpr p :=
  if denseCoveredBy xs c then .const 0 else denseGroupRewrite xs bits σfn patts c

/-- No position at or past `i + j` beyond `maxPos` can be touched by the rewrite. -/
def DenseWorkBounded (xs : List VarId) (maxPos i : Nat) (cs : List (DenseExpr p)) : Prop :=
  ∀ j c, cs[j]? = some c →
    (denseCoveredBy xs c = true ∨ c.sharesVarIn xs = true ∨ c.hasConstFoldableNode = true) →
    i + j ≤ maxPos

theorem denseTombify_id_of_untouched {xs bits : List VarId} {σfn : VarId → Option (DenseExpr p)}
    {patts : List (List (VarId × ZMod p))} :
    ∀ (l : List (DenseExpr p)),
      (∀ c ∈ l, denseCoveredBy xs c = false ∧ c.sharesVarIn xs = false ∧
        c.hasConstFoldableNode = false) →
      l.map (denseTombify xs bits σfn patts) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro h
      obtain ⟨hcov, hsh, hfd⟩ := h c (List.mem_cons_self ..)
      have htf : denseTombify xs bits σfn patts c = c := by
        simp [denseTombify, hcov, denseGroupRewrite_eq_self hsh hfd]
      rw [List.map_cons, htf, ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

/-- Rewrite the prefix through `maxPos`, then share the tail. `lastPos`/`lastFold` are extended for
    every position the rewrite touches, which keeps `DenseWorkBounded` true for the next group. -/
def denseWorkSpliceCs (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (maxPos : Nat) :
    Nat → List (DenseExpr p) → List (DenseExpr p) → Std.HashMap VarId Nat → Nat → Bool →
      List (DenseExpr p) × Std.HashMap VarId Nat × Nat × Bool
  | _, [], acc, lp, lf, ok => (acc.reverse, lp, lf, ok)
  | i, c :: rest, acc, lp, lf, ok =>
      if maxPos < i then (acc.reverse ++ (c :: rest), lp, lf, ok)
      else if denseCoveredBy xs c then
        denseWorkSpliceCs dmax xs bits σfn patts maxPos (i + 1) rest ((.const 0) :: acc) lp lf ok
      else if c.sharesVarIn xs || c.hasConstFoldableNode then
        let c' := denseGroupRewrite xs bits σfn patts c
        let lp' := c'.vars.foldl (fun m v => m.insert v (max (m.getD v 0) i)) lp
        let lf' := if c'.hasConstFoldableNode then max lf i else lf
        denseWorkSpliceCs dmax xs bits σfn patts maxPos (i + 1) rest (c' :: acc) lp' lf'
          (ok && decide (c'.degree ≤ dmax))
      else denseWorkSpliceCs dmax xs bits σfn patts maxPos (i + 1) rest (c :: acc) lp lf ok

/-- The spliced list is the positionwise `denseTombify` of the input: `maxPos` decides *whether to
    look*, never *what the answer is*, so boundedness makes the two agree. -/
theorem denseWorkSpliceCs_list (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p))) (maxPos : Nat) :
    ∀ (l : List (DenseExpr p)) (i : Nat) (acc : List (DenseExpr p)) (lp : Std.HashMap VarId Nat)
      (lf : Nat) (ok : Bool),
      DenseWorkBounded xs maxPos i l →
      (denseWorkSpliceCs dmax xs bits σfn patts maxPos i l acc lp lf ok).1
        = acc.reverse ++ l.map (denseTombify xs bits σfn patts) := by
  intro l
  induction l with
  | nil => intro i acc lp lf ok _; simp [denseWorkSpliceCs]
  | cons c rest ih =>
      intro i acc lp lf ok hb
      have hrest : DenseWorkBounded xs maxPos (i + 1) rest := by
        intro j c' hj hgate
        have := hb (j + 1) c' (by simpa using hj) hgate
        omega
      rw [denseWorkSpliceCs]
      by_cases hmp : maxPos < i
      · rw [if_pos hmp]
        have hall : ∀ c' ∈ c :: rest, denseCoveredBy xs c' = false ∧ c'.sharesVarIn xs = false ∧
            c'.hasConstFoldableNode = false := by
          intro c' hc'
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hc'
          by_contra hcon
          rw [not_and_or, not_and_or] at hcon
          have hg : denseCoveredBy xs c' = true ∨ c'.sharesVarIn xs = true ∨
              c'.hasConstFoldableNode = true := by
            rcases hcon with h | h
            · exact Or.inl (by simpa using h)
            · rcases h with h | h
              · exact Or.inr (Or.inl (by simpa using h))
              · exact Or.inr (Or.inr (by simpa using h))
          exact absurd (hb j c' hj hg) (by omega)
        rw [denseTombify_id_of_untouched _ hall]
      · rw [if_neg hmp]
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov, ih (i + 1) _ _ _ _ hrest]
          simp only [List.map_cons, denseTombify, if_pos hcov, List.reverse_cons,
            List.append_assoc, List.cons_append, List.nil_append]
        · rw [if_neg hcov]
          rw [Bool.not_eq_true] at hcov
          by_cases hg : c.sharesVarIn xs || c.hasConstFoldableNode
          · rw [if_pos hg, ih (i + 1) _ _ _ _ hrest]
            have htf : denseTombify xs bits σfn patts c
                = denseGroupRewrite xs bits σfn patts c := by simp [denseTombify, hcov]
            simp only [List.map_cons, htf, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append]
          · rw [if_neg hg, ih (i + 1) _ _ _ _ hrest]
            rw [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true] at hg
            have htf : denseTombify xs bits σfn patts c = c := by
              simp [denseTombify, hcov, denseGroupRewrite_eq_self hg.1 hg.2]
            simp only [List.map_cons, htf, List.reverse_cons, List.append_assoc,
              List.cons_append, List.nil_append]

theorem denseCoveredBy_const (xs : List VarId) (n : ZMod p) :
    denseCoveredBy xs (.const n) = false := by
  simp [denseCoveredBy, DenseExpr.hasVar]

/-- Filtering the placeholders out of the tombified list is the same as dropping the covered items
    first and rewriting what is left — the step that lets `denseReencodeOut` reappear. -/
theorem denseTombify_filter (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    ∀ (l : List (DenseExpr p)),
      ((l.map (denseTombify xs bits σfn patts)).filter (fun c => !denseIsZero c))
        = (((l.filter (fun c => !denseIsZero c)).filter
            (fun c => !denseCoveredBy xs c)).map (denseGroupRewrite xs bits σfn patts)).filter
              (fun c => !denseIsZero c) := by
  intro l
  induction l with
  | nil => rfl
  | cons c rest ih =>
      by_cases hz : denseIsZero c = true
      · -- a placeholder stays a placeholder and is dropped on both sides
        obtain ⟨n, rfl⟩ : ∃ n, c = (.const n : DenseExpr p) := by
          cases c with
          | const n => exact ⟨n, rfl⟩
          | var _ => simp [denseIsZero] at hz
          | add _ _ => simp [denseIsZero] at hz
          | mul _ _ => simp [denseIsZero] at hz
        have htf : denseTombify xs bits σfn patts (.const n) = (.const n : DenseExpr p) := by
          simp [denseTombify, denseCoveredBy_const, denseGroupRewrite]
        rw [List.map_cons, htf, List.filter_cons_of_neg (by simp [hz]),
          List.filter_cons_of_neg (by simp [hz]), ih]
      · rw [Bool.not_eq_true] at hz
        by_cases hcov : denseCoveredBy xs c = true
        · have htf : denseTombify xs bits σfn patts c = (.const 0 : DenseExpr p) := by
            simp [denseTombify, hcov]
          rw [List.map_cons, htf, List.filter_cons_of_neg (by simp [denseIsZero]),
            List.filter_cons_of_pos (by simp [hz]),
            List.filter_cons_of_neg (by simp [hcov]), ih]
        · have hcov' : denseCoveredBy xs c = false := by simpa using hcov
          have htf : denseTombify xs bits σfn patts c
              = denseGroupRewrite xs bits σfn patts c := by simp [denseTombify, hcov']
          by_cases hzr : denseIsZero (denseGroupRewrite xs bits σfn patts c) = true
          · simp only [List.map_cons, htf, List.filter_cons, hz, hcov', hzr,
              Bool.not_false, Bool.not_true, if_true]
            exact ih
          · rw [Bool.not_eq_true] at hzr
            simp only [List.map_cons, htf, List.filter_cons, hz, hcov', hzr,
              Bool.not_false, if_true]
            rw [ih]


/-! ### The position bound

`DenseWorkPosOk` is what makes `maxPos` a bound rather than a guess: it says `lastPos` bounds the
positions mentioning each variable and `lastFold` bounds the foldable ones. The splice maintains it,
and `denseWorkBounded_of_posOk` turns it into the `DenseWorkBounded` hypothesis the splice needs. -/

theorem denseSharesVarIn_exists {xs : List VarId} :
    ∀ {c : DenseExpr p}, c.sharesVarIn xs = true → ∃ v ∈ c.vars, v ∈ xs := by
  intro c
  induction c with
  | const n => intro h; simp [DenseExpr.sharesVarIn] at h
  | var y =>
      intro h
      exact ⟨y, by simp [DenseExpr.vars], denseContainsFast_sound xs y (by
        simpa [DenseExpr.sharesVarIn] using h)⟩
  | add a b iha ihb =>
      intro h
      rw [DenseExpr.sharesVarIn, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨v, hv, hx⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hx⟩
      · obtain ⟨v, hv, hx⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hx⟩
  | mul a b iha ihb =>
      intro h
      rw [DenseExpr.sharesVarIn, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨v, hv, hx⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hx⟩
      · obtain ⟨v, hv, hx⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hx⟩

/-- A covered constraint has a variable, and all of them lie in the group, so it shares one. -/
theorem denseCoveredBy_sharesVarIn {xs : List VarId} {c : DenseExpr p}
    (h : denseCoveredBy xs c = true) : c.sharesVarIn xs = true := by
  rw [denseCoveredBy, Bool.and_eq_true] at h
  by_contra hs
  rw [Bool.not_eq_true] at hs
  rw [DenseExpr.varsInF_eq_false h.1 hs] at h
  exact Bool.noConfusion h.2

def DenseWorkPosOk (lp : Std.HashMap VarId Nat) (lf : Nat) (cs : List (DenseExpr p)) : Prop :=
  ∀ j c, cs[j]? = some c →
    (∀ v ∈ c.vars, j ≤ lp.getD v 0) ∧ (c.hasConstFoldableNode = true → j ≤ lf)

def denseWorkMaxPos (lp : Std.HashMap VarId Nat) (lf : Nat) (xs : List VarId) : Nat :=
  xs.foldl (fun m x => max m (lp.getD x 0)) lf

theorem denseWorkMaxPos_ge_lf (lp : Std.HashMap VarId Nat) (lf : Nat) (xs : List VarId) :
    lf ≤ denseWorkMaxPos lp lf xs := by
  unfold denseWorkMaxPos
  suffices h : ∀ (l : List VarId) (acc : Nat), acc ≤ l.foldl (fun m x => max m (lp.getD x 0)) acc by
    exact h xs lf
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl acc
  | cons y rest ih => intro acc; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem denseWorkMaxPos_ge_mem {lp : Std.HashMap VarId Nat} {lf : Nat} {xs : List VarId} {v : VarId}
    (hv : v ∈ xs) : lp.getD v 0 ≤ denseWorkMaxPos lp lf xs := by
  unfold denseWorkMaxPos
  suffices h : ∀ (l : List VarId) (acc : Nat), v ∈ l →
      lp.getD v 0 ≤ l.foldl (fun m x => max m (lp.getD x 0)) acc by
    exact h xs lf hv
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons y rest ih =>
      intro acc h
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right acc _)
          (denseWorkMaxPos_ge_lf lp (max acc (lp.getD v 0)) rest)
      · exact ih _ h

theorem denseWorkBounded_of_posOk {lp : Std.HashMap VarId Nat} {lf : Nat} {xs : List VarId}
    {cs : List (DenseExpr p)} (h : DenseWorkPosOk lp lf cs) :
    DenseWorkBounded xs (denseWorkMaxPos lp lf xs) 0 cs := by
  intro j c hj hgate
  rw [Nat.zero_add]
  obtain ⟨hvars, hfold⟩ := h j c hj
  rcases hgate with hcov | hsh | hfd
  · obtain ⟨v, hv, hx⟩ := denseSharesVarIn_exists (denseCoveredBy_sharesVarIn hcov)
    exact Nat.le_trans (hvars v hv) (denseWorkMaxPos_ge_mem hx)
  · obtain ⟨v, hv, hx⟩ := denseSharesVarIn_exists hsh
    exact Nat.le_trans (hvars v hv) (denseWorkMaxPos_ge_mem hx)
  · exact Nat.le_trans (hfold hfd) (denseWorkMaxPos_ge_lf lp lf xs)


/-! ### Maintaining the bound

The splice only ever raises `lastPos`/`lastFold`, and raises them at every position it rewrites, so
`DenseWorkPosOk` survives an accept. `DenseLpLe` is the pointwise order that makes "only raises"
usable: the already-processed prefix keeps its bound because the map only grew. -/

def DenseLpLe (lp lp' : Std.HashMap VarId Nat) : Prop := ∀ v, lp.getD v 0 ≤ lp'.getD v 0

theorem DenseLpLe.refl (lp : Std.HashMap VarId Nat) : DenseLpLe lp lp := fun _ => Nat.le_refl _

theorem DenseLpLe.trans {a b c : Std.HashMap VarId Nat} (h1 : DenseLpLe a b) (h2 : DenseLpLe b c) :
    DenseLpLe a c := fun v => Nat.le_trans (h1 v) (h2 v)

theorem denseLpStep_mono (m : Std.HashMap VarId Nat) (v : VarId) (i : Nat) :
    DenseLpLe m (m.insert v (max (m.getD v 0) i)) := by
  intro u
  by_cases h : u = v
  · subst h
    rw [Std.HashMap.getD_insert]
    simp only [beq_self_eq_true, if_true]
    exact Nat.le_max_left _ _
  · rw [Std.HashMap.getD_insert, show (v == u) = false from by simpa using (Ne.symm h)]
    simp

theorem denseLpFold_mono (i : Nat) :
    ∀ (vs : List VarId) (m : Std.HashMap VarId Nat),
      DenseLpLe m (vs.foldl (fun m v => m.insert v (max (m.getD v 0) i)) m) := by
  intro vs
  induction vs with
  | nil => intro m; exact DenseLpLe.refl m
  | cons v rest ih =>
      intro m
      exact DenseLpLe.trans (denseLpStep_mono m v i) (ih _)

theorem denseLpFold_ge (i : Nat) :
    ∀ (vs : List VarId) (m : Std.HashMap VarId Nat) (u : VarId), u ∈ vs →
      i ≤ (vs.foldl (fun m v => m.insert v (max (m.getD v 0) i)) m).getD u 0 := by
  intro vs
  induction vs with
  | nil => intro _ _ h; simp at h
  | cons v rest ih =>
      intro m u h
      rcases List.mem_cons.mp h with rfl | h
      · refine Nat.le_trans ?_ (denseLpFold_mono i rest (m.insert u (max (m.getD u 0) i)) u)
        rw [Std.HashMap.getD_insert]
        simp only [beq_self_eq_true, if_true]
        exact Nat.le_max_right _ _
      · exact ih _ u h

def DenseWorkPosOkFrom (off : Nat) (lp : Std.HashMap VarId Nat) (lf : Nat)
    (cs : List (DenseExpr p)) : Prop :=
  ∀ j c, cs[j]? = some c →
    (∀ v ∈ c.vars, off + j ≤ lp.getD v 0) ∧ (c.hasConstFoldableNode = true → off + j ≤ lf)

theorem densePosOkFrom_mono {off : Nat} {lp lp' : Std.HashMap VarId Nat} {lf lf' : Nat}
    {cs : List (DenseExpr p)} (hlp : DenseLpLe lp lp') (hlf : lf ≤ lf')
    (h : DenseWorkPosOkFrom off lp lf cs) : DenseWorkPosOkFrom off lp' lf' cs := by
  intro j c hj
  obtain ⟨hv, hf⟩ := h j c hj
  exact ⟨fun v hvm => Nat.le_trans (hv v hvm) (hlp v), fun hfd => Nat.le_trans (hf hfd) hlf⟩

theorem densePosOkFrom_append {lp : Std.HashMap VarId Nat} {lf : Nat}
    {u v : List (DenseExpr p)} (hu : DenseWorkPosOkFrom 0 lp lf u)
    (hv : DenseWorkPosOkFrom u.length lp lf v) : DenseWorkPosOkFrom 0 lp lf (u ++ v) := by
  intro j c hj
  by_cases h : j < u.length
  · exact hu j c (by rwa [List.getElem?_append_left h] at hj)
  · rw [List.getElem?_append_right (by omega)] at hj
    have := hv (j - u.length) c hj
    rw [show u.length + (j - u.length) = j by omega] at this
    simpa using this

theorem densePosOkFrom_cons_last {lp : Std.HashMap VarId Nat} {lf : Nat}
    {u : List (DenseExpr p)} {c : DenseExpr p} (hu : DenseWorkPosOkFrom 0 lp lf u)
    (hc : (∀ v ∈ c.vars, u.length ≤ lp.getD v 0) ∧
      (c.hasConstFoldableNode = true → u.length ≤ lf)) :
    DenseWorkPosOkFrom 0 lp lf (u ++ [c]) := by
  refine densePosOkFrom_append hu ?_
  intro j c' hj
  cases j with
  | zero =>
      rw [List.getElem?_cons_zero, Option.some_inj] at hj
      subst hj
      simpa using hc
  | succ k => simp at hj


/-- The position bound survives an accept: the splice raises `lastPos`/`lastFold` at exactly the
    positions it rewrites, and only ever raises them, so the untouched prefix keeps its bound. -/
theorem denseWorkSpliceCs_posOk (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p))) (maxPos : Nat) :
    ∀ (l : List (DenseExpr p)) (i : Nat) (acc : List (DenseExpr p)) (lp : Std.HashMap VarId Nat)
      (lf : Nat) (ok : Bool),
      acc.length = i →
      DenseWorkPosOkFrom 0 lp lf acc.reverse →
      DenseWorkPosOkFrom i lp lf l →
      DenseWorkPosOkFrom 0
        (denseWorkSpliceCs dmax xs bits σfn patts maxPos i l acc lp lf ok).2.1
        (denseWorkSpliceCs dmax xs bits σfn patts maxPos i l acc lp lf ok).2.2.1
        (denseWorkSpliceCs dmax xs bits σfn patts maxPos i l acc lp lf ok).1 := by
  intro l
  induction l with
  | nil =>
      intro i acc lp lf ok _ hacc _
      simpa [denseWorkSpliceCs] using hacc
  | cons c rest ih =>
      intro i acc lp lf ok hlen hacc hl
      have hhead := hl 0 c (by simp)
      have hrest : DenseWorkPosOkFrom (i + 1) lp lf rest := by
        intro j c' hj
        have := hl (j + 1) c' (by simpa using hj)
        rw [show i + (j + 1) = i + 1 + j by omega] at this
        exact this
      rw [denseWorkSpliceCs]
      by_cases hmp : maxPos < i
      · rw [if_pos hmp]
        refine densePosOkFrom_append hacc ?_
        intro j c' hj
        simp only [List.length_reverse, hlen]
        exact hl j c' hj
      · rw [if_neg hmp]
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov]
          refine ih (i + 1) _ lp lf ok (by simp [hlen]) ?_ hrest
          -- the placeholder has no variables and no foldable node
          rw [List.reverse_cons]
          refine densePosOkFrom_cons_last hacc ?_
          refine ⟨fun v hv => by simp [DenseExpr.vars] at hv, fun hfd => ?_⟩
          simp [DenseExpr.hasConstFoldableNode] at hfd
        · rw [if_neg hcov]
          by_cases hg : c.sharesVarIn xs || c.hasConstFoldableNode
          · rw [if_pos hg]
            set c' := denseGroupRewrite xs bits σfn patts c with hc'
            set lp' := c'.vars.foldl (fun m v => m.insert v (max (m.getD v 0) i)) lp with hlp'
            set lf' := if c'.hasConstFoldableNode then max lf i else lf with hlf'
            have hmono : DenseLpLe lp lp' := denseLpFold_mono i _ lp
            have hlfle : lf ≤ lf' := by
              rw [hlf']; split <;> [exact Nat.le_max_left _ _; exact Nat.le_refl _]
            refine ih (i + 1) _ lp' lf' _ (by simp [hlen]) ?_
              (densePosOkFrom_mono hmono hlfle hrest)
            rw [List.reverse_cons]
            refine densePosOkFrom_cons_last (densePosOkFrom_mono hmono hlfle hacc) ?_
            rw [List.length_reverse, hlen]
            refine ⟨fun v hv => denseLpFold_ge i _ lp v hv, fun hfd => ?_⟩
            rw [hlf', if_pos hfd]
            exact Nat.le_max_right _ _
          · rw [if_neg hg]
            refine ih (i + 1) _ lp lf ok (by simp [hlen]) ?_ hrest
            rw [List.reverse_cons]
            refine densePosOkFrom_cons_last hacc ?_
            rw [List.length_reverse, hlen]
            simpa using hhead


/-! ### The accumulated booleanity constraints

Deferring the bools is what lets the splice share its tail, and it is sound because a bool is inert
for every later group: `denseBoolConstraint b` mentions only `b`, so as long as `b ∉ xs` it is not
covered, the rewrite is the identity on it, and it is not a placeholder. `DenseWorkBoolsOk` records
that every accumulated bool belongs to a minted bit, and the step's `bitSet` guard supplies `b ∉ xs`
directly — cheaper than deriving it from registry freshness, and sound either way since rejecting a
candidate is always allowed. -/

def DenseWorkBoolsOk (bitSet : Std.HashSet VarId) (bools : List (DenseExpr p)) : Prop :=
  ∀ c ∈ bools, ∃ b, c = (denseBoolConstraint b : DenseExpr p) ∧ bitSet.contains b = true

theorem denseContainsFast_of_not_mem {xs : List VarId} {b : VarId} (hb : b ∉ xs) :
    denseContainsFast xs b = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact absurd (denseContainsFast_sound xs b h) hb

theorem denseBoolConstraint_inert {xs : List VarId} {b : VarId} (hb : b ∉ xs) :
    denseCoveredBy xs (denseBoolConstraint b : DenseExpr p) = false ∧
    (denseBoolConstraint b : DenseExpr p).sharesVarIn xs = false ∧
    (denseBoolConstraint b : DenseExpr p).hasConstFoldableNode = false ∧
    denseIsZero (denseBoolConstraint b : DenseExpr p) = false := by
  have hc := denseContainsFast_of_not_mem (xs := xs) (b := b) hb
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp [denseCoveredBy, denseBoolConstraint, DenseExpr.varsInF, hc]
  · simp [denseBoolConstraint, DenseExpr.sharesVarIn, hc]
  · simp [denseBoolConstraint, DenseExpr.hasConstFoldableNode, DenseExpr.hasVar]

theorem denseWorkBools_filter_covered {xs : List VarId} {bitSet : Std.HashSet VarId}
    {bools : List (DenseExpr p)} (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (hb : DenseWorkBoolsOk bitSet bools)
    (hxs : ∀ x ∈ xs, bitSet.contains x = false) :
    bools.filter (fun c => !denseCoveredBy xs c) = bools ∧
    bools.map (denseGroupRewrite xs bits σfn patts) = bools ∧
    bools.filter (fun c => !denseIsZero c) = bools := by
  have hinert : ∀ c ∈ bools, denseCoveredBy xs c = false ∧ c.sharesVarIn xs = false ∧
      c.hasConstFoldableNode = false ∧ denseIsZero c = false := by
    intro c hc
    obtain ⟨bb, rfl, hbb⟩ := hb c hc
    refine denseBoolConstraint_inert (fun hmem => ?_)
    rw [hxs bb hmem] at hbb
    exact Bool.noConfusion hbb
  refine ⟨?_, ?_, ?_⟩
  · refine List.filter_eq_self.2 (fun c hc => ?_)
    simp [(hinert c hc).1]
  · rw [show bools.map (denseGroupRewrite xs bits σfn patts) = bools.map id from
      List.map_congr_left (fun c hc =>
        denseGroupRewrite_eq_self (hinert c hc).2.1 (hinert c hc).2.2.1), List.map_id]
  · refine List.filter_eq_self.2 (fun c hc => ?_)
    simp [(hinert c hc).2.2.2]

theorem denseBoolConstraints_not_zero (bits : List VarId) :
    (bits.map (denseBoolConstraint (p := p))).filter (fun c => !denseIsZero c)
      = bits.map (denseBoolConstraint (p := p)) := by
  refine List.filter_eq_self.2 (fun c hc => ?_)
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hc
  simp [denseIsZero, denseBoolConstraint]


/-- One accept on the working system: splice the constraints, gate the bus interactions (reusing the
    fused traversal of `denseGateBisGo`), and accumulate the booleanity constraints. Assumes the
    position bound is computed — `denseWorkStep` calls `denseWorkEnsureBounded` first. -/
def denseWorkOut (b : DegreeBound) (w : DenseReencodeWork p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseReencodeWork p × Bool :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let mp := denseWorkMaxPos w.lastPos w.lastFold xs
  let rc := denseWorkSpliceCs b.identities xs bits σfn patts mp 0 w.cs [] w.lastPos w.lastFold true
  let rb := denseGateBisGo b.busInteractions xs bits σfn patts w.bis [] true
  let newBools := bits.map (denseBoolConstraint (p := p))
  ({ cs := rc.1, bis := rb.1, bools := w.bools ++ newBools,
     bitSet := bits.foldl (·.insert ·) w.bitSet,
     lastPos := rc.2.1, lastFold := rc.2.2.1, bounded := true },
   (rc.2.2.2 && newBools.all (fun c => decide (c.degree ≤ b.identities))) && rb.2)

/-- An accept on the working system is `denseReencodeOut` on the view, followed by dropping the
    placeholders — and dropping those is itself a verified transformation
    (`DensePassCorrect.denseFilterConstraintsEntailed`), so both halves reuse existing correctness. -/
theorem denseWorkOut_view (b : DegreeBound) (w : DenseReencodeWork p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hpos : DenseWorkPosOk w.lastPos w.lastFold w.cs)
    (hbools : DenseWorkBoolsOk w.bitSet w.bools)
    (hxs : ∀ x ∈ xs, w.bitSet.contains x = false) :
    denseWorkView (denseWorkOut b w xs bits hm).1
      = (denseReencodeOut (denseWorkView w) xs bits hm).filterConstraints
          (fun c => !denseIsZero c) := by
  obtain ⟨hbcov, hbmap, hbz⟩ := denseWorkBools_filter_covered (bools := w.bools) bits
    (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits)) hbools hxs
  have hsplice : (denseWorkSpliceCs b.identities xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) (denseWorkMaxPos w.lastPos w.lastFold xs) 0 w.cs []
      w.lastPos w.lastFold true).1
      = w.cs.map (denseTombify xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) := by
    have := denseWorkSpliceCs_list b.identities xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) (denseWorkMaxPos w.lastPos w.lastFold xs)
      w.cs 0 [] w.lastPos w.lastFold true (denseWorkBounded_of_posOk hpos)
    simpa using this
  have hbus : (denseGateBisGo b.busInteractions xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) w.bis [] true).1
      = w.bis.map (fun bi => { bi with
          multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits)) bi.multiplicity,
          payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits))) }) := by
    rw [denseGateBisGo_eq]
    simp only [List.reverse_nil, List.nil_append]
    exact List.map_congr_left (fun bi _ => by
      rw [denseBIGateDeg_fst, denseBIRewriteGate_eq])
  unfold denseWorkView denseWorkOut denseReencodeOut DenseConstraintSystem.filterConstraints
  simp only [hsplice, hbus, List.filter_append, List.map_append, List.append_assoc,
    hbcov, hbmap, hbz, denseBoolConstraints_not_zero]
  rw [denseTombify_filter]


/-! ### Reading the certificate off the working system

The loop must not materialise the view per candidate — that would allocate a fresh spine for the whole
system on every candidate, which is the cost this design exists to remove. The certificate only looks
at the covered sublist and at whether anything mentions a fresh bit, and both are unaffected by the
placeholders (they mention nothing and are never covered) and by the accumulated bools (inert, by
`denseBoolConstraint_inert` and the step's guards). So it reads `w.cs` directly. -/

theorem List.all_filter_of {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ c ∈ l, P c = false → Q c = true) : (l.filter P).all Q = l.all Q := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
      by_cases hp : P c = true
      · rw [List.filter_cons_of_pos hp, List.all_cons, List.all_cons,
          ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      · rw [Bool.not_eq_true] at hp
        rw [List.filter_cons_of_neg (by simp [hp]), List.all_cons,
          h c (List.mem_cons_self ..) hp, Bool.true_and,
          ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

theorem List.filter_filter_of {α : Type} (l : List α) (P R : α → Bool)
    (h : ∀ c ∈ l, P c = false → R c = false) : (l.filter P).filter R = l.filter R := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
      by_cases hp : P c = true
      · rw [List.filter_cons_of_pos hp]
        by_cases hr : R c = true
        · rw [List.filter_cons_of_pos hr, List.filter_cons_of_pos hr,
            ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
        · rw [Bool.not_eq_true] at hr
          rw [List.filter_cons_of_neg (by simp [hr]), List.filter_cons_of_neg (by simp [hr]),
            ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      · rw [Bool.not_eq_true] at hp
        rw [List.filter_cons_of_neg (by simp [hp]),
          List.filter_cons_of_neg (by simp [h c (List.mem_cons_self ..) hp]),
          ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

theorem denseIsZero_mentions {c : DenseExpr p} (hz : denseIsZero c = true) (b : VarId) :
    c.mentions b = false := by
  cases c with
  | const n => rfl
  | var _ => simp [denseIsZero] at hz
  | add _ _ => simp [denseIsZero] at hz
  | mul _ _ => simp [denseIsZero] at hz

theorem denseIsZero_not_covered {xs : List VarId} {c : DenseExpr p} (hz : denseIsZero c = true) :
    denseCoveredBy xs c = false := by
  cases c with
  | const n => simp [denseCoveredBy, DenseExpr.hasVar]
  | var _ => simp [denseIsZero] at hz
  | add _ _ => simp [denseIsZero] at hz
  | mul _ _ => simp [denseIsZero] at hz

theorem denseIsZero_eval {c : DenseExpr p} (hz : denseIsZero c = true) (denv : VarId → ZMod p) :
    c.eval denv = 0 := by
  cases c with
  | const n =>
      have hn : n = 0 := by simpa [denseIsZero] using hz
      simp [DenseExpr.eval, hn]
  | var _ => simp [denseIsZero] at hz
  | add _ _ => simp [denseIsZero] at hz
  | mul _ _ => simp [denseIsZero] at hz

theorem denseCheckReencode_congr (cs1 cs2 : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hcov : cs1.filter (denseCoveredBy xs) = cs2.filter (denseCoveredBy xs))
    (hfresh : ∀ b ∈ bits, cs1.all (fun c => !c.mentions b) = cs2.all (fun c => !c.mentions b)) :
    denseCheckReencode { algebraicConstraints := cs1, busInteractions := bis } xs bits hm
      = denseCheckReencode { algebraicConstraints := cs2, busInteractions := bis } xs bits hm := by
  have hb : (bits.all (fun b =>
        cs1.all (fun c => !c.mentions b) &&
        bis.all (fun bi =>
          !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b))))
      = (bits.all (fun b =>
        cs2.all (fun c => !c.mentions b) &&
        bis.all (fun bi =>
          !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b)))) :=
    List.all_congr_mem bits _ _ (fun b hbm => by rw [hfresh b hbm])
  unfold denseCheckReencode denseCoveredCsOf
  simp only [hcov, hb]


theorem denseWorkView_check {w : DenseReencodeWork p} {xs bits : List VarId}
    (hm : Std.HashMap VarId (DenseExpr p))
    (hbools : DenseWorkBoolsOk w.bitSet w.bools)
    (hxs : ∀ x ∈ xs, w.bitSet.contains x = false)
    (hbits : ∀ bb ∈ bits, w.bitSet.contains bb = false) :
    denseCheckReencode (denseWorkView w) xs bits hm
      = denseCheckReencode { algebraicConstraints := w.cs, busInteractions := w.bis } xs bits hm := by
  have hinert : ∀ c ∈ w.bools, denseCoveredBy xs c = false ∧ ∀ b ∈ bits, c.mentions b = false := by
    intro c hc
    obtain ⟨bb, rfl, hbb⟩ := hbools c hc
    have hnx : bb ∉ xs := fun hmem => by rw [hxs bb hmem] at hbb; exact Bool.noConfusion hbb
    refine ⟨(denseBoolConstraint_inert (p := p) hnx).1, fun b hb => ?_⟩
    have hne : bb ≠ b := fun heq => by
      subst heq; rw [hbits bb hb] at hbb; exact Bool.noConfusion hbb
    simp [denseBoolConstraint, DenseExpr.mentions, hne]
  refine denseCheckReencode_congr _ _ _ xs bits hm ?_ ?_
  · show ((w.cs.filter (fun c => !denseIsZero c) ++ w.bools).filter (denseCoveredBy xs))
      = w.cs.filter (denseCoveredBy xs)
    have h1 : w.bools.filter (denseCoveredBy xs) = [] :=
      List.filter_eq_nil_iff.2 (fun c hc => by simp [(hinert c hc).1])
    have h2 : (w.cs.filter (fun c => !denseIsZero c)).filter (denseCoveredBy xs)
        = w.cs.filter (denseCoveredBy xs) :=
      List.filter_filter_of _ _ _ (fun c _ hz => denseIsZero_not_covered (by simpa using hz))
    rw [List.filter_append, h2, h1, List.append_nil]
  · intro b hb
    show ((w.cs.filter (fun c => !denseIsZero c) ++ w.bools).all (fun c => !c.mentions b))
      = w.cs.all (fun c => !c.mentions b)
    have h1 : w.bools.all (fun c => !c.mentions b) = true :=
      List.all_eq_true.2 (fun c hc => by simp [(hinert c hc).2 b hb])
    have h2 : (w.cs.filter (fun c => !denseIsZero c)).all (fun c => !c.mentions b)
        = w.cs.all (fun c => !c.mentions b) :=
      List.all_filter_of _ _ _ (fun c _ hz => by
        simp [denseIsZero_mentions (by simpa using hz) b])
    rw [List.all_append, h2, h1, Bool.and_true]

/-! ### Seeding the bound -/

def denseSeedLp : Nat → List (DenseExpr p) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | _, [], m => m
  | i, c :: rest, m =>
      denseSeedLp (i + 1) rest (c.vars.foldl (fun m v => m.insert v (max (m.getD v 0) i)) m)

def denseSeedLf : Nat → List (DenseExpr p) → Nat → Nat
  | _, [], n => n
  | i, c :: rest, n => denseSeedLf (i + 1) rest (if c.hasConstFoldableNode then max n i else n)

theorem denseSeedLp_mono : ∀ (l : List (DenseExpr p)) (i : Nat) (m : Std.HashMap VarId Nat),
    DenseLpLe m (denseSeedLp i l m) := by
  intro l
  induction l with
  | nil => intro i m; exact DenseLpLe.refl m
  | cons c rest ih =>
      intro i m
      exact DenseLpLe.trans (denseLpFold_mono i _ m) (ih (i + 1) _)

theorem denseSeedLf_mono : ∀ (l : List (DenseExpr p)) (i : Nat) (n : Nat), n ≤ denseSeedLf i l n := by
  intro l
  induction l with
  | nil => intro i n; exact Nat.le_refl n
  | cons c rest ih =>
      intro i n
      refine Nat.le_trans ?_ (ih (i + 1) _)
      split <;> [exact Nat.le_max_left _ _; exact Nat.le_refl _]

theorem denseSeed_posOk : ∀ (l : List (DenseExpr p)) (i : Nat) (m : Std.HashMap VarId Nat)
    (n : Nat), DenseWorkPosOkFrom i (denseSeedLp i l m) (denseSeedLf i l n) l := by
  intro l
  induction l with
  | nil => intro i m n j c hj; simp at hj
  | cons c rest ih =>
      intro i m n j c' hj
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero, Option.some_inj] at hj
          subst hj
          refine ⟨fun v hv => ?_, fun hfd => ?_⟩
          · rw [Nat.add_zero, denseSeedLp]
            exact Nat.le_trans (denseLpFold_ge i _ m v hv) (denseSeedLp_mono rest (i + 1) _ v)
          · rw [Nat.add_zero, denseSeedLf]
            exact Nat.le_trans (by rw [if_pos hfd]; exact Nat.le_max_right _ _)
              (denseSeedLf_mono rest (i + 1) _)
      | succ k =>
          have hk := ih (i + 1) (c.vars.foldl (fun m v => m.insert v (max (m.getD v 0) i)) m)
            (if c.hasConstFoldableNode then max n i else n) k c' (by simpa using hj)
          rw [show i + (k + 1) = i + 1 + k by omega]
          rw [denseSeedLp, denseSeedLf]
          exact hk

/-! ## The build/step/loop/pass layer -/

inductive DenseReencodeRootPlan (p : ℕ)
  | any (roots : List (ZMod p))
  | one (var : VarId) (roots : List (ZMod p))

def denseReencodeRootPlanMul :
    DenseReencodeRootPlan p → DenseReencodeRootPlan p → Option (DenseReencodeRootPlan p)
  | .any left, .any right => some (.any (left ++ right))
  | .any left, .one var right => some (.one var (left ++ right))
  | .one var left, .any right => some (.one var (left ++ right))
  | .one leftVar left, .one rightVar right =>
      if leftVar = rightVar then some (.one leftVar (left ++ right)) else none

def denseBuildReencodeRootPlan : DenseExpr p → Option (DenseReencodeRootPlan p)
  | .mul a b =>
      match denseBuildReencodeRootPlan a, denseBuildReencodeRootPlan b with
      | some left, some right => denseReencodeRootPlanMul left right
      | _, _ => none
  | e =>
      match denseLinearize e with
      | none => none
      | some l =>
          let l := l.norm
          match l.terms with
          | [] => if l.const = 0 then none else some (.any [])
          | [(i, _)] => (denseRootsOfTerms i l.const l.terms).map (.one i)
          | _ => none

def denseReencodeRootPlanLookup (i : VarId) :
    DenseReencodeRootPlan p → Option (List (ZMod p))
  | .any roots => some roots
  | .one var roots => if var = i then some roots else none

abbrev DenseReencodeRootCache (p : ℕ) :=
  Std.HashMap Nat (Option (DenseReencodeRootPlan p))

def denseReencodeRootAt (cache : DenseReencodeRootCache p) (pos : Nat) (c : DenseExpr p) :
    Option (DenseReencodeRootPlan p) × DenseReencodeRootCache p :=
  match cache[pos]? with
  | some plan => (plan, cache)
  | none =>
      let plan := denseBuildReencodeRootPlan c
      (plan, cache.insert pos plan)

def denseFindDomainCached (i : VarId) :
    List (Nat × DenseExpr p) → DenseReencodeRootCache p →
      Option (List (ZMod p)) × DenseReencodeRootCache p
  | [], cache => (none, cache)
  | c :: rest, cache =>
      if c.2.mentions i then
        let (plan, cache) := denseReencodeRootAt cache c.1 c.2
        match plan.bind (denseReencodeRootPlanLookup i) with
        | some roots => (some roots, cache)
        | none => denseFindDomainCached i rest cache
      else denseFindDomainCached i rest cache

def denseGroupDomsCached (es : List (Nat × DenseExpr p)) :
    List VarId → DenseReencodeRootCache p →
      Option (List (VarId × List (ZMod p))) × DenseReencodeRootCache p
  | [], cache => (some [], cache)
  | i :: rest, cache =>
      let (head, cache) := denseFindDomainCached i es cache
      let (tail, cache) := denseGroupDomsCached es rest cache
      match head, tail with
      | some d, some ds => (some ((i, d) :: ds), cache)
      | _, _ => (none, cache)

def denseCoveredIdxPos (idx : DenseCovIndex) (arr : Array (DenseExpr p))
    (xs : List VarId) : List (Nat × DenseExpr p) :=
  let uniq := ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then
      if denseCoveredBy xs arr[i] then some (i, arr[i]) else none
    else none)

/-- Build the inverted index (`VarId`-keyed twin of `CoveredIndex.buildPruned`), skipping items
    with more than `maxVars` distinct variables. -/
def denseBuildPruned {α : Type} (varsOf : α → List VarId) (maxVars : Nat) (items : List α) :
    DenseCovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    if (HashedDedup.hashedEraseDups (hash ·) (varsOf ai.1)).length ≤ maxVars then
      denseBuildStep varsOf ai idx
    else idx) ⟨∅, []⟩

/-- Register the `k` fresh bit variables `freshBase ++ "_0", …, freshBase ++ "_(k-1)"` into `reg`,
    in order. -/
def denseRegisterBits (reg : VarRegistry) (freshBase : String) (k : Nat) :
    VarRegistry × List VarId :=
  (List.range k).foldl
    (fun (acc : VarRegistry × List VarId) (j : Nat) =>
      let (r, bs) := acc
      let (r', i) := r.register ({ name := freshBase ++ "_" ++ toString j } : Variable)
      (r', bs ++ [i]))
    (reg, [])

/-- Construct the bits and the substitution map for a candidate group (proof-free — the checked
    certificate re-verifies everything). Registers fresh bits only on the single accepting path.
    Positions come from the bucket index, and the per-constraint root plans from the retained
    cache. -/
def denseBuildReencodeCached (reg : VarRegistry) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (cache : DenseReencodeRootCache p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) ×
      DenseReencodeRootCache p :=
  let planned := denseCoveredIdxPos csIdx arrCs xs
  let es := planned.map Prod.snd
  let (doms?, cache) := denseGroupDomsCached planned xs cache
  match doms? with
  | none => (reg, none, cache)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        (reg, none, cache)
      else
      match denseGroupSurvivorsECap es doms (2 ^ (xs.length - 1)) with
      | none => (reg, none, cache)
      | some survs =>
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1,
            some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))),
            cache)
        else (reg, none, cache)
      else (reg, none, cache)
    else (reg, none, cache)

/-- The index's candidate positions for `xs`, each once (an item is bucketed per variable
    occurrence, and the gate below rewrites every position it visits). -/
def denseUsePositions (idx : DenseCovIndex) (xs : List VarId) : List Nat :=
  ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList

/-- Degree pre-gate (untrusted): rewrite only the items sharing a variable with the group and fire
    when a rewritten item already exceeds the bound. Only the indexed candidate positions are
    visited — the buckets are complete, so every item outside them is variable-disjoint from `xs`
    and cannot fire. Stale bucket entries (the cached loop's indexes are grow-only) are harmless:
    each position's current content is re-tested. -/
def denseDegPreRejectIdx (b : DegreeBound) (csIdxUse biIdxUse : DenseCovIndex)
    (arrBis : Array (BusInteraction (DenseExpr p)))
    (arrCs : Array (DenseExpr p)) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let σ := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  (denseUsePositions csIdxUse xs).any (fun i =>
    match arrCs[i]? with
    | some c =>
      c.sharesVarIn xs && !denseCoveredBy xs c &&
        decide (b.identities < (denseGroupRewrite xs bits σ patts c).degree)
    | none => false) ||
  (denseUsePositions biIdxUse xs).any (fun i =>
    match arrBis[i]? with
    | some bi =>
      (bi.multiplicity.sharesVarIn xs &&
        decide (b.busInteractions < (denseGroupRewrite xs bits σ patts bi.multiplicity).degree)) ||
      bi.payload.any (fun e =>
        e.sharesVarIn xs &&
          decide (b.busInteractions < (denseGroupRewrite xs bits σ patts e).degree))
    | none => false)

/-- The cached loop's candidate-state, kept on stable positions across accepts: dropped
    constraints become `.const 0` tombstones (variable-free, so every index query skips them),
    the bucket indexes are grow-only, and `denseReencodeStateUpdate` touches only the positions
    an accept can change — nothing here is rebuilt per accepted group. `varSet` only ever gains
    the fresh bits, so it over-approximates the live variables; a group whose variable was
    eliminated by an earlier accept passes that gate and is then rejected by the certificate
    (no covered constraint mentions the variable), the same outcome the exact set produces. -/
structure DenseReencodeCacheState (p : ℕ) where
  csIdx : DenseCovIndex
  arrCs : Array (DenseExpr p)
  rootCache : DenseReencodeRootCache p
  varSet : Std.HashSet VarId
  useCs : DenseCovIndex
  useBis : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))
  foldCs : Std.HashSet Nat
  /-- The number of non-tombstone entries of `w.cs`, and `w.bis.length`. Both feed the fresh-name
      prefix only (`denseWorkNameCountsS`), which is why they live on the untrusted state: a wrong
      count can cost a rejected candidate, never soundness. Maintained exactly — the state update
      visits every position an accept can turn into `.const 0`. -/
  liveCs : Nat
  bisN : Nat
  /-- Whether `d` is *known* to be within the degree bound — the side condition that makes
      `denseReencodeOutOk`'s fused degree test agree with measuring the rewritten system outright
      (`denseReencodeOutOk_snd`). Starts `false`, so the first candidate to reach the gate measures
      the rewritten system the plain way; from the first accept on it is `true`, since an accepted
      `ro` passed the gate and becomes the new `d`. Deliberately not seeded with
      `d.withinDegreeB b`: that walk would be charged to every APC, including the ones where no
      candidate is ever accepted. -/
  dWithin : Bool

/-- Apply an accepted rewrite to the threaded state in place, mirroring `denseReencodeOut` on the
    stable-position arrays: only positions holding a group variable (bucket candidates) or a
    variable-free composite node (`foldCs`) can change. The root cache keeps every untouched
    position (it memoizes a pure function of the position's content). -/
def denseReencodeStateUpdate (state : DenseReencodeCacheState p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseReencodeCacheState p :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let bucketAdd : DenseCovIndex → List VarId → Nat → DenseCovIndex := fun idx vs i =>
    ⟨vs.foldl (fun m v => m.insert v (i :: m.getD v [])) idx.buckets, idx.varless⟩
  let posC := (denseCandidates state.useCs xs).foldl (·.insert ·) state.foldCs
  let st := posC.fold (fun st i =>
    if h : i < st.arrCs.size then
      let c := st.arrCs[i]
      if denseCoveredBy xs c then
        -- covered ⇒ `c.hasVar` ⇒ `c` was not a tombstone, so the live count drops by one
        { st with arrCs := st.arrCs.set i (.const 0), rootCache := st.rootCache.erase i,
                  foldCs := st.foldCs.erase i, liveCs := st.liveCs - 1 }
      else if c.sharesVarIn xs || c.hasConstFoldableNode then
        let c' := denseGroupRewrite xs bits σfn patts c
        let vs := HashedDedup.hashedDedup (hash ·) c'.vars
        { st with
          liveCs := if denseIsZero c' then st.liveCs - 1 else st.liveCs
          arrCs := st.arrCs.set i c'
          rootCache := st.rootCache.erase i
          csIdx := if vs.length ≤ 8 then bucketAdd st.csIdx vs i else st.csIdx
          useCs := bucketAdd st.useCs vs i
          foldCs := if c'.hasConstFoldableNode then st.foldCs.insert i else st.foldCs.erase i }
      else st
    else st) state
  let st := bits.foldl (fun st b =>
    let i := st.arrCs.size
    { st with arrCs := st.arrCs.push (denseBoolConstraint b),
              csIdx := bucketAdd st.csIdx [b] i,
              useCs := bucketAdd st.useCs [b] i }) st
  let posB := (denseCandidates state.useBis xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)
  let st := posB.fold (fun st i =>
    if h : i < st.arrBis.size then
      let bi := st.arrBis[i]
      if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
          || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
        let bi' : BusInteraction (DenseExpr p) :=
          { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
                    payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
        { st with arrBis := st.arrBis.set i bi',
                  useBis := bucketAdd st.useBis
                    (HashedDedup.hashedDedup (hash ·) (denseBIVars bi')) i }
      else st
    else st) st
  { st with varSet := bits.foldl (·.insert ·) st.varSet, dWithin := true }

theorem densePosOk_from0 {lp : Std.HashMap VarId Nat} {lf : Nat} {cs : List (DenseExpr p)} :
    DenseWorkPosOk lp lf cs ↔ DenseWorkPosOkFrom 0 lp lf cs := by
  constructor <;> intro h j c hj <;> simpa using h j c hj

/-- Compute the position bound if it has not been computed yet. Called on the accept path only, so a
    pass application that accepts nothing never walks the variables at all. -/
def denseWorkEnsureBounded (w : DenseReencodeWork p) : DenseReencodeWork p :=
  if w.bounded then w
  else { w with lastPos := denseSeedLp 0 w.cs ∅, lastFold := denseSeedLf 0 w.cs 0, bounded := true }

theorem denseWorkEnsureBounded_view (w : DenseReencodeWork p) :
    denseWorkView (denseWorkEnsureBounded w) = denseWorkView w := by
  unfold denseWorkEnsureBounded denseWorkView; split <;> rfl

theorem denseWorkEnsureBounded_bitSet (w : DenseReencodeWork p) :
    (denseWorkEnsureBounded w).bitSet = w.bitSet := by
  unfold denseWorkEnsureBounded; split <;> rfl

theorem denseWorkEnsureBounded_bools (w : DenseReencodeWork p) :
    (denseWorkEnsureBounded w).bools = w.bools := by
  unfold denseWorkEnsureBounded; split <;> rfl

theorem denseWorkEnsureBounded_posOk {w : DenseReencodeWork p}
    (h : w.bounded = true → DenseWorkPosOk w.lastPos w.lastFold w.cs) :
    DenseWorkPosOk (denseWorkEnsureBounded w).lastPos (denseWorkEnsureBounded w).lastFold
      (denseWorkEnsureBounded w).cs := by
  unfold denseWorkEnsureBounded
  split
  · next hb => exact h hb
  · exact densePosOk_from0.mpr (denseSeed_posOk w.cs 0 ∅ 0)

/-! ### The step, loop and pass over the working system -/

/-- `d`'s item counts for the fresh-name prefix, read off the working system. -/
def denseWorkNameCounts (derivs : DenseDerivations p) (w : DenseReencodeWork p) (nc nb : Nat) :
    Nat × Nat :=
  if derivs.isEmpty then (nc, nb)
  else ((w.cs.filter (fun c => !denseIsZero c)).length + w.bools.length, w.bis.length)

/-- The same counts, served from the threaded state instead of re-walking the whole system on every
    accept (`state.liveCs` mirrors `(w.cs.filter (!denseIsZero ·)).length`, `state.bisN` is
    `w.bis.length`, which no accept changes). Names only need to be fresh, and freshness is checked
    separately, so this is untrusted. -/
def denseWorkNameCountsS (derivs : DenseDerivations p) (w : DenseReencodeWork p)
    (state : DenseReencodeCacheState p) (nc nb : Nat) : Nat × Nat :=
  if derivs.isEmpty then (nc, nb) else (state.liveCs + w.bools.length, state.bisN)

/-- One checked re-encoding step. Mirrors the cached step, with two extra guards — no group variable
    and no freshly minted bit may be a bit minted earlier — which is what keeps the deferred
    booleanity constraints inert for this group (`denseBoolConstraint_inert`). Rejecting a candidate is
    always allowed, so the guards cost behaviour at worst, never soundness. -/
def denseWorkStep (b : DegreeBound) (reg : VarRegistry) (w : DenseReencodeWork p)
    (state : DenseReencodeCacheState p) (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseReencodeWork p × DenseDerivations p × DenseReencodeCacheState p :=
  if xs.all (fun x => reg.isInput x) then
  if xs.any (fun x => w.bitSet.contains x) then (reg, w, [], state) else
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => state.varSet.contains i
      | none => false) then
    (reg, w, [], state)
  else
  match denseBuildReencodeCached reg state.csIdx state.arrCs state.rootCache xs freshBase with
  | (reg1, none, rootCache) => (reg1, w, [], { state with rootCache })
  | (reg1, some (bits, hm), rootCache) =>
    let state := { state with rootCache }
    if bits.any (fun bb => w.bitSet.contains bb) then (reg1, w, [], state) else
    if denseDegPreRejectIdx b state.useCs state.useBis state.arrBis state.arrCs xs bits hm then
      (reg1, w, [], state)
    else
    if xs.all (fun x => state.varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun bb => decide ((reg1.resolve bb).powdrId? = none)) then
    if denseCheckReencode { algebraicConstraints := w.cs, busInteractions := w.bis } xs bits hm then
      let ro := denseWorkOut b (denseWorkEnsureBounded w) xs bits hm
      if (if state.dWithin then ro.2 else (denseWorkView ro.1).withinDegreeB b) then
        (reg1, ro.1,
         bits.map (fun bb => (bb, denseBitCM (denseAssignments (denseBitBox bits)) xs hm bb)),
         denseReencodeStateUpdate state xs bits hm)
      else (reg1, w, [], state)
    else (reg1, w, [], state)
    else (reg1, w, [], state)
    else (reg1, w, [], state)
    else (reg1, w, [], state)
  else (reg, w, [], state)

def denseWorkLoop (b : DegreeBound) :
    List (List VarId) → Nat → VarRegistry → DenseReencodeWork p →
      DenseReencodeCacheState p → Nat → Nat →
      VarRegistry × DenseReencodeWork p × DenseDerivations p
  | [], _, reg, w, _, _, _ => (reg, w, [])
  | xs :: rest, idx, reg, w, state, nc, nb =>
    let (reg1, w1, derivs1, state1) := denseWorkStep b reg w state xs s!"rnc{nc}_{nb}_{idx}"
    let (nc1, nb1) := denseWorkNameCountsS derivs1 w1 state1 nc nb
    let (reg2, w2, derivs2) := denseWorkLoop b rest (idx + 1) reg1 w1 state1 nc1 nb1
    (reg2, w2, derivs1 ++ derivs2)

def denseWorkSeed (d : DenseConstraintSystem p) : DenseReencodeWork p :=
  { cs := d.algebraicConstraints, bis := d.busInteractions, bools := [], bitSet := ∅,
    lastPos := ∅, lastFold := 0, bounded := false }

/-- Witness re-encoding. When a group of variables `xs` is so constrained that only a few value
    combinations survive, mint `Nat.clog 2 #survivors` fresh boolean bits, rewrite each group
    variable as an interpolation polynomial over the bits, drop the now-covered constraints, and add
    booleanity constraints — e.g. a group with 3 surviving combinations becomes 2 bits, cutting the
    variable count. The transform is shaped for `DenseVerifiedPassW.ofExtending`; `facts` is unused
    (reencode is fact-free). -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list, shared between `svSet` and `targets`.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Sort by the resolved `Variable`'s order: `denseWorkLoop` below is a greedy,
        -- order-sensitive accept/reject sequence, so the group order determines the outcome.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let r := denseWorkLoop b targets 0 reg (denseWorkSeed d)
      { csIdx := denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints
        arrCs := d.algebraicConstraints.toArray
        rootCache := ∅
        varSet := Std.HashSet.ofList d.occ
        useCs := denseCovBuild DenseExpr.vars d.algebraicConstraints
        useBis := denseCovBuild denseBIVars d.busInteractions
        arrBis := d.busInteractions.toArray
        foldCs := d.algebraicConstraints.zipIdx.foldl
          (fun s ci => if ci.1.hasConstFoldableNode then s.insert ci.2 else s) ∅
        liveCs := (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length
        bisN := d.busInteractions.length
        dWithin := false }
      (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length d.busInteractions.length
    (r.1, denseWorkView r.2.1, r.2.2)
  else (reg, d, [])

end ApcOptimizer.Dense
