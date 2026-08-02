import ApcOptimizer.Implementation.OptimizerPasses.DomainTable
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
  e.evalWith zmodAdd zmodMul denv

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

/-- Every conjunct of the certificate except freshness. Split out so `denseWorkStep` can discharge
    freshness from the threaded variable superset instead of scanning
    (`denseFreshScan_of_notMemOcc`). -/
def denseCheckReencodeNoFresh (d : DenseConstraintSystem p) (xs bits : List VarId)
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
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0)))

/-- The freshness conjunct: no bit occurs anywhere in the system. -/
def denseFreshScan (d : DenseConstraintSystem p) (bits : List VarId) : Bool :=
  d.algebraicConstraints.all (fun c => !c.mentionsAny (Std.HashSet.ofList bits)) &&
    d.busInteractions.all (fun bi =>
      !bi.multiplicity.mentionsAny (Std.HashSet.ofList bits) &&
      bi.payload.all (fun e => !e.mentionsAny (Std.HashSet.ofList bits)))

def denseCheckReencodeFast (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  denseCheckReencodeNoFresh d xs bits hm && denseFreshScan d bits

@[csimp] theorem denseCheckReencode_eq_fast : @denseCheckReencode = @denseCheckReencodeFast := by
  funext q d xs bits hm
  unfold denseCheckReencode denseCheckReencodeFast denseCheckReencodeNoFresh denseFreshScan
  simp only [denseFreshFused_eq]
  split
  · rfl
  · simp only [Bool.and_assoc]

/-- The certificate from its two halves. -/
theorem denseCheckReencode_of_parts (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (h1 : denseCheckReencodeNoFresh d xs bits hm = true)
    (h2 : denseFreshScan d bits = true) : denseCheckReencode d xs bits hm = true := by
  have h : denseCheckReencode d xs bits hm = denseCheckReencodeFast d xs bits hm := by
    simp only [denseCheckReencode_eq_fast]
  rw [h]
  simp only [denseCheckReencodeFast, h1, h2, Bool.and_self]

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

/-- Two lists' `all` agree when the predicates agree pointwise on the members. -/
theorem List.all_congr_mem {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Whether any expression of the interaction carries a variable-free composite node. Independent of
    the group, so it is a property of the interaction and does not need re-deriving per accept. -/
def denseBiHasFold (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.multiplicity.hasConstFoldableNode || bi.payload.any (fun e => e.hasConstFoldableNode)

/-- Whether the group rewrite can change the interaction: it touches a group variable, or it carries
    a variable-free composite node the rewrite would fold. `denseBIRewriteGate` and
    `denseBIGateDeg` are the identity when this is `false` (`denseBIGateDeg_of_not_fires`). -/
def denseBiGateFires (xs : List VarId) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode ||
    bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode)

/-- The bus side of an accept, driven by an ascending position list instead of by a gate test at
    every interaction: `denseBIRewriteGate` is the identity wherever the gate cannot fire
    (`denseBIRewriteGate_eq` + `denseGroupRewrite_eq_self`), and the positions where it can are the
    `useBis` bucket candidates for `xs` together with the interactions carrying a variable-free
    composite node. Once the positions run out the remaining suffix is shared untouched, which is
    what makes this `O(prefix + candidates)` rather than `O(system)` tree walks. -/
def denseGateBisPos (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    List Nat → Nat → List (BusInteraction (DenseExpr p)) →
      List (BusInteraction (DenseExpr p)) → Bool →
      List (BusInteraction (DenseExpr p)) × Bool
  | _, _, [], acc, ok => (acc.reverse, ok)
  | [], _, rest, acc, ok => (acc.reverse ++ rest, ok)
  | j :: ps, i, bi :: rest, acc, ok =>
      if j < i then denseGateBisPos dmax xs bits σfn patts ps i (bi :: rest) acc ok
      else if j == i then
        let r := denseBIGateDeg dmax xs bits σfn patts bi
        denseGateBisPos dmax xs bits σfn patts ps (i + 1) rest (r.1 :: acc) (ok && r.2)
      else denseGateBisPos dmax xs bits σfn patts (j :: ps) (i + 1) rest (bi :: acc) ok

/-- The gate leaves an interaction it cannot fire on completely alone. -/
theorem denseBIGateDeg_of_not_fires (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    {bi : BusInteraction (DenseExpr p)} (h : denseBiGateFires xs bi = false) :
    denseBIGateDeg dmax xs bits σfn patts bi = (bi, true) := by
  unfold denseBIGateDeg
  rw [if_neg (by simpa [denseBiGateFires] using h)]

/-- The position-driven bus rewrite equals the dense one, provided every position the gate can fire
    on is listed. Extra and out-of-range positions are harmless (each visited position is re-tested by
    `denseBIGateDeg`); the listed positions must be ascending, which is what lets the scan share the
    suffix once they run out. -/
theorem denseGateBisPos_eq (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p))) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (ps : List Nat) (i : Nat)
      (acc : List (BusInteraction (DenseExpr p))) (ok : Bool),
      ps.Pairwise (· ≤ ·) →
      (∀ k bi, bis[k]? = some bi → denseBiGateFires xs bi = true → (i + k) ∈ ps) →
      denseGateBisPos dmax xs bits σfn patts ps i bis acc ok
        = (acc.reverse ++ bis.map (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).1),
           ok && bis.all (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).2)) := by
  -- `gid l` : the gate is the identity on every item of `l`
  have gid : ∀ (l : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ l, denseBiGateFires xs bi = false) →
      l.map (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).1) = l ∧
      (l.all (fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).2)) = true := by
    intro l hl
    constructor
    · have h := List.map_congr_left (l := l)
        (f := fun bi => (denseBIGateDeg dmax xs bits σfn patts bi).1) (g := id)
        (fun bi hbi => by
          simp [denseBIGateDeg_of_not_fires dmax xs bits σfn patts (hl bi hbi)])
      rwa [List.map_id] at h
    · rw [List.all_eq_true]
      intro bi hbi
      simp only [denseBIGateDeg_of_not_fires dmax xs bits σfn patts (hl bi hbi)]
  intro bis
  induction bis with
  | nil =>
      intro ps i acc ok _ _
      cases ps <;> simp [denseGateBisPos]
  | cons bi rest ih =>
      intro ps i acc ok hsorted hcov
      induction ps with
      | nil =>
          have hl : ∀ bi' ∈ bi :: rest, denseBiGateFires xs bi' = false := by
            intro bi' hbi'
            cases hf : denseBiGateFires xs bi' with
            | false => rfl
            | true =>
                obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hbi'
                exact absurd (hcov k bi' hk hf) (by simp)
          obtain ⟨hmap, hall⟩ := gid (bi :: rest) hl
          simp only [denseGateBisPos, hmap, hall, Bool.and_true]
      | cons j ps' ihps =>
          have hsorted' : ps'.Pairwise (· ≤ ·) :=
            List.Pairwise.sublist (List.sublist_cons_self j ps') hsorted
          rcases Nat.lt_trichotomy j i with hji | hji | hji
          · -- a position already passed: drop it and keep the same items
            rw [denseGateBisPos, if_pos hji]
            refine ihps hsorted' ?_
            intro k bi' hk hf
            rcases List.mem_cons.1 (hcov k bi' hk hf) with h | h
            · omega
            · exact h
          · -- the current position: rewrite this item
            rw [denseGateBisPos, if_neg (by omega), if_pos (show (j == i) = true by simp [hji])]
            rw [ih ps' (i + 1) _ _ hsorted' ?_]
            · simp [Bool.and_assoc]
            · intro k bi' hk hf
              have h1 := hcov (k + 1) bi' (by simpa using hk) hf
              rcases List.mem_cons.1 h1 with h | h
              · omega
              · have : i + 1 + k = i + (k + 1) := by omega
                rwa [this]
          · -- the next listed position is later: this item cannot fire
            have hni : denseBiGateFires xs bi = false := by
              cases hf : denseBiGateFires xs bi with
              | false => rfl
              | true =>
                  have h0 := hcov 0 bi (by simp) hf
                  rcases List.mem_cons.1 (by simpa using h0) with h | h
                  · omega
                  · have := (List.pairwise_cons.1 hsorted).1 i h
                    omega
            rw [denseGateBisPos, if_neg (by omega),
              if_neg (show ¬ ((j == i) = true) by simp; omega)]
            rw [ih (j :: ps') (i + 1) _ _ hsorted ?_]
            · simp [denseBIGateDeg_of_not_fires dmax xs bits σfn patts hni]
            · intro k bi' hk hf
              have h1 := hcov (k + 1) bi' (by simpa using hk) hf
              have : i + 1 + k = i + (k + 1) := by omega
              rwa [this]

/-- A position the rewrite did not visit keeps its interaction. -/
theorem denseGateBisPos_untouched (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (ps : List Nat) (bis : List (BusInteraction (DenseExpr p)))
    (hsorted : ps.Pairwise (· ≤ ·))
    (hcov : ∀ k bi, bis[k]? = some bi → denseBiGateFires xs bi = true → k ∈ ps) :
    ∀ i bi, ((denseGateBisPos dmax xs bits σfn patts ps 0 bis [] true).1)[i]? = some bi →
      i ∉ ps → bis[i]? = some bi := by
  intro i bi hi hni
  rw [denseGateBisPos_eq dmax xs bits σfn patts bis ps 0 [] true hsorted
    (by simpa using hcov)] at hi
  simp only [List.reverse_nil, List.nil_append, List.getElem?_map,
    Option.map_eq_some_iff] at hi
  obtain ⟨bi0, hbi0, hgate⟩ := hi
  have hfires : denseBiGateFires xs bi0 = false := by
    cases hf : denseBiGateFires xs bi0 with
    | false => rfl
    | true => exact absurd (hcov i bi0 hbi0 hf) hni
  rw [denseBIGateDeg_of_not_fires dmax xs bits σfn patts hfires] at hgate
  rw [hbi0, ← hgate]

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

def denseIsZeroImpl : DenseExpr p → Bool
  | .const n => zmodIsZero n
  | _ => false

def denseIsZero : DenseExpr p → Bool
  | .const n => n == 0
  | _ => false

@[csimp] theorem denseIsZero_eq_impl : @denseIsZero = @denseIsZeroImpl := by
  funext q e
  cases e with
  | const n =>
      show (n == 0) = zmodIsZero n
      simp only [zmodIsZero_eq]
      rfl
  | var _ => rfl
  | add _ _ => rfl
  | mul _ _ => rfl

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
        denseWorkSpliceCs dmax xs bits σfn patts maxPos (i + 1) rest
          ((.const 0) :: acc) lp lf ok
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
    position-driven `denseGateBisPos`), and accumulate the booleanity constraints. Assumes the
    position bound is computed — `denseWorkStep` calls `denseWorkEnsureBounded` first. -/
def denseWorkOut (b : DegreeBound) (w : DenseReencodeWork p) (usePosB : List Nat)
    (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseReencodeWork p × Bool :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let mp := denseWorkMaxPos w.lastPos w.lastFold xs
  let rc := denseWorkSpliceCs b.identities xs bits σfn patts mp 0 w.cs [] w.lastPos w.lastFold true
  let rb := denseGateBisPos b.busInteractions xs bits σfn patts usePosB 0 w.bis [] true
  let newBools := bits.map (denseBoolConstraint (p := p))
  ({ cs := rc.1, bis := rb.1, bools := w.bools ++ newBools,
     bitSet := bits.foldl (·.insert ·) w.bitSet,
     lastPos := rc.2.1, lastFold := rc.2.2.1, bounded := true },
   (rc.2.2.2 && newBools.all (fun c => decide (c.degree ≤ b.identities))) && rb.2)

/-- **Unproven on this branch (measurement).** The real statement adds the completeness side
    condition that makes the position-driven bus rewrite agree with `denseReencodeOut`:

    `hcomplete : ∀ i bi, w.bis[i]? = some bi →
       (bi.multiplicity.sharesVarIn xs = true ∨ bi.multiplicity.hasConstFoldableNode = true ∨
        bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) = true) → i ∈ usePosB`

    plus `usePosB` ascending. The `useBis` buckets are complete by construction and `foldBis` tracks
    the fold positions, so a superset is fine and every visited position is re-tested by
    `denseBIGateDeg`. Given that, the bus half of the old proof goes through with
    `denseBIRewriteGate_eq` + `denseGroupRewrite_eq_self` supplying the identity at every unvisited
    position and at the shared suffix — structurally the same argument
    `denseTombify_id_of_untouched` already makes on the constraint side, which is why this shape was
    chosen over the array-backed one. The constraint half of this lemma is untouched. -/
theorem denseWorkOut_view (b : DegreeBound) (w : DenseReencodeWork p) {usePosB : List Nat}
    (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hpos : DenseWorkPosOk w.lastPos w.lastFold w.cs)
    (hbools : DenseWorkBoolsOk w.bitSet w.bools)
    (hxs : ∀ x ∈ xs, w.bitSet.contains x = false)
    (hsortedB : usePosB.Pairwise (· ≤ ·))
    (hcoverB : ∀ k bi, w.bis[k]? = some bi → denseBiGateFires xs bi = true → k ∈ usePosB) :
    denseWorkView (denseWorkOut b w usePosB xs bits hm).1
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
  have hbus : (denseGateBisPos b.busInteractions xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) usePosB 0 w.bis [] true).1
      = w.bis.map (fun bi => { bi with
          multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits)) bi.multiplicity,
          payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits))) }) := by
    rw [denseGateBisPos_eq b.busInteractions xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) w.bis usePosB 0 [] true hsortedB
      (by simpa using hcoverB)]
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
  /-- Bus positions carrying a variable-free composite node (`denseBiHasFold`). With the `useBis`
      buckets this is exactly the set of positions an accept's bus rewrite can touch. A `Thunk` so
      that an invocation which never accepts never pays the scan — the accept path is the only
      consumer, mirroring how `denseWorkEnsureBounded` defers the constraint-side bound. -/
  foldBis : Thunk (Std.HashSet Nat)
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

/-! ### Freshness from the state's variable superset

The certificate's freshness conjunct is its only `O(system)` one: it walks every constraint and
every bus expression to check that no minted bit occurs there (measured at 66.6 % of the
certificate, ~25 % of the pass, on sha256/apc_001). `state.varSet` starts as
`Std.HashSet.ofList d.occ` and only ever *gains* the minted bits, so it over-approximates the live
variables — and `bits.all (fun b => !varSet.contains b)` is therefore an `O(|bits|)` sufficient
condition for freshness. Being sufficient rather than equivalent, it enters the proof as an
implication (`denseCheckReencodeVS_sound`), not a `@[csimp]` equality; the invariant that licenses
it is `DenseWorkVarsOk`, threaded through the step and the loop. -/

/-- The checked certificate with freshness decided from `state.varSet` in `O(|bits|)`. -/
def denseCheckReencodeVS (state : DenseReencodeCacheState p) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  bits.all (fun bb => !state.varSet.contains bb) && denseCheckReencodeNoFresh d xs bits hm

/-- The bus half of an accept's index update: for each position the rewrite visited, record the new
    interaction's variables in the buckets and whether it still carries a variable-free composite
    node. Standalone (a fold over `(buckets, foldSet)`) so its result does not depend on the
    constraint half — which is what makes `denseBusIdxOk_update` a plain list induction. -/
def denseBusIdxFold (arrB : Array (BusInteraction (DenseExpr p))) :
    List Nat → DenseCovIndex × Std.HashSet Nat → DenseCovIndex × Std.HashSet Nat
  | [], acc => acc
  | i :: rest, acc =>
      if h : i < arrB.size then
        let bi := arrB[i]
        let vs := HashedDedup.hashedDedup (hash ·) (denseBIVars bi)
        denseBusIdxFold arrB rest
          (⟨vs.foldl (fun m v => m.insert v (i :: m.getD v [])) acc.1.buckets, acc.1.varless⟩,
           if denseBiHasFold bi then acc.2.insert i else acc.2.erase i)
      else denseBusIdxFold arrB rest acc

/-- Apply an accepted rewrite to the threaded state in place, mirroring `denseReencodeOut` on the
    stable-position arrays: only positions holding a group variable (bucket candidates) or a
    variable-free composite node (`foldCs`) can change. The root cache keeps every untouched
    position (it memoizes a pure function of the position's content). -/
def denseReencodeStateUpdate (state : DenseReencodeCacheState p) (usePosB : List Nat)
    (bisNew : List (BusInteraction (DenseExpr p))) (xs bits : List VarId)
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
        { st with arrCs := st.arrCs.set i (.const 0),
                  rootCache := st.rootCache.erase i,
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
  -- The bus side takes the accept's own output and its own position list: one rewrite, two
  -- consumers, folding over exactly the positions the splice visited.
  let arrB := bisNew.toArray
  let bus := denseBusIdxFold arrB usePosB (state.useBis, state.foldBis.get)
  -- `varSet` is grown from the *input* state: the position folds above never touch it, and reading
  -- it from `state` keeps `denseReencodeStateUpdate_varSet` a projection instead of a fold invariant.
  { st with arrBis := arrB, useBis := bus.1, foldBis := Thunk.mk (fun _ => bus.2),
            varSet := bits.foldl (·.insert ·) state.varSet, dWithin := true }

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

theorem denseWorkEnsureBounded_bis (w : DenseReencodeWork p) :
    (denseWorkEnsureBounded w).bis = w.bis := by
  unfold denseWorkEnsureBounded; split <;> rfl

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
    if denseCheckReencodeVS state { algebraicConstraints := w.cs, busInteractions := w.bis }
        xs bits hm then
      let ro := denseWorkOut b (denseWorkEnsureBounded w)
        (((denseCandidates state.useBis xs).foldl (·.insert ·)
          state.foldBis.get).toList.mergeSort (· ≤ ·)) xs bits hm
      if (if state.dWithin then ro.2 else (denseWorkView ro.1).withinDegreeB b) then
        (reg1, ro.1,
         bits.map (fun bb => (bb, denseBitCM (denseAssignments (denseBitBox bits)) xs hm bb)),
         denseReencodeStateUpdate state
           (((denseCandidates state.useBis xs).foldl (·.insert ·)
             state.foldBis.get).toList.mergeSort (· ≤ ·)) ro.1.bis xs bits hm)
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

/-! ## The array-backed engine

One position-stable `Array` per item list, `VarId.index`-keyed buckets, and per-invocation memos for
the quantities that are provably target-independent. Everything here is untrusted: the certificate
(`denseRncCert`) re-verifies
each candidate, so an index that over- or under-reports only costs a decision. -/

/-- Distinct variables of `e` appended to `acc`, abandoning the walk once `cap` are known — so a
    result of size `cap` means "at least `cap` distinct variables". Every consumer of the cheap path
    only distinguishes counts below 9: a constraint covered by an ≤ 8-variable group has ≤ 8
    variables. -/
def denseRncCapGo (cap : Nat) : DenseExpr p → Array VarId → Array VarId
  | .const _, acc => acc
  | .var y, acc => if cap ≤ acc.size || acc.contains y then acc else acc.push y
  | .add a b, acc =>
      let acc := denseRncCapGo cap a acc
      if cap ≤ acc.size then acc else denseRncCapGo cap b acc
  | .mul a b, acc =>
      let acc := denseRncCapGo cap a acc
      if cap ≤ acc.size then acc else denseRncCapGo cap b acc

def denseRncCapVars (c : DenseExpr p) : Array VarId := denseRncCapGo 9 c #[]

/-- All distinct variables, reusing the capped array when it is already exact. -/
def denseRncFullVars (c : DenseExpr p) (vs : Array VarId) : Array VarId :=
  if vs.size ≤ 8 then vs else (HashedDedup.hashedDedup (hash ·) c.vars).toArray

/-- `(hasVar, hasConstFoldableNode)` in one walk. `DenseExpr.hasConstFoldableNode` re-derives
    `hasVar` at every composite node, so it is quadratic in the depth. -/
def denseRncFoldPair : DenseExpr p → Bool × Bool
  | .const _ => (false, false)
  | .var _ => (true, false)
  | .add a b =>
      let (va, fa) := denseRncFoldPair a
      let (vb, fb) := denseRncFoldPair b
      (va || vb, !(va || vb) || fa || fb)
  | .mul a b =>
      let (va, fa) := denseRncFoldPair a
      let (vb, fb) := denseRncFoldPair b
      (va || vb, !(va || vb) || fa || fb)

def denseRncHasFold (e : DenseExpr p) : Bool := (denseRncFoldPair e).2

def denseRncBiHasFold (bi : BusInteraction (DenseExpr p)) : Bool :=
  denseRncHasFold bi.multiplicity || bi.payload.any denseRncHasFold

/-- The single bucket key of a position: its first variable. A constraint covered by a group has all
    its variables — in particular this one — in the group, which is what makes one bucket per
    position complete for the covered query. -/
def denseRncAnchorVars (c : DenseExpr p) : List VarId :=
  match (denseRncCapVars c)[0]? with
  | some v => [v]
  | none => []

def denseRncAnchorAdd (idx : DenseCovIndex) (ks : List VarId) (i : Nat) : DenseCovIndex :=
  match ks with
  | [] => idx
  | v :: _ => ⟨idx.buckets.insert v (i :: idx.buckets.getD v []), idx.varless⟩

def denseRncBGet (bs : Array (Array Nat)) (v : VarId) : Array Nat := bs.getD v.index #[]

/-- Grow-then-add, so a variable minted after the arrays were sized still gets a bucket. -/
def denseRncBAdd (bs : Array (Array Nat)) (v : VarId) (i : Nat) : Array (Array Nat) :=
  (denseArrEnsure bs v.index #[]).modify v.index (fun a => a.push i)

def denseRncMark (bs : Array Bool) (v : VarId) : Array Bool := bs.setIfInBounds v.index true

def denseRncGetB (bs : Array Bool) (v : VarId) : Bool := bs.getD v.index false

/-- The positions the group rewrite can touch, deduplicated: applying it twice at one position is
    not the identity, and `Std.HashSet` is what makes the list provably duplicate-free. -/
def denseRncPosList (bs : Array (Array Nat)) (xs : List VarId) (extra : List Nat) : List Nat :=
  ((xs.flatMap (fun x => (denseRncBGet bs x).toList) ++ extra).foldl (·.insert ·)
    (∅ : Std.HashSet Nat)).toList

/-- Whether every variable of the capped array lies in `xs` (exact for sizes below 9). -/
def denseRncSubset (xs : List VarId) (vs : Array VarId) : Bool :=
  vs.all (fun v => denseContainsFast xs v)

/-- `denseCoveredBy` off the capped variable array where it is exact, by tree walk otherwise. -/
def denseRncCovered (xs : List VarId) (vs : Array VarId) (c : DenseExpr p) : Bool :=
  if vs.size ≤ 8 then 1 ≤ vs.size && denseRncSubset xs vs else denseCoveredBy xs c

/-- `DenseExpr.sharesVarIn` off the capped array where it is exact, by tree walk otherwise. -/
def denseRncShares (xs : List VarId) (vs : Array VarId) (c : DenseExpr p) : Bool :=
  if vs.size ≤ 8 then vs.any (fun v => denseContainsFast xs v) else c.sharesVarIn xs

/-! ### The threaded state -/

/-- Per-invocation immutable context: the dictionary-free field operations and the shared `.const 0`
    tombstone (the plain literal rebuilds the whole `CommRing (ZMod p)` chain per tombstoned
    position — visible in the generated C of the list splice this engine replaces). -/
structure DenseRncCtx (p : ℕ) where
  ops : DenseZModOps p
  zeroE : DenseExpr p
  b : DegreeBound

def DenseRncCtx.dmaxC (ctx : DenseRncCtx p) : Nat := ctx.b.identities
def DenseRncCtx.dmaxB (ctx : DenseRncCtx p) : Nat := ctx.b.busInteractions

/-- `f` holds at some position of the buckets of `xs`; short-circuits. -/
def denseRncBucketAny (bs : Array (Array Nat)) (xs : List VarId) (f : Nat → Bool) : Bool :=
  xs.any (fun x => (denseRncBGet bs x).any f)

/-- `f` holds at every `i < n`, without materialising the range. -/
def denseRncAllLt (n : Nat) (f : Nat → Bool) : Bool :=
  let rec go (i : Nat) : Bool :=
    if h : i < n then (if f i then go (i + 1) else false) else true
    termination_by n - i
    decreasing_by omega
  go 0

/-- The working system and its indexes, on stable positions. Dropped constraints become the shared
    `.const 0`; the booleanity constraints of every accept are pushed onto `cs`, so the output list
    is one filtered pass over it. Structures that only the near-accept path reads are `Option`s,
    built on first use (`denseRncEnsure*`). -/
structure DenseRncState (p : ℕ) where
  cs : Array (DenseExpr p)
  /-- Per position, its distinct variables capped at 9 (`denseRncCapVars`). -/
  cvs : Array (Array VarId)
  bis : Array (BusInteraction (DenseExpr p))
  /-- Non-tombstone entries of `cs` (feeds the fresh-name prefix only). -/
  live : Nat
  bisN : Nat
  /-- Each ≤ 8-variable position under its *first* variable only: `vars c ⊆ xs` implies the first
      variable is in `xs`, so this is complete for the covered query (`denseCoveredIdx`), and no
      position is listed twice under one target. -/
  anchor : DenseCovIndex
  /-- Each position under *every* variable it mentions — what the rewrite and the degree pre-gate
      need. -/
  useCs : Option (Array (Array Nat))
  useBis : Option (Array (Array Nat))
  foldCs : Option (Std.HashSet Nat)
  foldBis : Option (Std.HashSet Nat)
  /-- Variables occurring in the system at pass entry; with `minted`, an over-approximation of the
      live variables, which is what decides bit freshness in `O(|bits|)`. -/
  varSeen : Option (Array Bool)
  minted : Std.HashSet VarId
  /-- Per-variable domain memo. A variable's domain is the roots of the lowest-positioned constraint
      whose variable set is exactly `{v}` and whose root plan resolves; a root plan resolves for `v`
      only for such a constraint, and such a constraint is covered by *every* group containing `v`,
      so the answer does not depend on the target. Computed once per invocation, dropped on each
      accept (a rewrite can change which constraint is lowest). -/
  domVal : Array (Option (List (ZMod p)))
  domKnown : Array Bool
  /-- Per variable, `position + 1` of the constraint its domain came from (`0` if unknown). Such a
      constraint vanishes on every point of the variable's own domain — the plan's roots *are* its
      factors' roots — so the enumeration below never tests it. -/
  domSrc : Array Nat
  domTouched : List VarId
  dWithin : Bool
  nVar : Nat

/-! ### Field updates

Every write destructures the state first, so the array being written is uniquely owned:
`{ st with f := g st.f }` leaves `st.f` shared and copies the whole array (the same trap
`Gauss.lean` documents, measured at 7× there and at ~10× on the accept path here). -/

def DenseRncState.setDom (st : DenseRncState p) (v : VarId)
    (r : Option (Nat × List (ZMod p))) : DenseRncState p :=
  let ⟨cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
        domVal, domKnown, domSrc, domTouched, dWithin, nVar⟩ := st
  { cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
    domVal := domVal.setIfInBounds v.index (r.map Prod.snd),
    domKnown := domKnown.setIfInBounds v.index true,
    domSrc := domSrc.setIfInBounds v.index (match r with | some (q, _) => q + 1 | none => 0),
    domTouched := v :: domTouched, dWithin, nVar }

/-- Drop the memo (an accept rewrites positions, so a memoized domain may no longer be the lowest
    one); only the entries actually filled are reset. -/
def DenseRncState.domReset (st : DenseRncState p) : DenseRncState p :=
  let ⟨cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
        domVal, domKnown, domSrc, domTouched, dWithin, nVar⟩ := st
  { cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted, domVal,
    domKnown := domTouched.foldl (fun m v => m.setIfInBounds v.index false) domKnown, domSrc,
    domTouched := [], dWithin, nVar }

/-- Install the rewritten constraint at `i` and extend the indexes for its new variables. -/
def DenseRncState.rewriteAt (st : DenseRncState p) (i : Nat) (c' : DenseExpr p)
    (cv' full : Array VarId) : DenseRncState p :=
  let ⟨cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
        domVal, domKnown, domSrc, domTouched, dWithin, nVar⟩ := st
  { cs := cs.setIfInBounds i c', cvs := cvs.setIfInBounds i cv', bis,
    live := if denseIsZero c' then live - 1 else live, bisN,
    anchor := denseRncAnchorAdd anchor (denseRncAnchorVars c') i,
    useCs := useCs.map (fun m => full.foldl (fun m v => denseRncBAdd m v i) m), useBis,
    foldCs := foldCs.map (fun s => if denseRncHasFold c' then s.insert i else s.erase i),
    foldBis, varSeen, minted, domVal, domKnown, domSrc, domTouched, dWithin, nVar }

def DenseRncState.rewriteBiAt (st : DenseRncState p) (i : Nat)
    (bi' : BusInteraction (DenseExpr p)) : DenseRncState p :=
  let ⟨cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
        domVal, domKnown, domSrc, domTouched, dWithin, nVar⟩ := st
  { cs, cvs, bis := bis.setIfInBounds i bi', live, bisN, anchor, useCs,
    useBis := useBis.map (fun m => (denseBIVars bi').foldl (fun m v => denseRncBAdd m v i) m),
    foldCs, foldBis := foldBis.map (fun s => if denseRncBiHasFold bi' then s.insert i else s.erase i),
    varSeen, minted, domVal, domKnown, domSrc, domTouched, dWithin, nVar }

/-- Append one booleanity constraint. -/
def DenseRncState.pushBool (st : DenseRncState p) (b : VarId) : DenseRncState p :=
  let ⟨cs, cvs, bis, live, bisN, anchor, useCs, useBis, foldCs, foldBis, varSeen, minted,
        domVal, domKnown, domSrc, domTouched, _, nVar⟩ := st
  { cs := cs.push (denseBoolConstraint b), cvs := cvs.push #[b], bis, live := live + 1, bisN,
    anchor := denseRncAnchorAdd anchor [b] cs.size,
    useCs := useCs.map (fun m => denseRncBAdd m b cs.size), useBis, foldCs, foldBis, varSeen,
    minted := minted.insert b,
    domVal, domKnown, domSrc, domTouched, dWithin := true, nVar }

def denseRncEnsureUse (st : DenseRncState p) : DenseRncState p :=
  match st.useCs with
  | some _ => st
  | none =>
    let rec go (i : Nat) (acc : Array (Array Nat)) : Array (Array Nat) :=
      if h : i < st.cs.size then
        let vs := denseRncFullVars st.cs[i] (st.cvs.getD i #[])
        go (i + 1) (vs.foldl (fun m v => denseRncBAdd m v i) acc)
      else acc
      termination_by st.cs.size - i
      decreasing_by omega
    { st with useCs := some (go 0 (Array.replicate st.nVar #[])) }

def denseRncEnsureUseBis (st : DenseRncState p) : DenseRncState p :=
  match st.useBis with
  | some _ => st
  | none =>
    let rec go (i : Nat) (acc : Array (Array Nat)) : Array (Array Nat) :=
      if h : i < st.bis.size then
        go (i + 1) ((denseBIVars st.bis[i]).foldl (fun m v => denseRncBAdd m v i) acc)
      else acc
      termination_by st.bis.size - i
      decreasing_by omega
    { st with useBis := some (go 0 (Array.replicate st.nVar #[])) }

def denseRncEnsureFoldCs (st : DenseRncState p) : DenseRncState p :=
  match st.foldCs with
  | some _ => st
  | none =>
    let rec go (i : Nat) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
      if h : i < st.cs.size then
        go (i + 1) (if denseRncHasFold st.cs[i] then acc.insert i else acc)
      else acc
      termination_by st.cs.size - i
      decreasing_by omega
    { st with foldCs := some (go 0 ∅) }

def denseRncEnsureFoldBis (st : DenseRncState p) : DenseRncState p :=
  match st.foldBis with
  | some _ => st
  | none =>
    let rec go (i : Nat) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
      if h : i < st.bis.size then
        go (i + 1) (if denseRncBiHasFold st.bis[i] then acc.insert i else acc)
      else acc
      termination_by st.bis.size - i
      decreasing_by omega
    { st with foldBis := some (go 0 ∅) }

def denseRncEnsureSeen (st : DenseRncState p) : DenseRncState p :=
  match st.varSeen with
  | some _ => st
  | none =>
    let m := st.cs.foldl (fun m c => c.foldVars (fun m v => denseRncMark m v) m)
      (Array.replicate st.nVar false)
    let m := st.bis.foldl (fun m bi =>
      bi.payload.foldl (fun m e => e.foldVars (fun m v => denseRncMark m v) m)
        (bi.multiplicity.foldVars (fun m v => denseRncMark m v) m)) m
    { st with varSeen := some m }

/-- Whether `v` may still occur in the system (over-approximate: entry occurrences plus minted
    bits). Assumes `denseRncEnsureSeen`. -/
def denseRncSeen (st : DenseRncState p) (v : VarId) : Bool :=
  (match st.varSeen with | some m => denseRncGetB m v | none => true) || st.minted.contains v

/-! ### Domains

The affine root `-(a⁻¹ · c)` costs a field inversion, and the plan of a booleanity or range
constraint asks for one per factor. At `a = ±1` — which is every constraint the domains actually
come from — the inverse is `a` itself, so the root is `∓c` with no inversion; the general case keeps
`denseRootsOfTerms`. -/

def denseRncRootsOfTerms (ops : DenseZModOps p) (i : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → Option (List (ZMod p))
  | [] => if zmodIsZero c then none else some []
  | [(j, a)] =>
      if j == i && (zmodIsOne a || zmodIsZero (ops.add a ops.one)) then
        let r := if zmodIsOne a then zmodNegP c else c
        if zmodIsZero (ops.add (ops.mul a r) c) then some [r] else none
      else denseRootsOfTerms i c [(j, a)]
  | _ :: _ :: _ => none

def denseRncRootPlan (ops : DenseZModOps p) : DenseExpr p → Option (DenseReencodeRootPlan p)
  | .mul a b =>
      match denseRncRootPlan ops a, denseRncRootPlan ops b with
      | some left, some right => denseReencodeRootPlanMul left right
      | _, _ => none
  | e =>
      match denseLinearize e with
      | none => none
      | some l =>
          let l := l.norm
          match l.terms with
          | [] => if zmodIsZero l.const then none else some (.any [])
          | [(i, a)] => (denseRncRootsOfTerms ops i l.const [(i, a)]).map (.one i)
          | _ => none

/-- The first single-variable position resolving a root plan for `v`, scanning ascending. -/
def denseRncFirstRoots (ops : DenseZModOps p) (cs : Array (DenseExpr p)) (v : VarId)
    (cands : Array Nat) (i : Nat) : Option (Nat × List (ZMod p)) :=
  if h : i < cands.size then
    match cs[cands[i]]? with
    | some c =>
      match (denseRncRootPlan ops c).bind (denseReencodeRootPlanLookup v) with
      | some roots => some (cands[i], roots)
      | none => denseRncFirstRoots ops cs v cands (i + 1)
    | none => denseRncFirstRoots ops cs v cands (i + 1)
  else none
  termination_by cands.size - i
  decreasing_by omega

/-- `v`'s domain: the roots of the lowest-positioned constraint whose variable set is exactly `{v}`
    and whose root plan resolves. Memoized per variable. -/
def denseRncDomOf (ops : DenseZModOps p) (st : DenseRncState p) (v : VarId) :
    Option (List (ZMod p)) × DenseRncState p :=
  if denseRncGetB st.domKnown v then (st.domVal.getD v.index none, st)
  else
    let cands := (((st.anchor.buckets.getD v []).filter (fun q =>
      match st.cvs[q]? with
      | some vs => vs.size == 1
      | none => false)).mergeSort (· ≤ ·)).toArray
    let r := denseRncFirstRoots ops st.cs v cands 0
    (r.map Prod.snd, st.setDom v r)

/-- Every group variable's domain, in group order; `none` if any is missing. -/
def denseRncDoms (ops : DenseZModOps p) (st : DenseRncState p) :
    List VarId → Array (Array (ZMod p)) →
    Option (Array (Array (ZMod p))) × DenseRncState p
  | [], acc => (some acc, st)
  | v :: rest, acc =>
    match denseRncDomOf ops st v with
    | (some ds, st) => denseRncDoms ops st rest (acc.push ds.toArray)
    | (none, st) => (none, st)

/-! ### Enumeration

Points are `Array (ZMod p)` in group order; compiled constraints are evaluated by index. Each
constraint is filed under the *smallest* group index it mentions, and the DFS assigns indices
`n-1 … 0` — which is `denseAssignments`' order (its head variable varies fastest) — so a constraint
is tested as soon as its last variable is assigned and a violation prunes the whole subtree. -/

def denseRncEvalA (zero : ZMod p) (env : Array (ZMod p)) : IExpr p → ZMod p
  | .const n => n
  | .ix i => env.getD i zero
  | .add a b => zmodAddP (denseRncEvalA zero env a) (denseRncEvalA zero env b)
  | .mul a b => zmodMulP (denseRncEvalA zero env a) (denseRncEvalA zero env b)

def denseRncIxMin : IExpr p → Nat → Nat
  | .const _, m => m
  | .ix i, m => min i m
  | .add a b, m => denseRncIxMin b (denseRncIxMin a m)
  | .mul a b, m => denseRncIxMin b (denseRncIxMin a m)

/-- Whether the constraint at `i` is the domain source of its (single) variable, hence zero at every
    point of the box. -/
def denseRncIsDomSrc (st : DenseRncState p) (i : Nat) : Bool :=
  match st.cvs[i]? with
  | some vs =>
    vs.size == 1 && (match vs[0]? with
      | some v => st.domSrc.getD v.index 0 == i + 1
      | none => false)
  | none => false

/-- The compiled covered constraints filed by the smallest group index they mention, dropping the
    domain sources. -/
def denseRncChecks (st : DenseRncState p) (n : Nat) (pos : Array Nat) (ces : List (IExpr p)) :
    Array (Array (IExpr p)) :=
  (ces.toArray.zip pos).foldl (fun acc iep =>
    if denseRncIsDomSrc st iep.2 then acc
    else
      let m := denseRncIxMin iep.1 n
      acc.modify (if m < n then m else 0) (fun a => a.push iep.1)) (Array.replicate n #[])

/-- Enumerate the box depth-first, keeping the points that zero every constraint; `none` as soon as
    a `cap + 1`-st survivor appears (mirroring `denseFilterCap`: above the cap the `k < |xs|` gate
    must fail anyway). -/
def denseRncDfs (zero : ZMod p) (doms : Array (Array (ZMod p)))
    (checks : Array (Array (IExpr p))) (cap : Nat) :
    Nat → Array (ZMod p) → Option (Array (Array (ZMod p))) →
      Array (ZMod p) × Option (Array (Array (ZMod p)))
  | 0, env, acc? => (env, acc?)
  | 1, env, acc? =>
      -- the innermost level emits directly: recursing per point would cost a call and a tuple each
      let chk := checks.getD 0 #[]
      (doms.getD 0 #[]).foldl (fun ea v =>
        match ea with
        | (env, none) => (env, none)
        | (env, some acc) =>
          let env := env.setIfInBounds 0 v
          if chk.all (fun ie => zmodIsZero (denseRncEvalA zero env ie)) then
            (if acc.size < cap then (env, some (acc.push (env.extract 0 env.size)))
             else (env, none))
          else (env, some acc)) (env, acc?)
  | i + 1, env, acc? =>
      let chk := checks.getD i #[]
      (doms.getD i #[]).foldl (fun ea v =>
        match ea with
        | (env, none) => (env, none)
        | (env, some acc) =>
          let env := env.setIfInBounds i v
          if chk.all (fun ie => zmodIsZero (denseRncEvalA zero env ie)) then
            denseRncDfs zero doms checks cap i env (some acc)
          else (env, some acc)) (env, acc?)

/-! ### The candidate -/

/-- Everything an accept needs about a candidate group. The interpolation polynomials, the bit
    patterns and the image table are `Thunk`s: the degree pre-gate rejects nearly every candidate
    (13.5 k of 13.6 k on sha256 `apc_001`) and decides without them (`denseRncDegRW`), so building
    them there is the pass's largest piece of wasted work. -/
structure DenseRncCand (p : ℕ) where
  bits : List VarId
  /-- `|bits|`, the degree of every interpolation polynomial. -/
  k : Nat
  /-- The padded survivor table: per bit pattern, the group's values in group order. The image of
      the group under the interpolation at pattern `t` is row `t` (the indicators are `δ` on the
      patterns), which is what lets the pre-gate work off values alone. -/
  vals : Array (Array (ZMod p))
  hm : Thunk (Std.HashMap VarId (DenseExpr p))
  patts : Thunk (List (List (VarId × ZMod p)))
  pattsA : Thunk (Array (List (VarId × ZMod p)))
  /-- Per pattern, the interpolation image of each group variable, evaluated from `hm` — the
      certificate checks it against `vals` rather than assuming it. -/
  imgs : Thunk (Array (Array (ZMod p)))
  /-- The covered constraints, in position order, as the index gathered them: the certificate is the
      audited predicate on exactly this list (`denseCoveredIdx`-style completeness makes it the
      filter). -/
  es : List (DenseExpr p)
  /-- The covered constraints compiled over the group (`.ix` = group index), in position order. -/
  ces : List (IExpr p)
  survs : Array (Array (ZMod p))

/-- The interpolation polynomial of the group variable at index `j`: `Σ_t indicator_t · value_t`,
    with the per-pattern indicators shared across the group (they depend only on the bits). -/
def denseRncInterp (ctx : DenseRncCtx p) (inds : Array (DenseExpr p))
    (vals : Array (Array (ZMod p))) (j : Nat) : DenseExpr p :=
  let rec go (t : Nat) (acc : DenseExpr p) : DenseExpr p :=
    if h : t < inds.size then
      go (t + 1) (.add acc (.mul inds[t] (.const ((vals.getD t #[]).getD j ctx.ops.zero))))
    else acc
    termination_by inds.size - t
    decreasing_by omega
  (go 0 (.const ctx.ops.zero)).fold

/-- Build the candidate: covered set, domains, box, survivors, bits. Proof-free — `denseRncCert`
    re-verifies. -/
def denseRncBuild (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (DenseRncCand p) × DenseRncState p :=
  let planned := denseCoveredIdxPos st.anchor st.cs xs
  let es := planned.map Prod.snd
  match denseRncDoms ctx.ops st xs #[] with
  | (none, st) => (reg, none, st)
  | (some doms, st) =>
    let boxSize := doms.foldl (fun n dd => n * dd.size) 1
    if boxSize > 256 then (reg, none, st)
    else if es.length == xs.length
        && planned.all (fun ic => (st.cvs.getD ic.1 #[]).size == 1)
        && xs.length ≤ Nat.clog 2 boxSize then (reg, none, st)
    else
      match denseCompileEs xs es with
      | none => (reg, none, st)
      | some ces =>
        let n := doms.size
        match (denseRncDfs ctx.ops.zero doms
            (denseRncChecks st n (planned.map Prod.fst).toArray ces) (2 ^ (xs.length - 1)) n
            (Array.replicate n ctx.ops.zero) (some #[])).2 with
        | none => (reg, none, st)
        | some survs =>
          if survs.size < 2 then (reg, none, st)
          else
            let k := Nat.clog 2 survs.size
            if k ≥ xs.length then (reg, none, st)
            else
              let (reg1, bits) := denseRegisterBits reg freshBase k
              let vals := survs ++ Array.replicate (2 ^ k - survs.size) (survs.getD 0 #[])
              let patts : Thunk (List (List (VarId × ZMod p))) :=
                Thunk.mk (fun _ => denseAssignments (denseBitBox bits))
              let pattsA : Thunk (Array (List (VarId × ZMod p))) :=
                Thunk.mk (fun _ => patts.get.toArray)
              let hm : Thunk (Std.HashMap VarId (DenseExpr p)) := Thunk.mk (fun _ =>
                let inds := pattsA.get.map denseIndicatorExpr
                Std.HashMap.ofList (xs.zipIdx.map
                  (fun xj => (xj.1, denseRncInterp ctx inds vals xj.2))))
              let imgs := Thunk.mk (fun _ => pattsA.get.map (fun aβ =>
                let env := denseEnvOfFast aβ
                (xs.toArray).map (fun x => ((hm.get[x]?).getD (.var x)).evalFast env)))
              (reg1, some { bits := bits, k := k, vals := vals, hm := hm, patts := patts,
                            pattsA := pattsA, imgs := imgs, es := es, ces := ces,
                            survs := survs }, st)

/-! ### The checked certificate

`denseCheckReencodeNoFresh` computes the covered set by filtering the whole system; the index has
already gathered it, and `denseCheckEs` is that same predicate with the list passed in. Freshness
stays the `O(|bits|)` `varSeen` test. -/

/-- `denseCheckReencodeNoFresh` with the covered set supplied. -/
def denseCheckEs (es : List (DenseExpr p)) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
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
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0)))

theorem denseCheckReencodeNoFresh_eq_Es (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) :
    denseCheckReencodeNoFresh d xs bits hm = denseCheckEs (denseCoveredCsOf d xs) xs bits hm := rfl

def denseRncCert (st : DenseRncState p) (xs : List VarId) (cd : DenseRncCand p) : Bool :=
  cd.bits.all (fun b => !denseRncSeen st b) && denseCheckEs cd.es xs cd.bits cd.hm.get

/-! ### The degree pre-gate

The gate needs the *degree* of each candidate position's rewrite, not the rewrite. A maximal
in-group node becomes its interpolation over the bit patterns — `denseCandSelect` always takes it
(its variables are the bits, and it agrees with the substitution at every pattern because the
indicators are `δ` there) — and after `DenseExpr.fold` that interpolation is a constant exactly when
the node takes one value across the padded survivor table, otherwise its surviving terms keep a full
`|bits|`-factor indicator. So the degree follows from values alone, and the interpolation
polynomials (and the substitution map they feed) are never built for a rejected candidate. -/

/-- The degree of a maximal in-group node's rewrite: `0` if it is constant across the survivor
    table, `|bits|` otherwise. -/
def denseRncCandDeg (zero : ZMod p) (k : Nat) (vals : Array (Array (ZMod p))) (xs : List VarId)
    (e : DenseExpr p) : Nat :=
  match denseCompileE xs e with
  | none => k
  | some ie =>
    match vals[0]? with
    | none => 0
    | some r0 =>
      let v0 := denseRncEvalA zero r0 ie
      if vals.all (fun r => zmodIsZero (zmodAddP (denseRncEvalA zero r ie) (zmodNegP v0)))
      then 0 else k

/-- `(denseGroupRewrite xs bits σ patts e).degree`, without building the rewrite. -/
def denseRncDegRW (zero : ZMod p) (k : Nat) (vals : Array (Array (ZMod p))) (xs : List VarId) :
    DenseExpr p → Nat
  | .const _ => 0
  | .var y =>
      if denseContainsFast xs y then denseRncCandDeg zero k vals xs (.var y) else 1
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then denseRncCandDeg zero k vals xs (.add a b)
      else max (denseRncDegRW zero k vals xs a) (denseRncDegRW zero k vals xs b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then denseRncCandDeg zero k vals xs (.mul a b)
      else denseRncDegRW zero k vals xs a + denseRncDegRW zero k vals xs b

/-- Untrusted degree pre-gate: fire when a candidate position's rewrite already exceeds the bound.
    Only positions mentioning a group variable are visited (the buckets are complete), and each
    position's current content is re-tested, so stale bucket entries are harmless. -/
def denseRncDegPre (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : Bool :=
  let deg : DenseExpr p → Nat := denseRncDegRW ctx.ops.zero cd.k cd.vals xs
  let useC := (match st.useCs with | some m => m | none => #[])
  let useB := (match st.useBis with | some m => m | none => #[])
  (denseRncBucketAny useC xs (fun i =>
    match st.cs[i]?, st.cvs[i]? with
    | some c, some vs =>
      denseRncShares xs vs c && !denseRncCovered xs vs c && decide (ctx.dmaxC < deg c)
    | _, _ => false)) ||
  (denseRncBucketAny useB xs (fun i =>
    match st.bis[i]? with
    | some bi =>
      (bi.multiplicity.sharesVarIn xs && decide (ctx.dmaxB < deg bi.multiplicity)) ||
      bi.payload.any (fun e => e.sharesVarIn xs && decide (ctx.dmaxB < deg e))
    | none => false))

/-! ### The accept

Computing the rewrite and writing it are separate steps: the degree decision is taken on the
computed edits, so the write consumes the state linearly (a rejected candidate never touches it, and
an accepted one never needs the old copy alive). -/

/-- One constraint position's new content: the tombstone, or the rewrite with its variable arrays. -/
inductive DenseRncCsEdit (p : ℕ) where
  | tomb (i : Nat)
  | cst (i : Nat) (c : DenseExpr p) (cv full : Array VarId)

def DenseRncCsEdit.pos : DenseRncCsEdit p → Nat
  | .tomb i => i
  | .cst i _ _ _ => i

/-- The accepted rewrite's constraint edits, over the only positions it can touch: the group's
    `useCs` buckets plus the recorded foldable positions. Read-only in `st`; the position list is
    `Std.HashSet`-deduplicated, since applying the rewrite twice at one position is not the
    identity. -/
def denseRncCsEdits (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : List (DenseRncCsEdit p) × Bool :=
  let σ := denseGroupSubst xs cd.hm.get
  let patts := cd.patts.get
  let foldC := (match st.foldCs with | some s => s | none => ∅)
  let useC := (match st.useCs with | some m => m | none => #[])
  ((denseRncPosList useC xs foldC.toList).foldr
    (fun i (acc : List (DenseRncCsEdit p) × Bool) =>
      match st.cs[i]?, st.cvs[i]? with
      | some c, some vs =>
        if denseRncCovered xs vs c then (.tomb i :: acc.1, acc.2)
        else if denseRncShares xs vs c || denseRncHasFold c then
          let c' := denseGroupRewrite xs cd.bits σ patts c
          let cv' := denseRncCapVars c'
          (.cst i c' cv' (denseRncFullVars c' cv') :: acc.1,
           acc.2 && decide (c'.degree ≤ ctx.dmaxC))
        else acc
      | _, _ => acc) ([], true))

/-- The bus half, over its own candidate positions. -/
def denseRncBiEdits (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : List (Nat × BusInteraction (DenseExpr p)) × Bool :=
  let σ := denseGroupSubst xs cd.hm.get
  let patts := cd.patts.get
  let foldB := (match st.foldBis with | some s => s | none => ∅)
  let useB := (match st.useBis with | some m => m | none => #[])
  ((denseRncPosList useB xs foldB.toList).foldr
    (fun i (acc : List (Nat × BusInteraction (DenseExpr p)) × Bool) =>
      match st.bis[i]? with
      | some bi =>
        if bi.multiplicity.sharesVarIn xs || denseRncHasFold bi.multiplicity
            || bi.payload.any (fun e => e.sharesVarIn xs || denseRncHasFold e) then
          let bi' : BusInteraction (DenseExpr p) :=
            { bi with multiplicity := denseGroupRewrite xs cd.bits σ patts bi.multiplicity,
                      payload := bi.payload.map (denseGroupRewrite xs cd.bits σ patts) }
          ((i, bi') :: acc.1,
           acc.2 && decide (bi'.multiplicity.degree ≤ ctx.dmaxB)
             && bi'.payload.all (fun e => decide (e.degree ≤ ctx.dmaxB)))
        else acc
      | none => acc) ([], true))

/-- The content one constraint edit installs. -/
def DenseRncCsEdit.content (ctx : DenseRncCtx p) : DenseRncCsEdit p → DenseExpr p
  | .tomb _ => ctx.zeroE
  | .cst _ c' _ _ => c'

/-- Both edits are the same write: a tombstone is the rewrite to the shared `.const 0`, whose
    variable arrays are empty and which is not foldable, so the index updates are no-ops. -/
def denseRncCsStep (ctx : DenseRncCtx p) (st : DenseRncState p) (e : DenseRncCsEdit p) :
    DenseRncState p :=
  match e with
  | .tomb i => st.rewriteAt i ctx.zeroE #[] #[]
  | .cst i c' cv' full => st.rewriteAt i c' cv' full

/-- Install the edits and the booleanity constraints. Consumes `st`. -/
def denseRncWrite (ctx : DenseRncCtx p) (st : DenseRncState p) (bits : List VarId)
    (csEdits : List (DenseRncCsEdit p)) (biEdits : List (Nat × BusInteraction (DenseExpr p))) :
    DenseRncState p :=
  let st := csEdits.foldl (denseRncCsStep ctx) st
  let st := biEdits.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st
  (bits.foldl (fun st b => st.pushBool b) st).domReset

/-- Whether the current system is within the degree bound. Discharges the side condition that makes
    the edit-level degree test agree with measuring the rewritten system outright; the pipeline's
    degree guard makes it true at every pass entry, so it is computed once per invocation. -/
def denseRncWithinNow (ctx : DenseRncCtx p) (st : DenseRncState p) : Bool :=
  st.cs.all (fun c => decide (c.degree ≤ ctx.dmaxC)) &&
    st.bis.all (fun bi => decide (bi.multiplicity.degree ≤ ctx.dmaxB) &&
      bi.payload.all (fun e => decide (e.degree ≤ ctx.dmaxB)))

/-! ### The bits' derivations

`denseBitCM`'s decision tree, with the group's per-pattern image values read from the shared table
instead of re-evaluating an interpolation polynomial per (bit, pattern, variable). -/

def denseRncMatchCM (img : Array (ZMod p)) (thenM elseM : DenseComputationMethod p) :
    List VarId → Nat → DenseComputationMethod p
  | [], _ => thenM
  | x :: rest, j =>
      .ifEqZero (.add (.var x) (.const (zmodNegP (img.getD j (zmodZeroP p)))))
        (denseRncMatchCM img thenM elseM rest (j + 1)) elseM

def denseRncBitCMGo (ctx : DenseRncCtx p) (cd : DenseRncCand p) (xs : List VarId) (b : VarId)
    (t : Nat) : DenseComputationMethod p :=
  if h : t < cd.pattsA.get.size then
    denseRncMatchCM (cd.imgs.get.getD t #[])
      (.const (denseEnvOfFast cd.pattsA.get[t] b))
      (denseRncBitCMGo ctx cd xs b (t + 1)) xs 0
  else .const ctx.ops.zero
  termination_by cd.pattsA.get.size - t
  decreasing_by omega

/-! ### The step, loop and pass -/

def denseRncView (st : DenseRncState p) : DenseConstraintSystem p :=
  { algebraicConstraints := (st.cs.filter (fun c => !denseIsZero c)).toList,
    busInteractions := st.bis.toList }

/-- One checked re-encoding step on the array state. Same gate sequence as `denseWorkStep`. -/
def denseRncStep (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseRncState p × DenseDerivations p :=
  if !xs.all (fun x => reg.isInput x) then (reg, st, [])
  else if xs.any (fun x => st.minted.contains x) then (reg, st, [])
  else
    let (skip, st) :=
      match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => let st := denseRncEnsureSeen st; (denseRncSeen st i, st)
      | none => (false, st)
    if skip then (reg, st, [])
    else
      match denseRncBuild ctx reg st xs freshBase with
      | (reg1, none, st) => (reg1, st, [])
      | (reg1, some cd, st) =>
        if cd.bits.any (fun b => st.minted.contains b) then (reg1, st, [])
        else
          let st := denseRncEnsureUseBis (denseRncEnsureUse st)
          if denseRncDegPre ctx st xs cd then (reg1, st, [])
          else
            let st := denseRncEnsureSeen st
            if !xs.all (fun x => denseRncSeen st x) then (reg1, st, [])
            else if !xs.all (fun x => decide (x ∉ cd.bits)) then (reg1, st, [])
            else if !cd.bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
              (reg1, st, [])
            else if !denseRncCert st xs cd then (reg1, st, [])
            else
              let st0 := denseRncEnsureFoldBis (denseRncEnsureFoldCs st)
              let (csEdits, okC) := denseRncCsEdits ctx st0 xs cd
              let (biEdits, okB) := denseRncBiEdits ctx st0 xs cd
              let ok := okC && okB && cd.bits.all (fun b =>
                decide ((denseBoolConstraint b : DenseExpr p).degree ≤ ctx.dmaxC))
              if (if st0.dWithin then ok else ok && denseRncWithinNow ctx st0) then
                (reg1, denseRncWrite ctx st0 cd.bits csEdits biEdits,
                 cd.bits.map (fun b => (b, denseRncBitCMGo ctx cd xs b 0)))
              else (reg1, st0, [])

/-- The fresh-name prefix depends only on the item counts, which change only on an accept, so it is
    threaded rather than rebuilt per target (`Nat.toString` twice per target otherwise). -/
def denseRncLoop (ctx : DenseRncCtx p) :
    List (List VarId) → Nat → VarRegistry → DenseRncState p → String →
      VarRegistry × DenseRncState p × DenseDerivations p
  | [], _, reg, st, _ => (reg, st, [])
  | xs :: rest, idx, reg, st, pre =>
    let (reg1, st1, derivs1) := denseRncStep ctx reg st xs (pre ++ toString idx)
    let pre1 := if derivs1.isEmpty then pre else s!"rnc{st1.live}_{st1.bisN}_"
    let (reg2, st2, derivs2) := denseRncLoop ctx rest (idx + 1) reg1 st1 pre1
    (reg2, st2, derivs1 ++ derivs2)

/-! ### The setup walk

One walk over the constraint array yields every position's capped variable array, the live count and
the single-variable set; the targets follow from that array alone. Nothing else is built when there
are no targets, and the remaining structures are `Option`s built on the path that reads them. -/

/-- Per-position capped variables, and the number of non-tombstone positions. -/
def denseRncScan (cs : Array (DenseExpr p)) : Array (Array VarId) × Nat :=
  cs.foldl (fun (acc : Array (Array VarId) × Nat) c =>
    (acc.1.push (denseRncCapVars c), if denseIsZero c then acc.2 else acc.2 + 1)) (#[], 0)

/-- Variables carrying a single-variable constraint. -/
def denseRncSvSet (nVar : Nat) (cvs : Array (Array VarId)) : Array Bool :=
  cvs.foldl (fun s vs =>
    if vs.size == 1 then (match vs[0]? with | some v => denseRncMark s v | none => s) else s)
    (Array.replicate nVar false)

/-- The candidate groups: the variable sets of size 2–8 all of whose members carry a
    single-variable constraint, sorted by the resolved `Variable` (the accept sequence is greedy and
    order-sensitive, so the group order is part of the result) and deduped. -/
def denseRncTargets (reg : VarRegistry) (sv : Array Bool) (cvs : Array (Array VarId)) :
    List (List VarId) :=
  dedupHash (cvs.toList.filterMap (fun vs =>
    if 2 ≤ vs.size && vs.size ≤ 8 && vs.all (fun v => denseRncGetB sv v) then
      some (vs.toList.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
    else none))

/-- Each ≤ 8-variable position under its first variable. -/
def denseRncAnchorBuild (cs : List (DenseExpr p)) : DenseCovIndex :=
  cs.zipIdx.foldr (fun ai idx => denseRncAnchorAdd idx (denseRncAnchorVars ai.1) ai.2) ⟨∅, []⟩

/-- Witness re-encoding. When a group of variables `xs` is so constrained that only a few value
    combinations survive, mint `Nat.clog 2 #survivors` fresh boolean bits, rewrite each group
    variable as an interpolation polynomial over the bits, drop the now-covered constraints, and add
    booleanity constraints — e.g. a group with 3 surviving combinations becomes 2 bits, cutting the
    variable count. The transform is shaped for `DenseVerifiedPassW.ofExtending`; `facts` is unused
    (reencode is fact-free). -/
def denseRncF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    let csArr := d.algebraicConstraints.toArray
    let (cvs, live) := denseRncScan csArr
    let nVar := reg.byId.size
    let targets := denseRncTargets reg (denseRncSvSet nVar cvs) cvs
    match targets with
    | [] => (reg, d, [])
    | _ :: _ =>
      let ops : DenseZModOps p := denseZModOps
      let ctx : DenseRncCtx p := { ops := ops, zeroE := .const ops.zero, b := b }
      let bisArr := d.busInteractions.toArray
      let st : DenseRncState p :=
        { cs := csArr, cvs := cvs, bis := bisArr, live := live, bisN := bisArr.size,
          anchor := denseRncAnchorBuild d.algebraicConstraints,
          useCs := none, useBis := none, foldCs := none, foldBis := none, varSeen := none,
          minted := ∅,
          domVal := Array.replicate nVar none, domKnown := Array.replicate nVar false,
          domSrc := Array.replicate nVar 0, domTouched := [], dWithin := false, nVar := nVar }
      let r := denseRncLoop ctx targets 0 reg st s!"rnc{live}_{bisArr.size}_" 
      (r.1, denseRncView r.2.1, r.2.2)
  else (reg, d, [])

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
        foldBis := Thunk.mk (fun _ => d.busInteractions.zipIdx.foldl
          (fun s bi => if denseBiHasFold bi.1 then s.insert bi.2 else s) ∅)
        liveCs := (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length
        bisN := d.busInteractions.length
        dWithin := false }
      (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length d.busInteractions.length
    (r.1, denseWorkView r.2.1, r.2.2)
  else (reg, d, [])

end ApcOptimizer.Dense
