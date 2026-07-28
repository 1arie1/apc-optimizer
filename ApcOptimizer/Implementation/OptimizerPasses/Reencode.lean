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

/-! ### Variable footprints

A `Nat` bitmask summarising which variables an expression can mention: bit `v.index % denseMaskBits`
for every `v` occurring in it. Disjoint footprints prove `sharesVarIn` false
(`denseVarMask_sharesVarIn_of_land_eq_zero`) without walking the expression, which is what lets the
rewrite gate skip an item in O(1) — see the cached gate below.

`denseMaskBits` is 62 so a mask stays below `2 ^ 63` and is therefore a tagged scalar `Nat`, never a
heap-allocated bignum; an `Array Nat` of masks then allocates nothing per element. -/

def denseMaskBits : Nat := 62

/-- The footprint bit of a single variable. -/
def denseVarBit (v : VarId) : Nat := 1 <<< (v.index % denseMaskBits)

/-- The footprint of an expression: the union of its variables' bits. -/
def denseVarMask : DenseExpr p → Nat
  | .const _ => 0
  | .var y => denseVarBit y
  | .add a b => denseVarMask a ||| denseVarMask b
  | .mul a b => denseVarMask a ||| denseVarMask b

/-- The footprint of a variable list. -/
def denseVarsMask (xs : List VarId) : Nat :=
  xs.foldl (fun m v => m ||| denseVarBit v) 0

theorem denseLandOrLeft {x y m : Nat} (h : (x ||| y) &&& m = 0) : x &&& m = 0 := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  have hi : ((x ||| y) &&& m).testBit i = false := by rw [h]; exact Nat.zero_testBit i
  rw [Nat.testBit_and, Nat.testBit_or] at hi
  rw [Nat.testBit_and, Nat.zero_testBit]
  rcases Bool.and_eq_false_iff.mp hi with hor | hm
  · rw [Bool.or_eq_false_iff] at hor
    rw [hor.1, Bool.false_and]
  · rw [hm, Bool.and_false]

theorem denseLandOrRight {x y m : Nat} (h : (x ||| y) &&& m = 0) : y &&& m = 0 := by
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  have hi : ((x ||| y) &&& m).testBit i = false := by rw [h]; exact Nat.zero_testBit i
  rw [Nat.testBit_and, Nat.testBit_or] at hi
  rw [Nat.testBit_and, Nat.zero_testBit]
  rcases Bool.and_eq_false_iff.mp hi with hor | hm
  · rw [Bool.or_eq_false_iff] at hor
    rw [hor.2, Bool.false_and]
  · rw [hm, Bool.and_false]

theorem denseVarBit_testBit_self (v : VarId) :
    (denseVarBit v).testBit (v.index % denseMaskBits) = true := by
  unfold denseVarBit
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.testBit_two_pow_self

theorem denseVarsMask_testBit_of_mem {xs : List VarId} {v : VarId} (hv : v ∈ xs) :
    (denseVarsMask xs).testBit (v.index % denseMaskBits) = true := by
  unfold denseVarsMask
  suffices h : ∀ (l : List VarId) (acc : Nat), v ∈ l →
      (l.foldl (fun m u => m ||| denseVarBit u) acc).testBit (v.index % denseMaskBits) = true by
    exact h xs 0 hv
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons u rest ih =>
      intro acc h
      rcases List.mem_cons.mp h with rfl | h
      · -- the accumulator keeps `v`'s bit once it is set, so the fold preserves it
        clear ih h
        suffices hk : ∀ (l : List VarId) (acc : Nat),
            acc.testBit (v.index % denseMaskBits) = true →
            (l.foldl (fun m u => m ||| denseVarBit u) acc).testBit
              (v.index % denseMaskBits) = true by
          exact hk rest (acc ||| denseVarBit v)
            (by rw [Nat.testBit_or, denseVarBit_testBit_self]; simp)
        intro l
        induction l with
        | nil => intro acc h; exact h
        | cons w rest ihk =>
            intro acc h
            exact ihk (acc ||| denseVarBit w) (by rw [Nat.testBit_or, h]; simp)
      · exact ih _ h

/-- Disjoint footprints certify that no variable of `xs` occurs in `e`. This is the whole reason the
    cached gate is sound: the mask may over-approximate, so a nonzero intersection means only
    "walk the expression to find out". -/
theorem denseVarMask_sharesVarIn_of_land_eq_zero {xs : List VarId} {e : DenseExpr p}
    (h : denseVarMask e &&& denseVarsMask xs = 0) : e.sharesVarIn xs = false := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [DenseExpr.sharesVarIn]
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have hc := denseContainsFast_sound xs y hc
      have hbit : ((denseVarMask (p := p) (.var y)) &&& denseVarsMask xs).testBit
          (y.index % denseMaskBits) = true := by
        rw [Nat.testBit_and, denseVarsMask_testBit_of_mem hc]
        simpa [denseVarMask] using denseVarBit_testBit_self y
      rw [h] at hbit
      simp at hbit
  | add a b iha ihb =>
      have h' : (denseVarMask a ||| denseVarMask b) &&& denseVarsMask xs = 0 := by
        simpa [denseVarMask] using h
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff]
      exact ⟨iha (denseLandOrLeft h'), ihb (denseLandOrRight h')⟩
  | mul a b iha ihb =>
      have h' : (denseVarMask a ||| denseVarMask b) &&& denseVarsMask xs = 0 := by
        simpa [denseVarMask] using h
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff]
      exact ⟨iha (denseLandOrLeft h'), ihb (denseLandOrRight h')⟩

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

/-- The read-only gate, paired with the degree test of the item it produced (`true` when it fires on
    nothing — see the section note). -/
def denseGateDeg (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p × Bool :=
  if e.sharesVarIn xs || e.hasConstFoldableNode then
    let e' := denseGroupRewrite xs bits σfn patts e
    (e', decide (e'.degree ≤ dmax))
  else (e, true)

theorem denseGateDeg_fst (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) :
    (denseGateDeg dmax xs bits σfn patts e).1 = denseGroupRewrite xs bits σfn patts e := by
  unfold denseGateDeg
  split
  · rfl
  · next h =>
      rw [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true] at h
      exact (denseGroupRewrite_eq_self h.1 h.2).symm

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

/-- The constraint side: the gated rewrite of `l` reversed onto `acc`, with `ok` accumulating the
    degree test of only the items the gate rewrote. Specialised rather than expressed through a
    generic `α → β × Bool` map so the traversal allocates no per-item pair. -/
def denseGateCsGo (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    List (DenseExpr p) → List (DenseExpr p) → Bool → List (DenseExpr p) × Bool
  | [], acc, ok => (acc.reverse, ok)
  | e :: rest, acc, ok =>
      if e.sharesVarIn xs || e.hasConstFoldableNode then
        let e' := denseGroupRewrite xs bits σfn patts e
        denseGateCsGo dmax xs bits σfn patts rest (e' :: acc) (ok && decide (e'.degree ≤ dmax))
      else denseGateCsGo dmax xs bits σfn patts rest (e :: acc) ok

theorem denseGateCsGo_eq (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    ∀ (l acc : List (DenseExpr p)) (ok : Bool),
      denseGateCsGo dmax xs bits σfn patts l acc ok
        = (acc.reverse ++ l.map (fun e => (denseGateDeg dmax xs bits σfn patts e).1),
           ok && l.all (fun e => (denseGateDeg dmax xs bits σfn patts e).2)) := by
  intro l
  induction l with
  | nil => intro acc ok; simp [denseGateCsGo]
  | cons e rest ih =>
      intro acc ok
      rw [denseGateCsGo]
      split
      · next h =>
          rw [ih]
          simp only [List.map_cons, List.all_cons, denseGateDeg, if_pos h,
            List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, Bool.and_assoc]
      · next h =>
          rw [ih]
          simp only [List.map_cons, List.all_cons, denseGateDeg, if_neg h,
            List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
            Bool.true_and]

/-! ### The gate decided from cached footprints

Both disjuncts of the rewrite gate — `sharesVarIn` and `hasConstFoldableNode` — are whole-expression
walks, and both answer "no" for almost every item of the system, so caching one alone saves nothing:
the other still walks. Caching a variable footprint (`denseVarMask`) *and* the foldable flag decides
the gate in O(1) per item. `denseSummSound` is the invariant that makes the O(1) decision agree with
walking, and it is soundness-critical: skipping an item that should have been rewritten would change
the output, so `denseGateCsGoS_eq` takes it as a hypothesis and the loop maintains it. -/

def denseMaskAll : Nat := (1 <<< denseMaskBits) - 1

/-- Can position `i`'s item be passed through untouched, judged from the cached footprints alone?
    Out-of-range positions answer `false` (the `folds` default), so a short array only costs work. -/
def denseSummSkip (masks : Array Nat) (folds : Array Bool) (xsMask i : Nat) : Bool :=
  !(folds.getD i true) && (masks.getD i denseMaskAll &&& xsMask == 0)

/-- The cached footprints describe the items of `cs` positionally, *where they claim to*: the
    obligation is conditioned on the cached foldable flag reading `false`, which is exactly when
    `denseSummSkip` can fire. Empty arrays therefore satisfy this vacuously
    (`denseSummSound_empty`) — the pass can start with no footprints at all, skip nothing, and let
    the first accepting rewrite fill them in, so an APC that never accepts pays nothing for them. -/
def denseSummSound (cs : List (DenseExpr p)) (masks : Array Nat) (folds : Array Bool) : Prop :=
  ∀ i e, cs[i]? = some e → folds.getD i true = false →
    e.hasConstFoldableNode = false ∧ masks.getD i denseMaskAll = denseVarMask e

theorem denseSummSound_empty (cs : List (DenseExpr p)) : denseSummSound cs #[] #[] := by
  intro i e _ hf
  simp at hf

theorem denseSummSkip_gate {masks : Array Nat} {folds : Array Bool} {xs : List VarId} {i : Nat}
    {e : DenseExpr p} (hfe : e.hasConstFoldableNode = false)
    (hm : masks.getD i denseMaskAll = denseVarMask e)
    (hk : denseSummSkip masks folds (denseVarsMask xs) i = true) :
    e.sharesVarIn xs = false ∧ e.hasConstFoldableNode = false := by
  rw [denseSummSkip, Bool.and_eq_true, beq_iff_eq, hm] at hk
  exact ⟨denseVarMask_sharesVarIn_of_land_eq_zero hk.2, hfe⟩

/-- `denseSummSkip` only ever fires where the cached foldable flag reads `false`, which is what makes
    `denseSummSound`'s conditional obligation enough. -/
theorem denseSummSkip_folds {masks : Array Nat} {folds : Array Bool} {xsMask i : Nat}
    (hk : denseSummSkip masks folds xsMask i = true) : folds.getD i true = false := by
  rw [denseSummSkip, Bool.and_eq_true, Bool.not_eq_true'] at hk
  exact hk.1

/-- The constraint side of the rewrite, with the covered-item filter fused in so the position counter
    tracks the *input* list (the filter compacts, the footprints do not), the gate decided from the
    cached footprints, and the output's footprints accumulated as we go. -/
def denseGateCsGoS (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (xsMask : Nat) (masks : Array Nat)
    (folds : Array Bool) :
    Nat → List (DenseExpr p) → List (DenseExpr p) → Array Nat → Array Bool → Bool →
      List (DenseExpr p) × Bool × Array Nat × Array Bool
  | _, [], acc, am, af, ok => (acc.reverse, ok, am, af)
  | i, e :: rest, acc, am, af, ok =>
      if denseCoveredBy xs e then
        denseGateCsGoS dmax xs bits σfn patts xsMask masks folds (i + 1) rest acc am af ok
      else if denseSummSkip masks folds xsMask i then
        denseGateCsGoS dmax xs bits σfn patts xsMask masks folds (i + 1) rest (e :: acc)
          (am.push (masks.getD i denseMaskAll)) (af.push (folds.getD i true)) ok
      else if e.sharesVarIn xs || e.hasConstFoldableNode then
        let e' := denseGroupRewrite xs bits σfn patts e
        denseGateCsGoS dmax xs bits σfn patts xsMask masks folds (i + 1) rest (e' :: acc)
          (am.push (denseVarMask e')) (af.push e'.hasConstFoldableNode)
          (ok && decide (e'.degree ≤ dmax))
      else
        denseGateCsGoS dmax xs bits σfn patts xsMask masks folds (i + 1) rest (e :: acc)
          (am.push (denseVarMask e)) (af.push e.hasConstFoldableNode) ok

/-- The cached gate decides exactly what the walking gate decides, so the fused traversal produces
    the same constraints and the same degree verdict as filtering and then gating. The footprints are
    indexed from `i`, tracking the input list rather than the filtered one. -/
theorem denseGateCsGoS_eq (dmax : Nat) (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (masks : Array Nat) (folds : Array Bool) :
    ∀ (l : List (DenseExpr p)) (i : Nat) (acc : List (DenseExpr p)) (am : Array Nat)
      (af : Array Bool) (ok : Bool),
      (∀ j e, l[j]? = some e → folds.getD (i + j) true = false →
        e.hasConstFoldableNode = false ∧
        masks.getD (i + j) denseMaskAll = denseVarMask e) →
      (denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds i l acc am af ok).1
          = (denseGateCsGo dmax xs bits σfn patts
              (l.filter (fun c => !denseCoveredBy xs c)) acc ok).1 ∧
        (denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds i l acc am af ok).2.1
          = (denseGateCsGo dmax xs bits σfn patts
              (l.filter (fun c => !denseCoveredBy xs c)) acc ok).2 := by
  intro l
  induction l with
  | nil => intro i acc am af ok _; exact ⟨rfl, rfl⟩
  | cons e rest ih =>
      intro i acc am af ok hsound
      have hrest : ∀ j e', rest[j]? = some e' → folds.getD (i + 1 + j) true = false →
          e'.hasConstFoldableNode = false ∧
          masks.getD (i + 1 + j) denseMaskAll = denseVarMask e' := by
        intro j e' hj hf
        rw [show i + 1 + j = i + (j + 1) by omega] at hf ⊢
        exact hsound (j + 1) e' (by simpa using hj) hf
      have hhead : folds.getD i true = false →
          e.hasConstFoldableNode = false ∧ masks.getD i denseMaskAll = denseVarMask e := by
        intro hf
        simpa using hsound 0 e (by simp) (by simpa using hf)
      rw [denseGateCsGoS]
      by_cases hcov : denseCoveredBy xs e = true
      · rw [if_pos hcov, List.filter_cons_of_neg (by simp [hcov])]
        exact ih (i + 1) acc am af ok hrest
      · rw [Bool.not_eq_true] at hcov
        rw [if_neg (by simp [hcov]), List.filter_cons_of_pos (by simp [hcov]), denseGateCsGo]
        by_cases hk : denseSummSkip masks folds (denseVarsMask xs) i = true
        · obtain ⟨hfe, hme⟩ := hhead (denseSummSkip_folds hk)
          obtain ⟨hs1, hs2⟩ := denseSummSkip_gate hfe hme hk
          rw [if_pos hk, if_neg (by simp [hs1, hs2])]
          exact ih (i + 1) (e :: acc) _ _ ok hrest
        · rw [if_neg hk]
          by_cases hg : e.sharesVarIn xs || e.hasConstFoldableNode
          · rw [if_pos hg, if_pos hg]
            exact ih (i + 1) _ _ _ _ hrest
          · rw [if_neg hg, if_neg hg]
            exact ih (i + 1) (e :: acc) _ _ ok hrest

/-- The traversal accumulates the output's footprints: every position it keeps carries the mask of
    the item it kept. Together with `denseGateCsGoS_folds` this re-establishes `denseSummSound` for
    the rewritten system, which is what lets the next candidate use the cached gate. -/
theorem denseGateCsGoS_masks (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (masks : Array Nat) (folds : Array Bool) :
    ∀ (l : List (DenseExpr p)) (i : Nat) (acc : List (DenseExpr p)) (am : Array Nat)
      (af : Array Bool) (ok : Bool),
      (∀ j e, l[j]? = some e → folds.getD (i + j) true = false →
        e.hasConstFoldableNode = false ∧
        masks.getD (i + j) denseMaskAll = denseVarMask e) →
      am = (acc.reverse.map (denseVarMask (p := p))).toArray →
      (denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds i l acc am af ok).2.2.1
        = (((denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds
              i l acc am af ok).1).map (denseVarMask (p := p))).toArray := by
  intro l
  induction l with
  | nil => intro i acc am af ok _ ham; simpa [denseGateCsGoS] using ham
  | cons e rest ih =>
      intro i acc am af ok hsound ham
      have hrest : ∀ j e', rest[j]? = some e' → folds.getD (i + 1 + j) true = false →
          e'.hasConstFoldableNode = false ∧
          masks.getD (i + 1 + j) denseMaskAll = denseVarMask e' := by
        intro j e' hj hf
        rw [show i + 1 + j = i + (j + 1) by omega] at hf ⊢
        exact hsound (j + 1) e' (by simpa using hj) hf
      have hhead : folds.getD i true = false →
          e.hasConstFoldableNode = false ∧ masks.getD i denseMaskAll = denseVarMask e := by
        intro hf
        simpa using hsound 0 e (by simp) (by simpa using hf)
      rw [denseGateCsGoS]
      split
      · exact ih (i + 1) acc am af ok hrest ham
      · split
        · next hk =>
            exact ih (i + 1) (e :: acc) _ _ ok hrest
              (by rw [ham, (hhead (denseSummSkip_folds hk)).2]; simp)
        · split
          · exact ih (i + 1) _ _ _ _ hrest (by rw [ham]; simp)
          · exact ih (i + 1) (e :: acc) _ _ ok hrest (by rw [ham]; simp)

/-- The `hasConstFoldableNode` half of `denseGateCsGoS_masks`. -/
theorem denseGateCsGoS_folds (dmax : Nat) (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (masks : Array Nat) (folds : Array Bool) :
    ∀ (l : List (DenseExpr p)) (i : Nat) (acc : List (DenseExpr p)) (am : Array Nat)
      (af : Array Bool) (ok : Bool),
      (∀ j e, l[j]? = some e → folds.getD (i + j) true = false →
        e.hasConstFoldableNode = false ∧
        masks.getD (i + j) denseMaskAll = denseVarMask e) →
      af = (acc.reverse.map DenseExpr.hasConstFoldableNode).toArray →
      (denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds i l acc am af ok).2.2.2
        = (((denseGateCsGoS dmax xs bits σfn patts (denseVarsMask xs) masks folds
              i l acc am af ok).1).map DenseExpr.hasConstFoldableNode).toArray := by
  intro l
  induction l with
  | nil => intro i acc am af ok _ haf; simpa [denseGateCsGoS] using haf
  | cons e rest ih =>
      intro i acc am af ok hsound haf
      have hrest : ∀ j e', rest[j]? = some e' → folds.getD (i + 1 + j) true = false →
          e'.hasConstFoldableNode = false ∧
          masks.getD (i + 1 + j) denseMaskAll = denseVarMask e' := by
        intro j e' hj hf
        rw [show i + 1 + j = i + (j + 1) by omega] at hf ⊢
        exact hsound (j + 1) e' (by simpa using hj) hf
      have hhead : folds.getD i true = false →
          e.hasConstFoldableNode = false ∧ masks.getD i denseMaskAll = denseVarMask e := by
        intro hf
        simpa using hsound 0 e (by simp) (by simpa using hf)
      rw [denseGateCsGoS]
      split
      · exact ih (i + 1) acc am af ok hrest haf
      · split
        · next hk =>
            have hfz := denseSummSkip_folds hk
            exact ih (i + 1) (e :: acc) _ _ ok hrest
              (by rw [haf, show folds.getD i true = e.hasConstFoldableNode from
                    hfz.trans (hhead hfz).1.symm]; simp)
        · split
          · exact ih (i + 1) _ _ _ _ hrest (by rw [haf]; simp)
          · exact ih (i + 1) (e :: acc) _ _ ok hrest (by rw [haf]; simp)

/-- The bus side of `denseGateCsGo`. -/
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

/-- `denseReencodeOut` together with `withinDegreeB` on its result. The `Bool` is only valid for an
    input system that is itself within the bound (`denseReencodeOutOk_snd`); the caller keeps that
    as an invariant (`DenseReencodeCacheState.dWithin`). -/
def denseReencodeOutOk (b : DegreeBound) (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p × Bool :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let rc := denseGateCsGo b.identities xs bits σfn patts
    (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)) [] true
  let rb := denseGateBisGo b.busInteractions xs bits σfn patts d.busInteractions [] true
  let bools := bits.map denseBoolConstraint
  ({ algebraicConstraints := rc.1 ++ bools, busInteractions := rb.1 },
    (rc.2 && bools.all (fun c => decide (c.degree ≤ b.identities))) && rb.2)

theorem denseReencodeOutOk_fst (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    (denseReencodeOutOk b d xs bits hm).1 = denseReencodeOut d xs bits hm := by
  unfold denseReencodeOutOk denseReencodeOut
  simp only [denseGateCsGo_eq, denseGateBisGo_eq, List.reverse_nil, List.nil_append,
    denseGateDeg_fst, denseBIGateDeg_fst, denseBIRewriteGate_eq]

/-- Two lists' `all` agree when the predicates agree pointwise on the members. -/
theorem List.all_congr_mem {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem denseReencodeOutOk_snd (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (hd : d.withinDegreeB b = true) :
    (denseReencodeOutOk b d xs bits hm).2 = (denseReencodeOut d xs bits hm).withinDegreeB b := by
  rw [DenseConstraintSystem.withinDegreeB, Bool.and_eq_true] at hd
  obtain ⟨hdc, hdb⟩ := hd
  rw [List.all_eq_true] at hdc hdb
  rw [← denseReencodeOutOk_fst b d xs bits hm]
  unfold denseReencodeOutOk DenseConstraintSystem.withinDegreeB
  simp only [denseGateCsGo_eq, denseGateBisGo_eq, List.reverse_nil, List.nil_append,
    Bool.true_and, List.all_append, List.all_map, Function.comp_def]
  -- the constraint side: an item the gate left alone is a member of `d`, so `hdc` bounds it
  have hcs : (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).all
        (fun e => (denseGateDeg b.identities xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) e).2)
      = (d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).all
        (fun e => decide ((denseGateDeg b.identities xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) e).1.degree ≤ b.identities)) := by
    refine List.all_congr_mem _ _ _ (fun e he => ?_)
    have hmem : e ∈ d.algebraicConstraints := List.mem_of_mem_filter he
    unfold denseGateDeg
    split
    · rfl
    · exact (hdc e hmem).symm
  -- the bus side, the same argument per interaction
  have hbs : d.busInteractions.all
        (fun bi => (denseBIGateDeg b.busInteractions xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) bi).2)
      = d.busInteractions.all (fun bi =>
          decide ((denseBIGateDeg b.busInteractions xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits)) bi).1.multiplicity.degree ≤ b.busInteractions) &&
          (denseBIGateDeg b.busInteractions xs bits (denseGroupSubst xs hm)
            (denseAssignments (denseBitBox bits)) bi).1.payload.all
              (fun e => decide (e.degree ≤ b.busInteractions))) := by
    refine List.all_congr_mem _ _ _ (fun bi hbi => ?_)
    unfold denseBIGateDeg
    split
    · rfl
    · exact (hdb bi hbi).symm
  rw [hcs, hbs]

/-- Footprint arrays built directly from a constraint list are sound for it. -/
theorem denseSummSound_of_toArray (cs : List (DenseExpr p)) :
    denseSummSound cs ((cs.map (denseVarMask (p := p))).toArray)
      ((cs.map DenseExpr.hasConstFoldableNode).toArray) := by
  intro i e hi hf
  have hm : ((cs.map (denseVarMask (p := p))).toArray).getD i denseMaskAll = denseVarMask e := by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, hi,
      Option.map_some, Option.getD_some]
  have hfv : ((cs.map DenseExpr.hasConstFoldableNode).toArray).getD i true
      = e.hasConstFoldableNode := by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, hi,
      Option.map_some, Option.getD_some]
  exact ⟨hfv.symm.trans hf, hm⟩

/-- `denseReencodeOutOk` with the constraint side driven by the cached footprints, returning the
    footprints of the system it produced. Behaviour is identical whenever the incoming footprints
    describe `d` (`denseReencodeOutOkS_fst`, `denseReencodeOutOkS_snd`), and the outgoing ones
    describe the result (`denseReencodeOutOkS_summ`), which is the loop's invariant. -/
def denseReencodeOutOkS (b : DegreeBound) (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (masks : Array Nat) (folds : Array Bool) :
    DenseConstraintSystem p × Bool × Array Nat × Array Bool :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let rc := denseGateCsGoS b.identities xs bits σfn patts (denseVarsMask xs) masks folds 0
    d.algebraicConstraints [] #[] #[] true
  let rb := denseGateBisGo b.busInteractions xs bits σfn patts d.busInteractions [] true
  let bools := bits.map denseBoolConstraint
  ({ algebraicConstraints := rc.1 ++ bools, busInteractions := rb.1 },
    (rc.2.1 && bools.all (fun c => decide (c.degree ≤ b.identities))) && rb.2,
    rc.2.2.1 ++ (bools.map (denseVarMask (p := p))).toArray,
    rc.2.2.2 ++ (bools.map DenseExpr.hasConstFoldableNode).toArray)

theorem denseReencodeOutOkS_fst (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) (masks : Array Nat)
    (folds : Array Bool) (hs : denseSummSound d.algebraicConstraints masks folds) :
    (denseReencodeOutOkS b d xs bits hm masks folds).1 = denseReencodeOut d xs bits hm := by
  rw [← denseReencodeOutOk_fst b d xs bits hm]
  unfold denseReencodeOutOkS denseReencodeOutOk
  have h := (denseGateCsGoS_eq b.identities xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) masks folds d.algebraicConstraints 0 [] #[] #[] true
    (fun j e hj hf => by
      simpa [Nat.zero_add] using hs j e hj (by simpa [Nat.zero_add] using hf))).1
  simp only [h]

theorem denseReencodeOutOkS_snd (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) (masks : Array Nat)
    (folds : Array Bool) (hs : denseSummSound d.algebraicConstraints masks folds) :
    (denseReencodeOutOkS b d xs bits hm masks folds).2.1 = (denseReencodeOutOk b d xs bits hm).2 := by
  unfold denseReencodeOutOkS denseReencodeOutOk
  have h := (denseGateCsGoS_eq b.identities xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) masks folds d.algebraicConstraints 0 [] #[] #[] true
    (fun j e hj hf => by
      simpa [Nat.zero_add] using hs j e hj (by simpa [Nat.zero_add] using hf))).2
  simp only [h]

theorem denseReencodeOutOkS_summ (b : DegreeBound) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) (masks : Array Nat)
    (folds : Array Bool) (hs : denseSummSound d.algebraicConstraints masks folds) :
    denseSummSound (denseReencodeOutOkS b d xs bits hm masks folds).1.algebraicConstraints
      (denseReencodeOutOkS b d xs bits hm masks folds).2.2.1
      (denseReencodeOutOkS b d xs bits hm masks folds).2.2.2 := by
  have hshift : ∀ j e, d.algebraicConstraints[j]? = some e → folds.getD (0 + j) true = false →
      e.hasConstFoldableNode = false ∧
      masks.getD (0 + j) denseMaskAll = denseVarMask e :=
    fun j e hj hf => by
      simpa [Nat.zero_add] using hs j e hj (by simpa [Nat.zero_add] using hf)
  have hm' := denseGateCsGoS_masks b.identities xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) masks folds d.algebraicConstraints 0 [] #[] #[] true
    hshift (by simp)
  have hf' := denseGateCsGoS_folds b.identities xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) masks folds d.algebraicConstraints 0 [] #[] #[] true
    hshift (by simp)
  have happ : ∀ {α : Type _} (u v : List α), (u ++ v).toArray = u.toArray ++ v.toArray :=
    fun u v => Array.toArray_eq_append_iff.mpr rfl
  show denseSummSound _ _ _
  unfold denseReencodeOutOkS
  simp only [hm', hf']
  rw [← happ, ← happ, ← List.map_append, ← List.map_append]
  exact denseSummSound_of_toArray _

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
  /-- Whether `d` is *known* to be within the degree bound — the side condition that makes
      `denseReencodeOutOk`'s fused degree test agree with measuring the rewritten system outright
      (`denseReencodeOutOk_snd`). Starts `false`, so the first candidate to reach the gate measures
      the rewritten system the plain way; from the first accept on it is `true`, since an accepted
      `ro` passed the gate and becomes the new `d`. Deliberately not seeded with
      `d.withinDegreeB b`: that walk would be charged to every APC, including the ones where no
      candidate is ever accepted. -/
  dWithin : Bool
  /-- Per-position variable footprints of `d.algebraicConstraints`, and their cached
      `hasConstFoldableNode`. Together they decide the rewrite gate without walking an expression;
      `denseSummSound` (maintained by `denseReencodeStepCached_summ`) is what makes that agree with
      walking. Unlike the other arrays here these track `d` positionally, not the stable
      pre-tombstone positions — the gate runs on `d`'s compacted list. -/
  masks : Array Nat
  folds : Array Bool

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
        { st with arrCs := st.arrCs.set i (.const 0), rootCache := st.rootCache.erase i,
                  foldCs := st.foldCs.erase i }
      else if c.sharesVarIn xs || c.hasConstFoldableNode then
        let c' := denseGroupRewrite xs bits σfn patts c
        let vs := HashedDedup.hashedDedup (hash ·) c'.vars
        { st with
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

/-- One checked re-encoding step (identity if construction or the certificate fails). Applies the
    gates in order, minting fresh bits and rewriting `d` only on full acceptance; the threaded
    candidate state is updated in place rather than rebuilt. -/
def denseReencodeStepCached (b : DegreeBound)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (state : DenseReencodeCacheState p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseReencodeCacheState p :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => state.varSet.contains i
      | none => false) then
    (reg, d, [], state)
  else
  match denseBuildReencodeCached reg state.csIdx state.arrCs state.rootCache xs freshBase with
  | (reg1, none, rootCache) => (reg1, d, [], { state with rootCache })
  | (reg1, some (bits, hm), rootCache) =>
    let state := { state with rootCache }
    if denseDegPreRejectIdx b state.useCs state.useBis state.arrBis state.arrCs xs bits hm then
      (reg1, d, [], state)
    else
    if xs.all (fun x => state.varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOutOkS b d xs bits hm state.masks state.folds
      if (if state.dWithin then ro.2.1 else ro.1.withinDegreeB b) then
        (reg1, ro.1,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         { denseReencodeStateUpdate state xs bits hm with
             masks := ro.2.2.1, folds := ro.2.2.2 })
      else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
  else (reg, d, [], state)

/-- The `dWithin` invariant is preserved by a step, which is what makes the fused degree gate above
    decide exactly what `(denseReencodeOut d xs bits hm).withinDegreeB b` decides
    (`denseReencodeOutOk_snd`): the flag is only ever set on the accept path, and there the accepted
    system passed the gate, and it starts `false`, so every step of the loop sees a valid flag.

    Unreachable from the correctness roots by design: the degree bound is enforced *outside* the
    pass, by `guardAll` in `Implementation/Optimizer.lean`, so this internal gate decides which
    candidates are accepted — behaviour, not soundness. -/
theorem denseReencodeStepCached_dWithin (b : DegreeBound) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (state : DenseReencodeCacheState p) (xs : List VarId)
    (freshBase : String) (hdw : state.dWithin = true → d.withinDegreeB b = true)
    (hsumm : denseSummSound d.algebraicConstraints state.masks state.folds) :
    (denseReencodeStepCached b reg d state xs freshBase).2.2.2.dWithin = true →
      (denseReencodeStepCached b reg d state xs freshBase).2.1.withinDegreeB b = true := by
  fun_cases denseReencodeStepCached b reg d state xs freshBase
  case case4 =>
    rename_i hgate hcoll reg1 bits hm rootCache hbeq state1 hdpr hA hB hC hD ro hwd
    intro _
    show ro.1.withinDegreeB b = true
    have hsumm1 : denseSummSound d.algebraicConstraints state1.masks state1.folds := hsumm
    by_cases hsw : state1.dWithin = true
    · rw [if_pos hsw] at hwd
      rw [denseReencodeOutOkS_fst b d xs bits hm _ _ hsumm1,
        ← denseReencodeOutOk_snd b d xs bits hm (hdw hsw),
        ← denseReencodeOutOkS_snd b d xs bits hm _ _ hsumm1]
      exact hwd
    · rw [if_neg hsw] at hwd
      exact hwd
  all_goals exact hdw

/-- The footprint invariant is preserved by a step: an accepting step installs exactly the footprints
    `denseReencodeOutOkS` accumulated for the system it produced, and every other branch leaves both
    `d` and the footprints alone. This is what the loop threads. -/
theorem denseReencodeStepCached_summ (b : DegreeBound) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (state : DenseReencodeCacheState p) (xs : List VarId)
    (freshBase : String)
    (hsumm : denseSummSound d.algebraicConstraints state.masks state.folds) :
    denseSummSound (denseReencodeStepCached b reg d state xs freshBase).2.1.algebraicConstraints
      (denseReencodeStepCached b reg d state xs freshBase).2.2.2.masks
      (denseReencodeStepCached b reg d state xs freshBase).2.2.2.folds := by
  fun_cases denseReencodeStepCached b reg d state xs freshBase
  case case4 =>
    rename_i hgate hcoll reg1 bits hm rootCache hbeq state1 hdpr hA hB hC hD ro hwd
    exact denseReencodeOutOkS_summ b d xs bits hm _ _ hsumm
  all_goals exact hsumm

/-- `d`'s item counts for the fresh-name prefix, re-read only after a step that rewrote `d`
    (a step derives one method per minted bit, so nonempty derivations mark exactly the accepts). -/
def denseReencodeNameCounts (derivs : DenseDerivations p) (d : DenseConstraintSystem p)
    (nc nb : Nat) : Nat × Nat :=
  if derivs.isEmpty then (nc, nb)
  else (d.algebraicConstraints.length, d.busInteractions.length)

/-- Process the candidate groups sequentially, threading the registry, the candidate state and
    `d`'s item counts (`nc`/`nb`, the fresh-name prefix). -/
def denseReencodeLoopCached (b : DegreeBound) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p →
      DenseReencodeCacheState p → Nat → Nat →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, state, nc, nb =>
    let (reg1, d1, derivs1, state1) :=
      denseReencodeStepCached b reg d state xs s!"rnc{nc}_{nb}_{idx}"
    let (nc1, nb1) := denseReencodeNameCounts derivs1 d1 nc nb
    let (reg2, d2, derivs2) :=
      denseReencodeLoopCached b rest (idx + 1) reg1 d1 state1 nc1 nb1
    (reg2, d2, derivs1 ++ derivs2)

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
        -- Sort by the resolved `Variable`'s order: `denseReencodeLoopCached` below is a greedy,
        -- order-sensitive accept/reject sequence, so the group order determines the outcome.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    denseReencodeLoopCached b targets 0 reg d
      { csIdx := denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints
        arrCs := d.algebraicConstraints.toArray
        rootCache := ∅
        varSet := Std.HashSet.ofList d.occ
        useCs := denseCovBuild DenseExpr.vars d.algebraicConstraints
        useBis := denseCovBuild denseBIVars d.busInteractions
        arrBis := d.busInteractions.toArray
        foldCs := d.algebraicConstraints.zipIdx.foldl
          (fun s ci => if ci.1.hasConstFoldableNode then s.insert ci.2 else s) ∅
        dWithin := false
        masks := #[]
        folds := #[] }
      d.algebraicConstraints.length d.busInteractions.length
  else (reg, d, [])

end ApcOptimizer.Dense
