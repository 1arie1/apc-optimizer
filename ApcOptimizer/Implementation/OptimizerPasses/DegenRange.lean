import ApcOptimizer.Implementation.OptimizerPasses.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Dense degenerate range checks → algebraic constraints

Impl-only recognizers for the `degenRange` pass (an `ofCheckRules` instance): a width-0 range
check forces its value slot to `0`; a width-1 check (on a prime field) makes its value boolean.
Rules, proofs and wiring in `Proofs/DegenRange.lean`. -/

namespace DegenRange

variable {p : ℕ}

/-- On a prime field, `x < 2` (value-level) is exactly booleanity `x·(x−1) = 0`. -/
theorem val_lt_two_iff (hp : Nat.Prime p) (x : ZMod p) :
    x.val < 2 ↔ x * (x - 1) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hlt
    have : x.val = 0 ∨ x.val = 1 := by omega
    rcases this with h0 | h1
    · rw [ZMod.val_eq_zero] at h0; rw [h0]; ring
    · have hx1 : x = 1 := by
        have := (ZMod.natCast_rightInverse x).symm
        rw [this, h1]; norm_cast
      rw [hx1]; ring
  · intro hprod
    rcases mul_eq_zero.1 hprod with h0 | h1
    · rw [h0, ZMod.val_zero]; omega
    · have hx1 : x = 1 := by linear_combination h1
      rw [hx1, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt]; omega

end DegenRange

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `v·(v − 1)` as a dense expression. -/
def denseBoolC (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (-1)))

/-- The `-1` numeral alone pulls the `ZMod.commRing` chain into every emitted constraint. -/
def denseBoolCImpl (v : DenseExpr p) : DenseExpr p := .mul v (.add v (.const (zmodNegOneP p)))

@[csimp] theorem denseBoolC_eq_impl : @denseBoolC = @denseBoolCImpl := by
  funext q v; rw [denseBoolC, denseBoolCImpl, zmodNegOneP_eq]

/-- Recognizes a degenerate-width range check: width-0 (`c = 0`) forces its value slot to `0`;
    width-1 (`c = 1`, on a prime field) makes its value boolean, returning `v·(v−1) = 0`. -/
def denseRangeEq? (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match bi.payload with
  | [v, c] =>
    if bi.multiplicity = DenseExpr.const 1 then
      if facts.zeroRangeEq bi.busId = true ∧ c = DenseExpr.const 0 then some v
      else if one = true ∧ facts.varRangeBus bi.busId = true ∧ c = DenseExpr.const 1
          ∧ v.degree ≤ 1 then some (denseBoolC v)
      else none
    else none
  | _ => none

/-- The `DenseExpr` equalities against `const 0` / `const 1` put a `ZMod.commRing` chain at this
    recognizer's *entry*, ahead of the payload-shape test, so every interaction paid it. The tag
    matches gate first and the literal tests go through the dictionary-free primitives; the
    `facts` lookups (an assoc-list scan each) come after the cheaper `ZMod` tests. -/
def denseRangeEqImpl? (one : Bool) (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match bi.payload, bi.multiplicity with
  | [v, .const c], .const m =>
    if zmodIsOne m then
      if zmodIsZero c && facts.zeroRangeEq bi.busId then some v
      else if one && zmodIsOne c && facts.varRangeBus bi.busId && v.degree ≤ 1 then
        some (denseBoolC v)
      else none
    else none
  | _, _ => none

@[csimp] theorem denseRangeEq_eq_impl : @denseRangeEq? = @denseRangeEqImpl? := by
  funext q one bs facts bi
  obtain ⟨busId, mult, payload⟩ := bi
  simp only [denseRangeEq?, denseRangeEqImpl?]
  rcases payload with _ | ⟨v, tl⟩
  · cases mult <;> simp
  rcases tl with _ | ⟨c, tl⟩
  · cases mult <;> simp
  rcases tl with _ | ⟨w, tl⟩
  case cons => cases mult <;> simp
  cases c with
  | var _ => cases mult <;> simp
  | add _ _ => cases mult <;> simp
  | mul _ _ => cases mult <;> simp
  | const k =>
    cases mult with
    | var _ => simp
    | add _ _ => simp
    | mul _ _ => simp
    | const m =>
      simp only [DenseExpr.const.injEq, zmodIsOne_eq, zmodIsZero_eq, Bool.and_eq_true,
        decide_eq_true_eq]
      split_ifs <;> tauto

def DenseExpr.isBareVar : DenseExpr p → Bool
  | .var _ => true
  | _ => false

/-- Does some slot hold a bare variable? A pre-filter for `denseBoolCheck?`, which emits only when
    its value slot does — allocation-free, unlike the pattern it guards. -/
def denseHasBareVar : List (DenseExpr p) → Bool
  | [] => false
  | e :: rest => e.isBareVar || denseHasBareVar rest

/-- `payload.map constValue?` without `mapTR`'s reversal pass. -/
def denseConstPattern : List (DenseExpr p) → List (Option (ZMod p))
  | [] => []
  | e :: rest => e.constValue? :: denseConstPattern rest

theorem denseConstPattern_eq (l : List (DenseExpr p)) :
    denseConstPattern l = l.map DenseExpr.constValue? := by
  induction l with
  | nil => rfl
  | cons e t ih => rw [denseConstPattern, List.map_cons, ih]

/-- No bare variable anywhere means no slot is one, which is what makes the pre-filter exact. -/
theorem denseHasBareVar_getElem? (l : List (DenseExpr p)) (h : denseHasBareVar l = false)
    (i : Nat) (x : VarId) : l[i]? ≠ some (DenseExpr.var x) := by
  induction l generalizing i with
  | nil => simp
  | cons e t ih =>
    rw [denseHasBareVar, Bool.or_eq_false_iff] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq]
      intro he
      rw [he] at h
      exact absurd h.1 (by simp [DenseExpr.isBareVar])
    | succ n => simpa using ih h.2 n

def denseBoolCheckImpl? {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match bi.multiplicity with
  | .const m =>
    if zmodIsOne m && denseHasBareVar bi.payload then
      match facts.rangeCheckAt bi.busId (denseConstPattern bi.payload) with
      | some (valSlot, bound) =>
        if bound == 2 then
          match bi.payload[valSlot]? with
          | some (DenseExpr.var x) => some (denseBoolC (DenseExpr.var x))
          | _ => none
        else none
      | none => none
    else none
  | _ => none

/-- The booleanity `x·(x−1)` of a width-1 (`bound = 2`) check whose value slot is a bare variable
    `x`. -/
def denseBoolCheck? {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = DenseExpr.const 1 ∧ bound = 2 then
      match bi.payload[valSlot]? with
      | some (DenseExpr.var x) => some (denseBoolC (DenseExpr.var x))
      | _ => none
    else none
  | none => none

@[csimp] theorem denseBoolCheck_q_eq_impl : @denseBoolCheck? = @denseBoolCheckImpl? := by
  funext q bs facts bi
  simp only [denseBoolCheck?, denseBoolCheckImpl?, denseConstPattern_eq]
  cases hm : bi.multiplicity with
  | var _ | add _ _ | mul _ _ =>
    cases facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
    | none => rfl
    | some vb => obtain ⟨valSlot, bound⟩ := vb; simp
  | const m =>
    by_cases hm1 : m = 1
    case neg =>
      cases facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | none => simp [zmodIsOne_eq, hm1]
      | some vb => obtain ⟨valSlot, bound⟩ := vb; simp [zmodIsOne_eq, hm1]
    case pos =>
      subst hm1
      by_cases hbv : denseHasBareVar bi.payload = true
      case pos => simp [zmodIsOne_eq, hbv]
      case neg =>
        simp only [Bool.not_eq_true] at hbv
        simp only [zmodIsOne_eq, hbv, decide_true, Bool.and_false]
        cases facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
        | none => rfl
        | some vb =>
          obtain ⟨valSlot, bound⟩ := vb
          simp only [true_and]
          split
          · cases hg : bi.payload[valSlot]? with
            | none => rfl
            | some e =>
              cases e with
              | var x => exact absurd hg (denseHasBareVar_getElem? bi.payload hbv valSlot x)
              | const _ => rfl
              | add _ _ => rfl
              | mul _ _ => rfl
          · rfl

end ApcOptimizer.Dense
