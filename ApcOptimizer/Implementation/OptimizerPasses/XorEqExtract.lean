import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack

set_option autoImplicit false

/-! # Dense bitwise-XOR constant-operand equality extraction

Impl-only: the constant-operand XOR recognizer `denseXorEq?`, the OR/AND generalization
`denseBoolEq?` (with `denseSimpleTarget`/`denseOpIs`), and the transform `denseXorEqExtractF`;
correctness in `Proofs/XorEqExtract.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The entailed equality from a constant-operand XOR interaction. -/
def denseXorEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = DenseExpr.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if op = DenseExpr.const spec.xorOp then
          if o1 = DenseExpr.const 0 then some (denseEqExpr r o2)
          else if o2 = DenseExpr.const 0 then some (denseEqExpr r o1)
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o1 = DenseExpr.const 255 then
            some (denseEqExpr r (denseComplExpr o2))
          else if 256 ≤ p ∧ spec.bound = 256 ∧ o2 = DenseExpr.const 255 then
            some (denseEqExpr r (denseComplExpr o1))
          else none
        else none
      | none => none
    else none

/-- The `255` literal behind a call, so it stays out of the recognizers' entry. -/
def denseIsConst255 (e : DenseExpr p) : Bool := decide (e = DenseExpr.const 255)

/-- Dictionary-free twin: the literal-`1` multiplicity gate runs first (a tag test, ahead of the
    `byteXorSpec` lookup), the `0` tests go through `isConstZero`, and `255` sits behind
    `denseIsConst255`, which the hot path never reaches. -/
def denseXorEqImpl? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  if bi.multiplicity.isConstOne then
    match facts.byteXorSpec bi.busId with
    | none => none
    | some spec =>
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if op = DenseExpr.const spec.xorOp then
          if o1.isConstZero then some (denseEqExpr r o2)
          else if o2.isConstZero then some (denseEqExpr r o1)
          else if 256 ≤ p ∧ spec.bound = 256 ∧ denseIsConst255 o1 = true then
            some (denseEqExpr r (denseComplExpr o2))
          else if 256 ≤ p ∧ spec.bound = 256 ∧ denseIsConst255 o2 = true then
            some (denseEqExpr r (denseComplExpr o1))
          else none
        else none
      | none => none
  else none

@[csimp] theorem denseXorEq_eq_impl : @denseXorEq? = @denseXorEqImpl? := by
  funext q bs facts bi
  unfold denseXorEq? denseXorEqImpl?
  rw [DenseExpr.isConstOne_eq_decide]
  by_cases hm : bi.multiplicity = DenseExpr.const 1
  · simp only [hm, decide_true, if_true, DenseExpr.isConstZero_eq_decide, decide_eq_true_eq,
      denseIsConst255, decide_eq_true_eq]
  · simp only [hm, decide_false, Bool.false_eq_true, if_false]
    cases facts.byteXorSpec bi.busId with
    | none => rfl
    | some spec =>
      cases spec.decode bi.payload with
      | none => rfl
      | some t => obtain ⟨op, o1, o2, r⟩ := t; rfl

/-- A substitution target Gauss can inline freely: a constant. -/
def denseSimpleTarget (e : DenseExpr p) : Bool := e.constValue?.isSome

/-- Does `op` match the (optional) op-selector value `o`? -/
def denseOpIs (o : Option (ZMod p)) (op : DenseExpr p) : Bool :=
  match o with
  | some v => decide (op = DenseExpr.const v)
  | none => false

/-- The entailed equality from a constant-zero-operand OR/AND interaction (result pinned to a
    constant). -/
def denseBoolEq? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    if bi.multiplicity = DenseExpr.const 1 then
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if denseOpIs spec.orOp op then
          if o1 = DenseExpr.const 0 then
            (if denseSimpleTarget o2 then some (denseEqExpr r o2) else none)
          else if o2 = DenseExpr.const 0 then
            (if denseSimpleTarget o1 then some (denseEqExpr r o1) else none)
          else none
        else if denseOpIs spec.andOp op then
          if o1 = DenseExpr.const 0 ∨ o2 = DenseExpr.const 0 then some r
          else none
        else none
      | none => none
    else none

/-- Dictionary-free twin of `denseBoolEq?`; see `denseXorEqImpl?`. -/
def denseBoolEqImpl? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  if bi.multiplicity.isConstOne then
    match facts.byteXorSpec bi.busId with
    | none => none
    | some spec =>
      match spec.decode bi.payload with
      | some (op, o1, o2, r) =>
        if denseOpIs spec.orOp op then
          if o1.isConstZero then
            (if denseSimpleTarget o2 then some (denseEqExpr r o2) else none)
          else if o2.isConstZero then
            (if denseSimpleTarget o1 then some (denseEqExpr r o1) else none)
          else none
        else if denseOpIs spec.andOp op then
          if o1.isConstZero || o2.isConstZero then some r
          else none
        else none
      | none => none
  else none

@[csimp] theorem denseBoolEq_eq_impl : @denseBoolEq? = @denseBoolEqImpl? := by
  funext q bs facts bi
  unfold denseBoolEq? denseBoolEqImpl?
  rw [DenseExpr.isConstOne_eq_decide]
  by_cases hm : bi.multiplicity = DenseExpr.const 1
  · simp only [hm, decide_true, if_true, DenseExpr.isConstZero_eq_decide, decide_eq_true_eq,
      Bool.or_eq_true, decide_eq_true_eq]
  · simp only [hm, decide_false, Bool.false_eq_true, if_false]
    cases facts.byteXorSpec bi.busId with
    | none => rfl
    | some spec =>
      cases spec.decode bi.payload with
      | none => rfl
      | some t => obtain ⟨op, o1, o2, r⟩ := t; rfl

end ApcOptimizer.Dense
