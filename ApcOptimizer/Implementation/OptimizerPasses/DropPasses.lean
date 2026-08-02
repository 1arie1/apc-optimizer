import ApcOptimizer.Implementation.OptimizerPasses.Rewrite
import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Dense drop-pass runtime recognizers (passes and proofs in `Proofs/DropPasses.lean`) -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Tautology-lookup removal (dense) -/

/-- `constValue?` deciding the fold's shape instead of building it: a non-constant subterm
    short-circuits, so no folded copy of the expression is allocated. The multiplication arms return
    the annihilating factor itself rather than a zero literal, which is the same value there. -/
def DenseExpr.constValueImpl : DenseExpr p → Option (ZMod p)
  | .const n => some n
  | .var _ => none
  | .add a b =>
    match a.constValueImpl with
    | none => none
    | some x =>
      match b.constValueImpl with
      | none => none
      | some y => some (zmodAdd x y)
  | .mul a b =>
    match a.constValueImpl with
    | some x =>
      if zmodIsZero x then some x
      else
        match b.constValueImpl with
        | none => none
        | some y => some (zmodMul x y)
    | none =>
      match b.constValueImpl with
      | some y => if zmodIsZero y then some y else none
      | none => none

/-- Constant value of a dense expression (fold then require a literal). -/
def DenseExpr.constValue? (e : DenseExpr p) : Option (ZMod p) :=
  match e.fold with
  | .const c => some c
  | _ => none

@[csimp] theorem DenseExpr_constValue?_eq_impl :
    @DenseExpr.constValue? = @DenseExpr.constValueImpl := by
  funext q e
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb =>
      simp only [DenseExpr.constValue?, DenseExpr.fold] at *
      rw [DenseExpr.constValueImpl, ← iha, ← ihb]
      cases a.fold <;> cases b.fold <;> simp [DenseExpr.foldAdd] <;> split_ifs <;> simp
  | mul a b iha ihb =>
      simp only [DenseExpr.constValue?, DenseExpr.fold] at *
      rw [DenseExpr.constValueImpl, ← iha, ← ihb]
      cases a.fold <;> cases b.fold <;>
        simp [DenseExpr.foldMul] <;> (try split_ifs) <;> simp_all

/-- Constant values of a dense payload list. -/
def denseConstValues? : List (DenseExpr p) → Option (List (ZMod p))
  | [] => some []
  | e :: rest =>
    match e.constValue?, denseConstValues? rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- Constant message of a dense bus interaction, if fully constant. -/
def denseConstMessage? (bi : BusInteraction (DenseExpr p)) : Option (BusInteraction (ZMod p)) :=
  match bi.multiplicity.constValue?, denseConstValues? bi.payload with
  | some m, some vs => some { busId := bi.busId, multiplicity := m, payload := vs }
  | _, _ => none

/-- Recognizes a tautological lookup: a stateless interaction whose message is fully constant and
    already accepted by the bus — e.g. a range check `[5]` against `[0..255]` — hence droppable. -/
def denseIsTautoLookup (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  !bs.isStateful bi.busId &&
    (match denseConstMessage? bi with
     | some msg => facts.acceptsDec msg
     | none => false)

end ApcOptimizer.Dense
