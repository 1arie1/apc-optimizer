import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.AddrDiseq
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Shared soundness helpers from the `busUnify` surface

Value-level helpers and the constant-address (dis)equality certificates consumed by other pass
proofs (`Proofs/XorEqExtract.lean`, `Proofs/BusPairCancelIndex.lean`,
`Proofs/BusPairCancelCheck.lean`).

The `busUnify` pass itself (`BusUnify.lean`) is not scheduled: its soundness would consume the
order-free rely via `admissibleMemoryBusM_copies` (`Implementation/MemoryBusMultiset.lean`), whose
timestamp hypotheses — a payload-determined `tsVal` with semantically strictly increasing send
values — no circuit fact provides (`MemoryBusShape` names no timestamp slot, and strict
monotonicity of `ZMod.val` timestamps needs a no-wrap bound the circuit does not enforce). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A dense constant-folded expression evaluates to its recognized constant. -/
private theorem denseConstValueEval (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  grind [DenseExpr.constValue?, DenseExpr.eval]

/-- `denseEqExpr e₂ e₁` evaluates to `e₂ − e₁`. -/
theorem denseEqExpr_eval (e2 e1 : DenseExpr p) (denv : VarId → ZMod p) :
    (denseEqExpr e2 e1).eval denv = e2.eval denv - e1.eval denv := by
  show e2.eval denv + (-1) * e1.eval denv = _
  ring

theorem denseAddrConstsEq_sound (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p))
    (h : denseAddrConstsEq shape S S' = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) = shape.address (denseBIEval S' denv) := by
  unfold MemoryBusShape.address
  apply List.map_congr_left
  intro slot hslot
  have hs := List.all_eq_true.mp h slot hslot
  show (S.payload.map (fun e => e.eval denv))[slot]?
    = (S'.payload.map (fun e => e.eval denv))[slot]?
  grind [denseConstValueEval]

theorem denseAddrConstsNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (h : denseAddrConstsNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  grind [denseAddrConstsNeq, denseConstValueEval, denseAddr_slot_neq]

end ApcOptimizer.Dense
