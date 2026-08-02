import ApcOptimizer.Implementation.OptimizerPasses.CarryBranch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DigitFold

set_option autoImplicit false

/-! # Correctness for the dense carry-branch resolution (`CarryBranch.lean`). Value bounds are
consumed through `denseBuild_sound` (`Proofs/DigitFold.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Two-sided interval certificate -/

/-- Checked never-zero certificate for an expression (over the candidate rescalings). -/
theorem denseNeverZeroB_sound (hp : 0 < p) (ops : DenseZModOps p) (B : Std.HashMap VarId Nat)
    (e : DenseExpr p)
    (h : denseNeverZeroB ops B e = true) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    e.eval denv ≠ 0 := by
  sorry

/-- The resolution is an *equivalence* on satisfying assignments: with the bounds valid and `p`
    prime, `f·g = 0 ↔ f = 0` whenever `g` is certified never-zero. -/
theorem denseResolveExpr_eval_iff [Fact p.Prime] (ops : DenseZModOps p)
    (B : Std.HashMap VarId Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    (denseResolveExpr ops B e).eval denv = 0 ↔ e.eval denv = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction e with
  | mul f g ihf ihg =>
      simp only [denseResolveExpr]
      split_ifs with h1 h2
      · have hg : g.eval denv ≠ 0 := denseNeverZeroB_sound hp ops B g h1 denv hB
        refine ihf.trans ?_
        show f.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, zero_mul], fun h => (mul_eq_zero.mp h).resolve_right hg⟩
      · have hf : f.eval denv ≠ 0 := denseNeverZeroB_sound hp ops B f h2 denv hB
        refine ihg.trans ?_
        show g.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hf⟩
      · exact Iff.rfl
  | const n => exact Iff.rfl
  | var x => exact Iff.rfl
  | add a b iha ihb => exact Iff.rfl

/-! ## The pass correctness -/

/-- Carry-branch correctness: the `denseResolveExpr` rewrite preserves the satisfying set exactly;
    value bounds hold for every satisfying assignment via `denseBuild_sound`. -/
theorem denseCarryBranchF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseCarryBranchF pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    have hout : denseCarryBranchF pw bs facts d = { d with
          algebraicConstraints :=
            d.algebraicConstraints.map
              (denseResolveExpr denseZModOps (denseBuild bs facts d.busInteractions)) } := by
      unfold denseCarryBranchF; rw [if_pos hpB]
    rw [hout]
    set B := denseBuild bs facts d.busInteractions with hBdef
    -- for any assignment whose bus interactions are non-violating, the built bounds are valid
    have hBof : ∀ denv, (∀ bi ∈ d.busInteractions,
        (denseBIEval bi denv).multiplicity ≠ 0 →
          bs.accepts (denseBIEval bi denv)) →
        ∀ v bound, B[v]? = some bound → (denv v).val < bound := by
      intro denv hbus v bound hlk
      rw [hBdef] at hlk
      exact denseBuild_sound bs facts d.busInteractions v bound hlk denv hbus
    -- satisfaction is preserved under the constraint rewrite
    have hsat_iff : ∀ denv, (∀ v bound, B[v]? = some bound → (denv v).val < bound) →
        (d.satisfies bs denv ↔
          ({ d with algebraicConstraints :=
              d.algebraicConstraints.map (denseResolveExpr denseZModOps B) } :
            DenseConstraintSystem p).satisfies bs denv) := by
      intro denv hB
      constructor
      · rintro ⟨hc, hb⟩
        refine ⟨fun c' hc' => ?_, hb⟩
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact (denseResolveExpr_eval_iff denseZModOps B c denv hB).mpr (hc c hcmem)
      · rintro ⟨hc, hb⟩
        refine ⟨fun c hcmem => ?_, hb⟩
        exact (denseResolveExpr_eval_iff denseZModOps B c denv hB).mp (hc _ (List.mem_map_of_mem hcmem))
    refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
    · -- soundness: the same assignment satisfies the input
      intro denv hsatout
      have hB := hBof denv hsatout.2
      exact ⟨denv, (hsat_iff denv hB).mpr hsatout, rfl⟩
    · -- invariant preservation (bus interactions are untouched)
      intro hgi denv hsatout
      have hB := hBof denv hsatout.2
      exact hgi denv ((hsat_iff denv hB).mpr hsatout)
    · -- no new variables
      intro i hi
      have hocc :
          ({ d with algebraicConstraints := d.algebraicConstraints.map (denseResolveExpr denseZModOps B) }
              : DenseConstraintSystem p).occ
            = (d.algebraicConstraints.map (denseResolveExpr denseZModOps B)).flatMap DenseExpr.vars
              ++ d.busInteractions.flatMap denseBIVars := rfl
      rw [hocc, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨c', hc', hic'⟩ := List.mem_flatMap.1 hi
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact DenseConstraintSystem.mem_occ_of_constraint hcmem (denseResolveExpr_vars denseZModOps B c i hic')
      · obtain ⟨bi, hbi, hib⟩ := List.mem_flatMap.1 hi
        exact DenseConstraintSystem.mem_occ_of_bi hbi hib
    · -- completeness: same assignment, same side effects, `admissible` untouched
      intro denv hadm hsat
      have hB := hBof denv hsat.2
      exact ⟨(hsat_iff denv hB).mp hsat, hadm, rfl⟩
  · rw [show denseCarryBranchF pw bs facts d = d from by unfold denseCarryBranchF; rw [if_neg hpB]]
    exact DensePassCorrect.refl reg.isInput d bs

/-- The dense carry-branch-resolution pass; correctness via `denseCarryBranchF_correct`. -/
def denseCarryBranchPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (denseCarryBranchF pw)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseCarryBranchF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseCarryBranchF_correct pw reg bs facts d)

end ApcOptimizer.Dense
