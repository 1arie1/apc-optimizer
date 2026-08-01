import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchFast
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # The rebuilt domain-batch pass (PROTOTYPE: entailment `sorry`ed)

Wiring only. `dbDomainBatchσ_entailed` is the one obligation the engine owes; it is `sorry`ed here
while the runtime half is measured (`OptimizingRuntime.md` → *Sizing a win before proving it*). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

theorem dbDomainBatchσ_entailed [Fact p.Prime] [NeZero p]
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    EntailedMap d bs (dbDomainBatchσ bs facts d).map := by
  sorry

theorem dbApplyσ_eq (dσ : DenseSolved p) (d : DenseConstraintSystem p) :
    dbApplyσ dσ d = applyσ dσ d := by
  sorry

theorem dbDomainBatchTransform_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    (dbDomainBatchTransform pw bs facts d).CoveredBy reg := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d = applyσ (dbDomainBatchσ bs facts d) d
        from by simp only [dbDomainBatchTransform, if_pos hpB, dbApplyσ_eq], applyσ]
    by_cases he : (dbDomainBatchσ bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact hcov
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_covered hcov (fun i _ t ht z hz => ?_)
      exact DenseConstraintSystem.occ_valid hcov z
        ((dbDomainBatchσ_entailed bs facts d i t ht).1 z hz)
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact hcov

theorem dbDomainBatchTransform_correct (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (dbDomainBatchTransform pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d = applyσ (dbDomainBatchσ bs facts d) d
        from by simp only [dbDomainBatchTransform, if_pos hpB, dbApplyσ_eq], applyσ]
    by_cases he : (dbDomainBatchσ bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact DensePassCorrect_refl reg.isInput d bs
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_denseCorrect d (dbDomainBatchσ bs facts d).fn bs
        reg.isInput (fun denv hsat j t hjt => ?_) (fun j t hjt z hz => ?_)
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).2 denv hsat
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).1 z hz
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact DensePassCorrect_refl reg.isInput d bs

/-- The rebuilt domain-batch pass (see `dbDomainBatchσ`). -/
def dbDomainBatchPass (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := dbDomainBatchTransform pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := dbDomainBatchTransform_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := DensePassCorrect.lift hcov
      (dbDomainBatchTransform_covered pw reg bs facts d hcov) (by intro x hx; simp at hx)
      (dbDomainBatchTransform_correct pw reg bs facts d) }

end ApcOptimizer.Dense
