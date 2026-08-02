import ApcOptimizer.Implementation.OptimizerPasses.FlagFold
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagFoldDrops

set_option autoImplicit false

/-! # Soundness for the dense `flagFold` pass

`denseFlagFoldF` (`FlagFold.lean`) runs four transforms over one shared finite-domain table, so the
whole proof is the four existing arguments composed with `DensePassCorrect.trans` plus what makes
the table admissible:

* `ffSole_vars` — the scalar walk only reports single-variable constraints;
* `ffBucketsOf_mem` — every bucket holds single-variable constraints of the system;
* `ffTabGet_eq` — every table entry is its own bucket's `denseFindDomainAlg` verdict.

Part C's gate is an equality, not a new certificate (`ffBtCert_eq`: it rejects on `denseBtCert`'s
own cheapest conjunct first). Part B's gate needs no lemma at all — below the bound the pass
returns its input unchanged. Part D's sweep is a proposal generator re-verified by `densePdKeep`,
so it carries no obligation either. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The single-variable walk -/

/-- The walk's invariant: `0` means nothing seen, `1` is uninformative, `i + 2` means at least one
    variable was seen and every one of them is `⟨i⟩`. -/
def FfSoleInv (s : Nat) (l : List VarId) : Prop :=
  (s = 0 → l = []) ∧ (2 ≤ s → l ≠ [] ∧ ∀ y ∈ l, y.index + 2 = s)

theorem ffSoleGo_inv (e : DenseExpr p) :
    ∀ s acc, FfSoleInv s acc → FfSoleInv (ffSoleGo e s) (acc ++ e.vars) := by
  induction e with
  | const n => intro s acc h; simpa [ffSoleGo, DenseExpr.vars] using h
  | var i =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h0 : (s == 0) = true
      · have hs0 : s = 0 := by simpa using h0
        have hacc : acc = [] := h.1 hs0
        subst hacc
        rw [if_pos h0]
        refine ⟨by omega, fun _ => ⟨by simp, ?_⟩⟩
        intro y hy
        simp only [List.nil_append, List.mem_singleton] at hy
        subst hy; rfl
      · rw [if_neg h0]
        by_cases h1 : (s == i.index + 2) = true
        · have hsi : s = i.index + 2 := by simpa using h1
          rw [if_pos h1]
          refine ⟨by omega, fun _ => ⟨by simp, ?_⟩⟩
          intro y hy
          rcases List.mem_append.1 hy with hy' | hy'
          · by_cases hacc : acc = []
            · subst hacc; simp at hy'
            · exact (h.2 (by omega)).2 y hy'
          · simp only [List.mem_singleton] at hy'; subst hy'; exact hsi.symm
        · rw [if_neg h1]
          exact ⟨by omega, by omega⟩
  | add a b iha ihb =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h1 : (ffSoleGo a s == 1) = true
      · rw [if_pos h1]; exact ⟨by omega, by omega⟩
      · rw [if_neg h1, ← List.append_assoc]
        exact ihb _ _ (iha _ _ h)
  | mul a b iha ihb =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h1 : (ffSoleGo a s == 1) = true
      · rw [if_pos h1]; exact ⟨by omega, by omega⟩
      · rw [if_neg h1, ← List.append_assoc]
        exact ihb _ _ (iha _ _ h)

/-- A nonempty list all of whose elements are `v` deduplicates to `[v]`. -/
theorem eraseDups_of_all_eq {v : VarId} :
    ∀ (l : List VarId), l ≠ [] → (∀ y ∈ l, y = v) → l.eraseDups = [v] := by
  intro l hne hall
  match l with
  | [] => exact absurd rfl hne
  | a :: as =>
      have ha : a = v := hall a (by simp)
      subst ha
      rw [List.eraseDups_cons]
      have hnil : as.filter (fun b => !b == a) = [] := by
        refine List.filter_eq_nil_iff.2 (fun b hb => ?_)
        rw [hall b (by simp [hb])]
        simp
      rw [hnil]
      rfl

/-- `ffSole` only reports genuinely single-variable expressions. -/
theorem ffSole_vars {c : DenseExpr p} {v : VarId} (h : ffSole c = some v) :
    c.vars.eraseDups = [v] := by
  unfold ffSole at h
  by_cases hs : 2 ≤ ffSoleGo c 0
  · rw [if_pos hs] at h
    have hv : v = ⟨ffSoleGo c 0 - 2⟩ := by
      simp only [Option.some.injEq] at h; exact h.symm
    have hinv := ffSoleGo_inv c 0 [] ⟨fun _ => rfl, by omega⟩
    obtain ⟨hne, hall⟩ := hinv.2 hs
    rw [List.nil_append] at hne hall
    refine eraseDups_of_all_eq c.vars hne (fun y hy => ?_)
    have := hall y hy
    rw [hv]
    exact congrArg VarId.mk (by omega)
  · rw [if_neg hs] at h; exact absurd h (by simp)

/-- A constraint the walk accepts is one of the system's single-variable constraints. -/
theorem ffSole_mem_singleVarCs {cs : List (DenseExpr p)} {c : DenseExpr p} {v : VarId}
    (hc : c ∈ cs) (h : ffSole c = some v) : c ∈ denseSingleVarCs cs := by
  refine List.mem_filter.2 ⟨hc, ?_⟩
  rw [HashedDedup.hashedEraseDups_eq, ffSole_vars h]
  rfl

/-! ## The bucket array -/

theorem ffGetD_set!_cases {α : Type} (B : Array α) (j : Nat) (y d : α) (i : Nat) :
    (B.set! j y).getD i d = y ∨ (B.set! j y).getD i d = B.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  show ((B.setIfInBounds j y)[i]?).getD d = y ∨ ((B.setIfInBounds j y)[i]?).getD d = (B[i]?).getD d
  rw [Array.getElem?_setIfInBounds]
  by_cases hij : j = i
  · subst hij
    by_cases hj : j < B.size
    · rw [if_pos rfl, if_pos hj]; exact Or.inl rfl
    · rw [if_pos rfl, if_neg hj]
      refine Or.inr ?_
      rw [Array.getElem?_eq_none (by omega)]
  · rw [if_neg hij]; exact Or.inr rfl

/-- Every constraint in every bucket is a single-variable constraint of the source list. -/
theorem ffBucketsOf_mem (cs : List (DenseExpr p)) (v : VarId) (c : DenseExpr p)
    (h : c ∈ ffBucketOf (ffBucketsOf cs) v) : c ∈ denseSingleVarCs cs := by
  unfold ffBucketsOf ffBucketOf at h
  suffices hgen : ∀ (l : List (DenseExpr p)) (B : Array (List (DenseExpr p))),
      (∀ i, ∀ c' ∈ B.getD i [], c' ∈ denseSingleVarCs cs) →
      (∀ c' ∈ l, c' ∈ cs) →
      ∀ i, ∀ c' ∈ (l.foldr (fun c B =>
        match ffSole c with
        | some w => B.set! w.index (c :: B.getD w.index [])
        | none => B) B).getD i [], c' ∈ denseSingleVarCs cs from
    hgen cs _ (fun i c' hc' => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hc'
      split at hc' <;> simp at hc') (fun _ h => h) v.index c h
  intro l
  induction l with
  | nil => intro B hB _ i c' hc'; exact hB i c' hc'
  | cons a rest ih =>
      intro B hB hmem i c' hc'
      rw [List.foldr_cons] at hc'
      have hrest := ih B hB (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      cases hsole : ffSole a with
      | none => rw [hsole] at hc'; exact hrest i c' hc'
      | some w =>
          rw [hsole] at hc'
          rcases ffGetD_set!_cases (α := List (DenseExpr p)) _ w.index
            (a :: (rest.foldr _ B).getD w.index []) [] i with heq | heq
          · rw [heq] at hc'
            rcases List.mem_cons.1 hc' with heqa | hc''
            · exact heqa ▸ ffSole_mem_singleVarCs (hmem a (List.mem_cons_self ..)) hsole
            · exact hrest w.index c' hc''
          · rw [heq] at hc'; exact hrest i c' hc'

/-! ## The domain table -/

/-- Every table entry is its own bucket's `denseFindDomainAlg` verdict. -/
theorem ffTabGet_eq (B : Array (List (DenseExpr p))) (v : VarId) :
    ffTabGet (ffTabOf B) v = denseFindDomainAlg (ffBucketOf B v) v := by
  unfold ffTabGet ffTabOf ffBucketOf
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases hv : v.index < B.size
  · rw [Array.getElem?_eq_getElem (by rw [Array.size_mapFinIdx]; exact hv),
        Array.getElem?_eq_getElem hv, Array.getElem_mapFinIdx]
    rfl
  · rw [Array.getElem?_eq_none (by rw [Array.size_mapFinIdx]; omega),
        Array.getElem?_eq_none (by omega)]
    rfl

/-- The domains the fused pass reports are justified by their own buckets. -/
theorem ffTab_domOf (cs : List (DenseExpr p)) (v : VarId) (dm : List (ZMod p))
    (h : ffTabGet (ffTabOf (ffBucketsOf cs)) v = some dm) :
    denseFindDomainAlg (ffBucketOf (ffBucketsOf cs) v) v = some dm := by
  rwa [ffTabGet_eq] at h

/-! ## Part C's gate -/

theorem ffAllBoxed_false {T : FfTab p} :
    ∀ (c : DenseExpr p), ffAllBoxed T c = false → ∃ v ∈ c.vars, ffTabGet T v = none := by
  intro c
  induction c with
  | const n => intro h; simp [ffAllBoxed] at h
  | var i =>
      intro h
      refine ⟨i, by simp [DenseExpr.vars], ?_⟩
      simp only [ffAllBoxed, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      exact h
  | add a b iha ihb =>
      intro h
      simp only [ffAllBoxed, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨v, hv, hd⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
      · obtain ⟨v, hv, hd⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
  | mul a b iha ihb =>
      intro h
      simp only [ffAllBoxed, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨v, hv, hd⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
      · obtain ⟨v, hv, hd⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩

/-- The gate is one of `denseBtCert`'s own conjuncts: a variable without a domain breaks the
    `doms.map Prod.fst = vs` cover test. -/
theorem ffBtCert_eq (T : FfTab p) (c : DenseExpr p) :
    ffBtCert T c = denseBtCert (ffTabGet T) c := by
  unfold ffBtCert
  by_cases hg : ffAllBoxed T c = true
  · rw [hg, Bool.true_and]
  · rw [Bool.not_eq_true] at hg
    rw [hg, Bool.false_and]
    obtain ⟨v, hv, hd⟩ := ffAllBoxed_false c hg
    unfold denseBtCert
    rw [HashedDedup.hashedEraseDups_eq]
    have hcover : (decide ((c.vars.eraseDups.filterMap (fun w =>
        (ffTabGet T w).map (fun dm => (w, dm)))).map Prod.fst = c.vars.eraseDups)) = false := by
      simp only [decide_eq_false_iff_not]
      intro hc
      have hvm : v ∈ (c.vars.eraseDups.filterMap (fun w =>
          (ffTabGet T w).map (fun dm => (w, dm)))).map Prod.fst := by
        rw [hc]; exact List.mem_eraseDups.2 hv
      obtain ⟨pr, hpr, hfst⟩ := List.mem_map.1 hvm
      obtain ⟨w, _hw, hwe⟩ := List.mem_filterMap.1 hpr
      cases hdw : ffTabGet T w with
      | none => rw [hdw] at hwe; simp at hwe
      | some dm =>
          rw [hdw] at hwe
          simp only [Option.map_some, Option.some.injEq] at hwe
          rw [← hwe] at hfst
          simp only at hfst
          rw [hfst] at hdw
          rw [hd] at hdw
          exact absurd hdw (by simp)
    simp [hcover]

theorem ffBoxTauto_eq (d : DenseConstraintSystem p) (T : FfTab p) :
    d.ffBoxTauto T = d.boxTautoReplaceWith (ffTabGet T) := by
  unfold DenseConstraintSystem.ffBoxTauto DenseConstraintSystem.boxTautoReplaceWith
  refine congrArg (fun l => { d with algebraicConstraints := l }) ?_
  exact List.map_congr_left (fun c _ => by rw [ffBtCert_eq])

/-! ## Part D -/

theorem ffPdDropWith_covered {reg : VarRegistry} (bs : BusSemantics p)
    (d : DenseConstraintSystem p)
    (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) (hcov : d.CoveredBy reg) :
    (ffPdDropWith bs d drops).CoveredBy reg := by
  unfold ffPdDropWith
  split_ifs with hE
  · exact hcov
  · exact DenseConstraintSystem.filterBus_covered hcov

theorem ffPdDropWith_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p)
    (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) :
    DensePassCorrect isInput d (ffPdDropWith bs d drops) [] bs := by
  unfold ffPdDropWith
  split_ifs with hE
  · exact DensePassCorrect.refl isInput d bs
  · refine DensePassCorrect.densePointwiseDupDrop d bs isInput _ ?_
    intro bi _ hkf
    exact densePdVerdictKeep_false _ bi hkf

/-! ## The fused pass -/

theorem denseFlagFoldF_covered (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) : (denseFlagFoldF pw b bs facts d).CoveredBy reg := by
  unfold denseFlagFoldF
  split_ifs with hp
  · refine ffPdDropWith_covered bs _ _ ?_
    rw [ffBoxTauto_eq]
    refine DenseConstraintSystem.boxTautoReplaceWith_covered _ ?_
    split_ifs with hover
    · exact DenseConstraintSystem.boxRewrite_covered _ b
        (denseFxSubstF_covered pw reg bs facts d hcov)
    · exact denseFxSubstF_covered pw reg bs facts d hcov
  · exact hcov

theorem denseFlagFoldF_correct (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseFlagFoldF pw b bs facts d) [] bs := by
  unfold denseFlagFoldF
  split_ifs with hp
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    set d1 := denseFxSubstF pw bs facts d with hd1
    have hA : DensePassCorrect reg.isInput d d1 [] bs :=
      denseFxSubstF_correct pw reg bs facts d hcov
    set d2 := (if ffAnyOverBound b d1
      then d1.boxRewriteWith (ffTabGet (ffTabOf (ffBucketsOf d1.algebraicConstraints))) b
      else d1) with hd2
    have hB : DensePassCorrect reg.isInput d1 d2 [] bs := by
      rw [hd2]
      split_ifs with hover
      · exact DenseConstraintSystem.boxRewrite_denseCorrect d1 bs reg.isInput
          (ffBucketOf (ffBucketsOf d1.algebraicConstraints))
          (fun v c hc => ffBucketsOf_mem d1.algebraicConstraints v c hc)
          _ (fun v dm hv => ffTab_domOf d1.algebraicConstraints v dm hv) b
      · exact DensePassCorrect.refl reg.isInput d1 bs
    have hC : DensePassCorrect reg.isInput d2
        (d2.ffBoxTauto (ffTabOf (ffBucketsOf d2.algebraicConstraints))) [] bs := by
      rw [ffBoxTauto_eq]
      exact DenseConstraintSystem.boxTautoReplace_denseCorrect d2 bs reg.isInput
        (ffBucketOf (ffBucketsOf d2.algebraicConstraints))
        (fun v c hc => ffBucketsOf_mem d2.algebraicConstraints v c hc)
        _ (fun v dm hv => ffTab_domOf d2.algebraicConstraints v dm hv)
    exact (hA.trans hB).trans
      (hC.trans (ffPdDropWith_correct bs reg.isInput _ _))
  · exact DensePassCorrect.refl reg.isInput d bs

/-- The dense `flagFold` pass: substitute entailed nonlinear interpolations, rewrite over-bound
    survivors multilinearly, drop box tautologies and pointwise stateless-check duplicates.
    Unguarded here — box-rewrite intermediates legitimately exceed the bound — so the whole chain
    runs under ONE `guardDegree b` at its `cleanupPasses` entry. -/
def denseFlagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of (denseFlagFoldF pw b) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseFlagFoldF_covered pw b reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseFlagFoldF_correct pw b reg bs facts d hcov)

end ApcOptimizer.Dense
