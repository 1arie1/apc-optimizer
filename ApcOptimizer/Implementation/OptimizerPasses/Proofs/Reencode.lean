import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DropPasses

set_option autoImplicit false

/-! # Witness re-encoding — correctness.

The full `DensePassCorrect` proof for the `Reencode` pass over dense environments `VarId → ZMod p`:
structure lemmas, the transport core `DenseConstraintSystem.reencode_correct_D`, the capstone
`denseCheckReencode_sound`, and the step/loop/pass assembly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- On the keys, `denseEnvExt` agrees with `denseEnvOfFast`. -/
theorem denseEnvExt_eq_envOfFast_of_mem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∈ pairs.map Prod.fst) : denseEnvExt pairs denv y = denseEnvOfFast pairs y := by
  induction pairs with
  | nil => simp at h
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [denseEnvExt, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos hyx, if_pos (by simp [hyx])]
    · rw [if_neg hyx, if_neg (by simpa using hyx)]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hyx
      · exact h

/-- Off the keys, `denseEnvExt` is `denv`. -/
theorem denseEnvExt_eq_env_of_notmem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∉ pairs.map Prod.fst) : denseEnvExt pairs denv y = denv y := by
  induction pairs with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [denseEnvExt, if_neg h.1]
    exact ih h.2

theorem denseMentions_false_not_mem_vars (i : VarId) (e : DenseExpr p)
    (h : e.mentions i = false) : i ∉ e.vars := by
  induction e with
  | const n => simp [DenseExpr.vars]
  | var j =>
      simp only [DenseExpr.mentions] at h
      simp only [DenseExpr.vars, List.mem_singleton]
      intro hij
      subst hij
      simp at h
  | add a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx
  | mul a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx

theorem DenseExpr.evalWith_eq (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (denv : VarId → ZMod p) (e : DenseExpr p) : e.evalWith add mul denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hadd, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hmul, iha, ihb]

theorem DenseExpr.evalFast_eq (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.evalFast denv = e.eval denv :=
  DenseExpr.evalWith_eq zmodAdd zmodMul (fun _ _ => zmodAdd_eq _ _) (fun _ _ => zmodMul_eq _ _)
    denv e

theorem denseBoolConstraint_eval_of_bool (b : VarId) (denv : VarId → ZMod p)
    (h : denv b = 0 ∨ denv b = 1) : (denseBoolConstraint b).eval denv = 0 := by
  show denv b * (denv b + (-1)) = 0
  rcases h with h | h <;> rw [h] <;> ring

theorem dense_bool_of_boolConstraint_eval [Fact p.Prime] (b : VarId) (denv : VarId → ZMod p)
    (h : (denseBoolConstraint b).eval denv = 0) : denv b = 0 ∨ denv b = 1 := by
  have h' : denv b * (denv b + (-1)) = 0 := h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    linear_combination h1

/-- Every enumerated assignment has the domains' keys, in order. -/
theorem denseAssignments_keys (doms : List (VarId × List (ZMod p)))
    (a : List (VarId × ZMod p)) (h : a ∈ denseAssignments doms) :
    a.map Prod.fst = doms.map Prod.fst := by
  induction doms generalizing a with
  | nil =>
      simp only [denseAssignments, List.mem_singleton] at h
      subst h
      rfl
  | cons xd rest ih =>
    obtain ⟨x, d⟩ := xd
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp [ih a' ha']

/-- Every enumerated assignment's value at a (distinct-keyed) domain entry lies in that domain. -/
theorem denseEnvOf_mem_of_assignments (doms : List (VarId × List (ZMod p)))
    (hnd : (doms.map Prod.fst).Nodup) (a : List (VarId × ZMod p))
    (h : a ∈ denseAssignments doms) : ∀ xd ∈ doms, denseEnvOfFast a xd.1 ∈ xd.2 := by
  induction doms generalizing a with
  | nil => simp
  | cons xd0 rest ih =>
    obtain ⟨x, d⟩ := xd0
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at hnd
    intro yd hyd
    rcases List.mem_cons.1 hyd with rfl | hyd
    · rw [denseEnvOfFast, if_pos (show (x == x) = true by simp)]
      exact hv
    · have hne : yd.1 ≠ x := by
        intro heq
        exact hnd.1 (heq ▸ List.mem_map.2 ⟨yd, hyd, rfl⟩)
      have hbf : (yd.1 == x) = false := beq_eq_false_iff_ne.mpr hne
      rw [denseEnvOfFast, if_neg (by simp [hbf])]
      exact ih hnd.2 a' ha' yd hyd

/-- `denseEnvOfFast` of a zipped image list reads off the image function. -/
theorem denseEnvOf_zipimg (xs : List VarId) (g : VarId → ZMod p) (y : VarId) (hy : y ∈ xs) :
    denseEnvOfFast (xs.map (fun x => (x, g x))) y = g y := by
  induction xs with
  | nil => simp at hy
  | cons x rest ih =>
    simp only [List.map_cons, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos (by simp [hyx]), hyx]
    · rw [if_neg (by simp [hyx])]
      exact ih (by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h hyx
        · exact h)

/-- `denseEnvF` at any variable is the evaluation of the substituted variable expression. -/
theorem denseEnvF_eq_varSubst (σ : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p)
    (y : VarId) : denseEnvF σ denv y = ((DenseExpr.var y).substF σ).eval denv := by
  show (match σ y with | some t => t.eval denv | none => denv y)
    = ((match σ y with | some t => t | none => .var y) : DenseExpr p).eval denv
  cases σ y <;> rfl

/-- Expression-level agreement from pointwise environment agreement. -/
theorem denseSubstF_eval_agree (σ : VarId → Option (DenseExpr p)) (denv₀ denv₁ : VarId → ZMod p)
    (e : DenseExpr p) (h : ∀ y ∈ e.vars, denseEnvF σ denv₀ y = denv₁ y) :
    (e.substF σ).eval denv₀ = e.eval denv₁ := by
  rw [DenseExpr.eval_substF]
  exact DenseExpr.eval_congr e _ _ h

theorem denseContainsFast_of_mem (xs : List VarId) (y : VarId) (h : y ∈ xs) :
    denseContainsFast xs y = true := by
  induction xs with
  | nil => simp at h
  | cons x rest ih =>
    simp only [denseContainsFast, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (by simp)
    · exact Or.inr (ih h)

/-- Substituting a wholly-in-group expression (whose group variables `σfn` maps into the bits)
    yields an expression over the bits only. -/
theorem DenseExpr.substF_varsIn_bits (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (e.substF σfn).vars, v ∈ bits := by
  induction e with
  | const n => intro v hv; simp [DenseExpr.substF, DenseExpr.vars] at hv
  | var y =>
      intro v hv
      exact hσ y (denseContainsFast_sound xs y (by simpa [DenseExpr.varsInF] using hin)) v hv
  | add a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv
  | mul a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv

/-- Interpolation candidate agreement: on a bit pattern that agrees with `denv₀` and off which the
    substitution map matches `denv₁`, the checked interpolation candidate evaluates as the
    original. -/
theorem denseGroupRewriteCand_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hin : e.varsInF xs = true)
    (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewriteCand bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  have hnotbits : ∀ y ∈ e.vars, y ∉ bits := by
    intro y hy hyb
    exact absurd hy (denseMentions_false_not_mem_vars y e (hfresh y hyb))
  have hsubstF : (e.substF σfn).eval denv₀ = e.eval denv₁ := by
    rw [DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    exact hpoint y (hnotbits y hy)
  simp only [denseGroupRewriteCand]
  unfold denseCandSelect
  split
  · next hchk =>
    rw [Bool.and_eq_true] at hchk
    have hβ := of_decide_eq_true (List.all_eq_true.mp hchk.2 _
      (zip_map_self_mem (fun aβ => (e.substF σfn).evalFast (denseEnvOfFast aβ)) patts aβ haβ))
    have hchk1 := hchk.1
    simp only [DenseExpr.evalFast_eq] at hβ hchk1 ⊢
    have hcvars : ∀ v ∈ ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).vars, v ∈ bits :=
      denseVarsInF_sound bits _ hchk1
    have h₀β : ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval denv₀
        = ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval (denseEnvOfFast aβ) := by
      apply DenseExpr.eval_congr
      intro v hv
      exact hbitsagree v (hcvars v hv)
    rw [h₀β, hβ, DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    have hyx : y ∈ xs := denseVarsInF_sound xs e hin y hy
    rw [denseEnvF_eq_varSubst]
    have hstep : ((DenseExpr.var y).substF σfn).eval (denseEnvOfFast aβ)
        = ((DenseExpr.var y).substF σfn).eval denv₀ := by
      apply DenseExpr.eval_congr
      intro v hv
      exact (hbitsagree v (hpolyvars y hyx v hv)).symm
    rw [hstep, ← denseEnvF_eq_varSubst]
    exact hpoint y (hnotbits y hy)
  · exact hsubstF

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else, agreeing pointwise with the original. -/
theorem denseGroupRewrite_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewrite xs bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) hfresh
      · rw [if_neg hyx]
        have hyxs : y ∉ xs := fun h => hyx (denseContainsFast_of_mem xs y h)
        have hynb : y ∉ bits := by
          intro hyb
          have := hfresh y hyb
          simp [DenseExpr.mentions] at this
        have := hpoint y hynb
        unfold denseEnvF at this
        rw [hσnone y hyxs] at this
        show (DenseExpr.var y).eval denv₀ = (DenseExpr.var y).eval denv₁
        exact this
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.add a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          + ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ + b.eval denv₁
        rw [iha hfa, ihb hfb]
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.mul a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          * ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ * b.eval denv₁
        rw [iha hfa, ihb hfb]

/-- Bus-interaction-level agreement for the group rewrite, over the field-by-field inlined rewrite
    that `denseReencodeOut` produces (there is no dense `BusInteraction.mapExpr`). -/
theorem denseGroupRewrite_bi_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (bi : BusInteraction (DenseExpr p))
    (hfreshM : ∀ b ∈ bits, bi.multiplicity.mentions b = false)
    (hfreshP : ∀ e ∈ bi.payload, ∀ b ∈ bits, e.mentions b = false) :
    denseBIEval { bi with
        multiplicity := denseGroupRewrite xs bits σfn patts bi.multiplicity,
        payload := bi.payload.map (denseGroupRewrite xs bits σfn patts) } denv₀
      = denseBIEval bi denv₁ := by
  unfold denseBIEval
  congr 1
  · exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint bi.multiplicity hfreshM
  · rw [List.map_map]
    refine List.map_congr_left (fun e he => ?_)
    simp only [Function.comp_apply]
    exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint e (hfreshP e he)

/-- A rewritten wholly-in-group expression is over the bits only. -/
theorem denseGroupRewriteCand_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (denseGroupRewriteCand bits σfn patts e).vars, v ∈ bits := by
  intro v hv
  simp only [denseGroupRewriteCand] at hv
  unfold denseCandSelect at hv
  split at hv
  · next hchk =>
      rw [Bool.and_eq_true] at hchk
      exact denseVarsInF_sound bits _ hchk.1 v hv
  · exact DenseExpr.substF_varsIn_bits xs bits σfn hσ e hin v hv

/-- Every variable of a group-rewritten expression is either an original variable of `e` or a
    fresh bit. -/
theorem denseGroupRewrite_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) :
    ∀ v ∈ (denseGroupRewrite xs bits σfn patts e).vars, v ∈ e.vars ∨ v ∈ bits := by
  induction e with
  | const n => simp [denseGroupRewrite, DenseExpr.vars]
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) v hv)
      · rw [if_neg hyx]; intro v hv; exact Or.inl hv
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.add a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.mul a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

/-- Every variable of the re-encoded system is either an original variable of `d` or a fresh bit —
    proven by construction from the certified substitution, so the pass needs no scan. -/
theorem denseReencodeOut_vars_subset (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits) :
    ∀ v ∈ (denseReencodeOut d xs bits hm).occ, v ∈ d.occ ∨ v ∈ bits := by
  intro v hv
  have gr := denseGroupRewrite_vars xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) hσ
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [denseReencodeOut, List.mem_append] at hc
    rcases hc with hc | hc
    · rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
      rcases gr c0 v hcv with h | h
      · exact Or.inl (DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc0) h)
      · exact Or.inr h
    · rcases List.mem_map.1 hc with ⟨b, hb, rfl⟩
      right
      have hvb : v = b := by simpa [denseBoolConstraint, DenseExpr.vars] using hcv
      exact hvb ▸ hb
  · simp only [denseReencodeOut, List.mem_map] at hbi
    rcases hbi with ⟨bi0, hbi0, rfl⟩
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hbiv
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · rcases gr bi0.multiplicity v hmv with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append]; exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
      rcases gr e0 v hev with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e0, he0, h⟩
      · exact Or.inr h

/-- A dense computation method reads only its variables. -/
theorem DenseComputationMethod.eval_congr (cm : DenseComputationMethod p) (e1 e2 : VarId → ZMod p) :
    (∀ v ∈ cm.vars, e1 v = e2 v) → cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => intro _; rfl
  | quotientOrZero num den =>
      intro h
      have hn : num.eval e1 = num.eval e2 :=
        DenseExpr.eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        DenseExpr.eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      intro h
      have hc : cond.eval e1 = cond.eval e2 :=
        DenseExpr.eval_congr cond _ _ (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hv)))
      have ht := iht (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hv)))
      have he := ihe (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hv))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, ht, he]

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`. -/
theorem denseMatchCM_eval (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) (denv : VarId → ZMod p) :
    (denseMatchCM xs imgFn thenM elseM).eval denv
    = if xs.all (fun x => decide (imgFn x = denv x)) then thenM.eval denv else elseM.eval denv := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show (DenseComputationMethod.ifEqZero _ (denseMatchCM rest imgFn thenM elseM) elseM).eval denv = _
      rw [DenseComputationMethod.eval]
      by_cases hx : imgFn x = denv x
      · rw [if_pos (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv = 0 by
              show denv x + -(imgFn x) = 0; rw [hx]; ring), ih, List.all_cons]
        simp [hx]
      · rw [if_neg (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv ≠ 0 by
              show denv x + -(imgFn x) ≠ 0; intro h; exact hx (by linear_combination -h)),
            List.all_cons]
        simp [hx]

/-- Variables of `denseMatchCM` lie in `xs` together with those of the branches. -/
theorem denseMatchCM_vars (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) :
    ∀ v ∈ (denseMatchCM xs imgFn thenM elseM).vars, v ∈ xs ∨ v ∈ thenM.vars ∨ v ∈ elseM.vars := by
  induction xs with
  | nil => intro v hv; exact Or.inr (Or.inl hv)
  | cons x rest ih =>
      intro v hv
      simp only [denseMatchCM, DenseComputationMethod.vars, DenseExpr.vars, List.nil_append,
        List.append_assoc, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | hv | hv
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih v hv with h | h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr hv)

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
theorem denseBitCM_eval (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) (denv : VarId → ZMod p) :
    (denseBitCM patts xs hm b).eval denv
    = match patts.find? (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
      | some aβ => denseEnvOfFast aβ b
      | none => 0 := by
  induction patts with
  | nil => rfl
  | cons aβ rest ih =>
      show (denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b)).eval denv = _
      rw [denseMatchCM_eval, List.find?_cons]
      by_cases hmatch : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true
      · rw [if_pos hmatch, hmatch]; rfl
      · rw [if_neg hmatch]
        simp only [hmatch, ih]

/-- The derivation of bit `b` reads only group variables. -/
theorem denseBitCM_vars (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) :
    ∀ v ∈ (denseBitCM patts xs hm b).vars, v ∈ xs := by
  induction patts with
  | nil => intro v hv; simp [denseBitCM, DenseComputationMethod.vars] at hv
  | cons aβ rest ih =>
      intro v hv
      rcases denseMatchCM_vars xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b) v hv with h | h | h
      · exact h
      · simp [DenseComputationMethod.vars] at h
      · exact ih v h

/-! ## Survivor enumeration -/

/-- Positional lookup at `y`'s first key position is exactly the `denseEnvOfFast` scan, on any
    assignment with the given keys. -/
theorem denseVarIx_lookup (keys : List VarId) (y : VarId) (i : Nat)
    (h : denseVarIx keys y = some i) (pt : List (VarId × ZMod p))
    (hpt : pt.map Prod.fst = keys) : denseLookupIx pt i = denseEnvOfFast pt y := by
  induction keys generalizing i pt with
  | nil => exact absurd h (by simp [denseVarIx])
  | cons x rest ih =>
    cases pt with
    | nil => exact absurd hpt (by simp)
    | cons xv pt' =>
      obtain ⟨x', v⟩ := xv
      simp only [List.map_cons, List.cons.injEq] at hpt
      obtain ⟨rfl, hpt'⟩ := hpt
      rw [denseVarIx] at h
      split_ifs at h with hfast
      · simp only [Option.some.injEq] at h
        subst h
        rw [denseLookupIx, denseEnvOfFast, if_pos hfast]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [denseLookupIx, denseEnvOfFast, if_neg hfast]
        exact ih j hj pt' hpt'

/-- Compiled keyed evaluation agrees with the source's keyed-environment evaluation. -/
theorem denseCompileE_eval (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (e : DenseExpr p) (ie : IExpr p) (h : denseCompileE keys e = some ie)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    denseIExprEvalWith add mul pt ie = e.eval (denseEnvOfFast pt) := by
  induction e generalizing ie with
  | const n => simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨i, hi, rfl⟩ := h
      show denseIExprEvalWith add mul pt (.ix i) = denseEnvOfFast pt y
      rw [denseIExprEvalWith]
      exact denseVarIx_lookup keys y i hi pt hpt
  | add a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show add (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) + b.eval (denseEnvOfFast pt)
          rw [hadd, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show mul (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) * b.eval (denseEnvOfFast pt)
          rw [hmul, iha ia ha, ihb ib hb]

/-- Compiled-list zero-check agrees with the source list's, keyed. -/
theorem denseCompileEs_all (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (keys : List VarId)
    (es : List (DenseExpr p)) (ces : List (IExpr p)) (h : denseCompileEs keys es = some ces)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    ces.all (fun ie => decide (denseIExprEvalWith add mul pt ie = 0))
      = es.all (fun c => decide (c.eval (denseEnvOfFast pt) = 0)) := by
  induction es generalizing ces with
  | nil => simp only [denseCompileEs, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    rw [denseCompileEs] at h
    cases he : denseCompileE keys e with
    | none => rw [he] at h; exact absurd h (by simp)
    | some ie =>
      cases hr : denseCompileEs keys rest with
      | none => rw [he, hr] at h; exact absurd h (by simp)
      | some irest =>
        rw [he, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [List.all_cons, List.all_cons, ih irest hr,
          denseCompileE_eval add mul hadd hmul keys e ie he pt hpt]

/-- `denseGroupSurvivorsE` computes the identical list to the direct `evalFast`/`denseEnvOfFast`
    filter — the index-compiled path is a pure speedup. -/
theorem denseGroupSurvivorsE_eq (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    denseGroupSurvivorsE es doms
      = (denseAssignments doms).filter
          (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0))) := by
  unfold denseGroupSurvivorsE
  split
  · rename_i ces hce
    refine List.filter_congr (fun a ha => ?_)
    have hkeys : a.map Prod.fst = doms.map Prod.fst := denseAssignments_keys doms a ha
    have hval : (fun c : DenseExpr p => decide (c.evalFast (denseEnvOfFast a) = 0))
        = (fun c : DenseExpr p => decide (c.eval (denseEnvOfFast a) = 0)) := by
      funext c; rw [DenseExpr.evalFast_eq]
    rw [hval]
    unfold denseSurvZeroCW
    exact denseCompileEs_all (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul
      (fun _ _ => rfl) (fun _ _ => rfl) (doms.map Prod.fst) es ces hce a hkeys
  · rfl

/-! ## The generic dense transport core

A witness transport principle producing `DensePassCorrect` directly from forward/backward transport
hypotheses. `out` replaces every expression by `grw`, keeps the constraints selected by `keep`, and
appends `newCs`; the fresh columns carry the derivations `dd`. Mentions neither bits nor groups. -/

theorem DenseConstraintSystem.reencode_correct_D (d out : DenseConstraintSystem p)
    (bs : BusSemantics p) (isInput : VarId → Bool)
    (grw : DenseExpr p → DenseExpr p) (keep : DenseExpr p → Bool)
    (newCs : List (DenseExpr p)) (dd : DenseDerivations p)
    (hout : out =
      { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
        busInteractions := d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) })
    (hfwd : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ newCs, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d out dd denv denv'))
    (hbwd : ∀ denv', out.satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0))
    (hVars : ∀ i ∈ out.occ, isInput i = true → i ∈ d.occ) :
    DensePassCorrect isInput d out dd bs := by
  subst hout
  -- side-effect equality under bus-interaction agreement
  have hside : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      DenseConstraintSystem.sideEffects
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' = d.sideEffects bs denv := by
    intro denv denv' hB
    refine funext (fun message => congrArg (multiplicitySum message) ?_)
    show ((d.busInteractions.map (fun bi =>
        { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).filter
        (fun bi => bs.isStateful bi.busId)).map _ = _
    rw [filter_map_busId_comm d.busInteractions
        (fun bi => { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })
        bs (fun _ => rfl), List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  -- admissible transfer under bus-interaction agreement
  have hdisc : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (DenseConstraintSystem.admissible
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' ↔ d.admissible bs denv) := by
    intro denv denv' hB
    unfold DenseConstraintSystem.admissible
    have hmap : ((d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).map
          (fun bi => denseBIEval bi denv'))
        = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
      rw [List.map_map]
      exact List.map_congr_left (fun bi hbi => hB bi hbi)
    rw [hmap]
  -- recover `d.satisfies denv` from a satisfying output and the backward agreement
  have hsatd : ∀ (denv denv' : VarId → ZMod p),
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) →
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0) →
      DenseConstraintSystem.satisfies
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' → d.satisfies bs denv := by
    intro denv denv' hA hB hdrop hsat'
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases hk : keep c = true
      · have hmem : grw c ∈ ((d.algebraicConstraints.filter keep).map grw) ++ newCs :=
          List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
        have h1 := hsat'.1 _ hmem
        rw [hA c hc] at h1; exact h1
      · exact hdrop c hc (by simpa using hk)
    · show (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)
      have hmem : { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }
          ∈ (d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })) :=
        List.mem_map.2 ⟨bi, hbi, rfl⟩
      have h2 := hsat'.2 _ hmem
      rw [hB bi hbi] at h2
      exact h2
  refine ⟨?_, ?_, hVars, ?_⟩
  · -- Soundness: `out.implies d`.
    intro denv' hsat'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    refine ⟨denv, hsatd denv denv' hA hB hdrop hsat', ?_⟩
    rw [hside denv denv' hB]
  · -- Invariant preservation.
    intro hinv denv' hsat' bi' hbi'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    have hd := hsatd denv denv' hA hB hdrop hsat'
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
      bs.maintainsInvariants (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv')
    rw [hB bi0 hbi0]
    exact hinv denv hd bi0 hbi0
  · -- Completeness with derivations.
    intro denv hadm hsat
    obtain ⟨denv', hA, hB, hnew, hframe, hrec⟩ := hfwd denv hsat
    refine ⟨denv', ⟨fun c hc => ?_, fun bi hbi => ?_⟩, (hdisc denv denv' hB).2 hadm, ?_, hframe, hrec⟩
    · rcases List.mem_append.1 hc with h | h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
        rw [hA c0 (List.mem_of_mem_filter hc0)]
        exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hnew c h
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
        bs.accepts (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv')
      rw [hB bi0 hbi0]
      exact hsat.2 bi0 hbi0
    · rw [hside denv denv' hB]

/-- The method list built for the fresh bits supplies `g w` for a bit `w`, nothing otherwise. -/
theorem DenseDerivations.methodFor_map (bits : List VarId) (g : VarId → DenseComputationMethod p)
    (w : VarId) :
    DenseDerivations.methodFor (bits.map (fun b => (b, g b))) w
      = if w ∈ bits then some (g w) else none := by
  induction bits with
  | nil => simp [DenseDerivations.methodFor]
  | cons b rest ih =>
      simp only [List.map_cons, DenseDerivations.methodFor, ih, List.mem_cons]
      by_cases hw : w ∈ rest
      · simp [hw]
      · by_cases hbw : b = w
        · subst hbw; simp [hw]
        · have hwb : w ≠ b := fun h => hbw h.symm
          simp [hw, hbw, hwb, Option.orElse]

/-! ## The capstone: certificate soundness

Supplies the forward transport (with the input-column frame and the `DenseOutReconstructs`
obligation for the minted bits) and the backward transport to
`DenseConstraintSystem.reencode_correct_D`. The freshness / `isInput` facts about the minted bits
and the group columns enter as abstract hypotheses, discharged in the step/loop section below. -/

theorem denseCheckReencode_sound [Fact p.Prime] (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (hxsInput : ∀ x ∈ xs, isInput x = true) (hxsOcc : ∀ x ∈ xs, x ∈ d.occ)
    (hxsB : ∀ x ∈ xs, x ∉ bits) (hbnInput : ∀ b ∈ bits, isInput b = false)
    (hchk : denseCheckReencode d xs bits hm = true) :
    DensePassCorrect isInput d (denseReencodeOut d xs bits hm)
      (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b))) bs := by
  unfold denseCheckReencode at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i doms hdoms
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨_hbox, _hm2⟩, _hprofit⟩, hnodup⟩, hvarsB⟩, hC5⟩, hC6⟩, hfreshB⟩ := hchk
  have hnodup' : bits.Nodup := of_decide_eq_true hnodup
  have hkeys : doms.map Prod.fst = xs := denseGroupDoms_fst (denseCoveredCsOf d xs) xs doms hdoms
  have hbitKeys : (denseBitBox (p := p) bits).map Prod.fst = bits := by
    unfold denseBitBox; rw [List.map_map]; simp [Function.comp_def]
  have hpolyVars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars,
      v ∈ bits := by
    intro y hy v hv
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hvarsB y hy) v hv)
  have hσnone : ∀ y, y ∉ xs → denseGroupSubst xs hm y = none := by
    intro y hy
    show (if denseContainsFast xs y = true then hm[y]? else none) = none
    rw [if_neg (fun h => hy (denseContainsFast_sound xs y h))]
  have hfreshCm : ∀ c ∈ d.algebraicConstraints, ∀ b ∈ bits, c.mentions b = false := by
    intro c hc b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    simpa using List.all_eq_true.mp h1.1 c hc
  have hfreshMm : ∀ bi ∈ d.busInteractions, ∀ b ∈ bits, bi.multiplicity.mentions b = false := by
    intro bi hbi b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using h2.1
  have hfreshPm : ∀ bi ∈ d.busInteractions, ∀ e ∈ bi.payload, ∀ b ∈ bits,
      e.mentions b = false := by
    intro bi hbi e he b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using List.all_eq_true.mp h2.2 e he
  -- FORWARD (with the input frame and the `DenseOutReconstructs` obligation)
  have hfwd_D : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ bits.map denseBoolConstraint, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d (denseReencodeOut d xs bits hm)
          (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
          denv denv') := by
    intro denv hsat
    have hallES : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := fun c hc =>
      hsat.1 c (List.mem_of_mem_filter hc)
    have hdsound := denseGroupDoms_sound denv (denseCoveredCsOf d xs) hallES xs doms hdoms
    have hamem : (doms.map (fun yd => (yd.1, denv yd.1))) ∈ denseAssignments doms :=
      mem_denseAssignments doms denv hdsound
    have hasurv : (doms.map (fun yd => (yd.1, denv yd.1)))
        ∈ denseGroupSurvivorsE (denseCoveredCsOf d xs) doms := by
      rw [denseGroupSurvivorsE_eq]
      refine List.mem_filter.2 ⟨hamem, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq]
      have hcov := List.of_mem_filter hc
      rw [denseCoveredBy, Bool.and_eq_true] at hcov
      have hcvars : ∀ v ∈ c.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]; exact denseVarsInF_sound xs c hcov.2
      have heq : c.eval (denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1)))) = c.eval denv :=
        DenseExpr.eval_congr c _ _ (fun v hv => denseEnvOfFast_map doms denv v (hcvars v hv))
      rw [heq]; exact hallES c hc
    have hC5' : (denseAssignments (denseBitBox bits)).any
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) = true := by
      rw [List.any_eq_true]
      obtain ⟨aβ, ha, hp⟩ := List.any_eq_true.1 (List.all_eq_true.mp hC5 _ hasurv)
      refine ⟨aβ, ha, ?_⟩
      rw [List.all_eq_true] at hp ⊢
      intro x hx
      have hsx : denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1))) x = denv x :=
        denseEnvOfFast_map doms denv x (by rw [hkeys]; exact hx)
      have hpp := hp x hx
      rw [hsx] at hpp
      exact hpp
    cases hfindEnv : (denseAssignments (denseBitBox bits)).find?
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
    | none =>
        exfalso
        rw [List.find?_eq_none] at hfindEnv
        obtain ⟨aβ0, ha0, hp0⟩ := List.any_eq_true.1 hC5'
        exact absurd hp0 (by simpa using hfindEnv aβ0 ha0)
    | some aβ =>
      have haβ : aβ ∈ denseAssignments (denseBitBox bits) := List.mem_of_find?_eq_some hfindEnv
      have hβpred : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true := by
        simpa using List.find?_some hfindEnv
      have hkeysβ : aβ.map Prod.fst = bits := by
        rw [denseAssignments_keys (denseBitBox bits) aβ haβ, hbitKeys]
      have henvxs : ∀ x ∈ xs, denseEnvExt aβ denv x = denv x := fun x hx =>
        denseEnvExt_eq_env_of_notmem aβ denv x (by rw [hkeysβ]; exact hxsB x hx)
      have hpoint : ∀ y, y ∉ bits →
          denseEnvF (denseGroupSubst xs hm) (denseEnvExt aβ denv) y = denv y := by
        intro y hyb
        by_cases hyx : y ∈ xs
        · rw [denseEnvF_eq_varSubst]
          have hagree : ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvExt aβ denv)
              = ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvOfFast aβ) := by
            apply DenseExpr.eval_congr
            intro v hv
            exact denseEnvExt_eq_envOfFast_of_mem aβ denv v (by rw [hkeysβ]; exact hpolyVars y hyx v hv)
          rw [hagree, ← DenseExpr.evalFast_eq]
          exact of_decide_eq_true (List.all_eq_true.mp hβpred y hyx)
        · unfold denseEnvF
          rw [hσnone y hyx]
          exact denseEnvExt_eq_env_of_notmem aβ denv y (by rw [hkeysβ]; exact hyb)
      have hbitsagree : ∀ b ∈ bits, denseEnvExt aβ denv b = denseEnvOfFast aβ b := fun b hb =>
        denseEnvExt_eq_envOfFast_of_mem aβ denv b (by rw [hkeysβ]; exact hb)
      refine ⟨denseEnvExt aβ denv, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint c (hfreshCm c hc)
      · intro bi hbi
        exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint bi (hfreshMm bi hbi) (hfreshPm bi hbi)
      · intro c hc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        apply denseBoolConstraint_eval_of_bool
        have hbk : b ∈ aβ.map Prod.fst := hkeysβ ▸ hb
        rw [denseEnvExt_eq_envOfFast_of_mem aβ denv b hbk]
        have hmem := denseEnvOf_mem_of_assignments (denseBitBox bits)
          (by rw [hbitKeys]; exact hnodup') aβ haβ
          (b, ([0, 1] : List (ZMod p))) (List.mem_map.2 ⟨b, hb, rfl⟩)
        simpa using hmem
      · intro i hii
        refine denseEnvExt_eq_env_of_notmem aβ denv i ?_
        rw [hkeysβ]
        intro hib
        rw [hbnInput i hib] at hii
        simp at hii
      · intro inputVarIds hcov1 i hiout hisF
        rw [DenseDerivations.methodFor_map bits
          (fun b => denseBitCM (denseAssignments (denseBitBox bits)) xs hm b) i]
        by_cases hib : i ∈ bits
        · rw [if_pos hib]
          refine ⟨fun j hj => hxsInput j (denseBitCM_vars _ xs hm i j hj), fun j hj => ?_, ?_⟩
          · exact hcov1 j (hxsOcc j (denseBitCM_vars _ xs hm i j hj))
              (hxsInput j (denseBitCM_vars _ xs hm i j hj))
          · have hval : (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i).eval
                (denseEnvExt aβ denv) = denseEnvOfFast aβ i := by
              rw [DenseComputationMethod.eval_congr
                  (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i)
                  (denseEnvExt aβ denv) denv
                  (fun v hv => henvxs v (denseBitCM_vars _ xs hm i v hv)),
                denseBitCM_eval, hfindEnv]
            rw [hval]
            exact (hbitsagree i hib).symm
        · rw [if_neg hib]
          refine ⟨?_, denseEnvExt_eq_env_of_notmem aβ denv i (by rw [hkeysβ]; exact hib)⟩
          rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hiout with h | h
          · exact h
          · exact absurd h hib
  -- BACKWARD
  have hbwd : ∀ denv', (denseReencodeOut d xs bits hm).satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, (fun c => !denseCoveredBy xs c) c = false → c.eval denv = 0) := by
    intro denv' hsat'
    have hbool : ∀ b ∈ bits, denv' b = 0 ∨ denv' b = 1 := by
      intro b hb
      apply dense_bool_of_boolConstraint_eval
      exact hsat'.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))
    have haβmem : ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1)))
        ∈ denseAssignments (denseBitBox bits) := by
      apply mem_denseAssignments
      intro yd hyd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hyd
      simpa using hbool b hb
    have hβenv : ∀ b ∈ bits,
        denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b = denv' b := by
      intro b hb
      exact denseEnvOfFast_map (denseBitBox bits) denv' b (by rw [hbitKeys]; exact hb)
    have hkeysP : (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))).map Prod.fst = xs := by
      rw [List.map_map]; simp [Function.comp_def]
    have hpoint : ∀ y, denseEnvF (denseGroupSubst xs hm) denv' y
        = denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv' y := by
      intro y
      by_cases hyx : y ∈ xs
      · rw [denseEnvF_eq_varSubst,
          denseEnvExt_eq_envOfFast_of_mem _ denv' y (by rw [hkeysP]; exact hyx),
          denseEnvOf_zipimg xs _ y hyx]
      · unfold denseEnvF
        rw [hσnone y hyx]
        exact (denseEnvExt_eq_env_of_notmem _ denv' y (by rw [hkeysP]; exact hyx)).symm
    have hexpr : ∀ e : DenseExpr p, (e.substF (denseGroupSubst xs hm)).eval denv'
        = e.eval (denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv') :=
      fun e => denseSubstF_eval_agree (denseGroupSubst xs hm) denv' _ e (fun y _ => hpoint y)
    have hbitsagree' : ∀ b ∈ bits,
        denv' b = denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b :=
      fun b hb => (hβenv b hb).symm
    refine ⟨denseEnvExt (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv', ?_, ?_, ?_⟩
    · intro c hc
      exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) c (hfreshCm c hc)
    · intro bi hbi
      exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) bi (hfreshMm bi hbi) (hfreshPm bi hbi)
    · intro c hc hkc
      have hcov : denseCoveredBy xs c = true := by simpa using hkc
      have hcmem : c ∈ denseCoveredCsOf d xs := List.mem_filter.2 ⟨hc, hcov⟩
      have h6 := List.all_eq_true.mp (List.all_eq_true.mp hC6 _ haβmem) c hcmem
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq] at h6
      have hcvars : ∀ v ∈ c.vars, v ∈ xs := by
        rw [denseCoveredBy, Bool.and_eq_true] at hcov
        exact denseVarsInF_sound xs c hcov.2
      have hagree : (c.substF (denseGroupSubst xs hm)).eval
            (denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))))
          = (c.substF (denseGroupSubst xs hm)).eval denv' := by
        rw [DenseExpr.eval_substF, DenseExpr.eval_substF]
        apply DenseExpr.eval_congr
        intro y hy
        rw [denseEnvF_eq_varSubst, denseEnvF_eq_varSubst]
        apply DenseExpr.eval_congr
        intro v hv
        exact hβenv v (hpolyVars y (hcvars y hy) v hv)
      rw [← hexpr c, ← hagree]
      exact h6
  -- no new powdr-ID column: every output variable is a `d`-column or a (non-input) bit
  have hVars : ∀ i ∈ (denseReencodeOut d xs bits hm).occ, isInput i = true → i ∈ d.occ := by
    intro i hi hii
    rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hi with h | h
    · exact h
    · rw [hbnInput i h] at hii; simp at hii
  exact DenseConstraintSystem.reencode_correct_D d (denseReencodeOut d xs bits hm) bs isInput
    (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits)))
    (fun c => !denseCoveredBy xs c)
    (bits.map denseBoolConstraint)
    (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
    rfl hfwd_D hbwd hVars


/-! ## Step / loop correctness, pass assembly

Each step is `DensePassCorrect` at its own output registry (reject branches by
`DensePassCorrect.refl`, the accept branch by the capstone `denseCheckReencode_sound`); the loop
composes them via `DensePassCorrect.andThen`, threading pointwise `isInput`-preservation to a
uniform final registry. `denseReencodePass` packages `denseReencodeF` through `ofExtending`. -/

theorem register_isInput_eq (reg : VarRegistry) (v : Variable) (hv : v.powdrId? = none)
    (i : VarId) : (reg.register v).1.isInput i = reg.isInput i := by
  by_cases hvalid : reg.Valid i
  · rw [VarRegistry.isInput, VarRegistry.isInput,
        (VarRegistry.register_extends reg v).resolve_eq hvalid]
  · have hge : reg.byId.size ≤ i.index := Nat.not_lt.mp hvalid
    have hreg : reg.isInput i = false := by
      show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    rw [hreg]
    show (((reg.register v).1.byId[i.index]?).getD default).powdrId?.isSome = false
    unfold VarRegistry.register
    split
    · show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    · show (((reg.byId.push v)[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_push]
      split
      · rw [Option.getD_some]; show (v.powdrId?).isSome = false; rw [hv]; rfl
      · rw [Array.getElem?_eq_none hge]; rfl

private def rbStep (fb : String) (acc : VarRegistry × List VarId) (j : Nat) :
    VarRegistry × List VarId :=
  let (r, bs) := acc
  let (r', i) := r.register ({ name := fb ++ "_" ++ toString j } : Variable)
  (r', bs ++ [i])

private theorem rbStep_eq (fb : String) (racc : VarRegistry) (bacc : List VarId) (j : Nat) :
    rbStep fb (racc, bacc) j
      = ((racc.register ({ name := fb ++ "_" ++ toString j } : Variable)).1,
         bacc ++ [(racc.register ({ name := fb ++ "_" ++ toString j } : Variable)).2]) := rfl

theorem registerBits_fold_inv (fb : String) (r0 : VarRegistry) :
    ∀ (l : List Nat) (racc : VarRegistry) (bacc : List VarId),
      r0.Extends racc → (∀ i, racc.isInput i = r0.isInput i) → (∀ b ∈ bacc, racc.Valid b) →
      r0.Extends (l.foldl (rbStep fb) (racc, bacc)).1
      ∧ (∀ i, (l.foldl (rbStep fb) (racc, bacc)).1.isInput i = r0.isInput i)
      ∧ (∀ b ∈ (l.foldl (rbStep fb) (racc, bacc)).2, (l.foldl (rbStep fb) (racc, bacc)).1.Valid b) := by
  intro l
  induction l with
  | nil => intro racc bacc hext hii hval; exact ⟨hext, hii, hval⟩
  | cons j rest ih =>
      intro racc bacc hext hii hval
      rw [List.foldl_cons, rbStep_eq]
      apply ih
      · exact hext.trans (VarRegistry.register_extends racc _)
      · intro i; rw [register_isInput_eq racc _ rfl i]; exact hii i
      · intro b hb
        rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact (VarRegistry.register_extends racc _).valid (hval b hb)
        · exact VarRegistry.register_valid racc _

theorem denseRegisterBits_props (reg : VarRegistry) (fb : String) (k : Nat) :
    reg.Extends (denseRegisterBits reg fb k).1
    ∧ (∀ i, (denseRegisterBits reg fb k).1.isInput i = reg.isInput i)
    ∧ (∀ b ∈ (denseRegisterBits reg fb k).2, (denseRegisterBits reg fb k).1.Valid b) :=
  registerBits_fold_inv fb reg (List.range k) reg [] (VarRegistry.Extends.refl reg)
    (fun _ => rfl) (by intro b hb; simp at hb)

theorem denseRegisterBits_extends_of_eq {reg r : VarRegistry} {fb : String} {k : Nat}
    {bs : List VarId} (h : denseRegisterBits reg fb k = (r, bs)) : reg.Extends r := by
  have := (denseRegisterBits_props reg fb k).1; rw [h] at this; exact this

theorem denseRegisterBits_isInput_of_eq {reg r : VarRegistry} {fb : String} {k : Nat}
    {bs : List VarId} (h : denseRegisterBits reg fb k = (r, bs)) (i : VarId) :
    r.isInput i = reg.isInput i := by
  have := (denseRegisterBits_props reg fb k).2.1 i; rw [h] at this; exact this

theorem denseRegisterBits_valid_of_eq {reg r : VarRegistry} {fb : String} {k : Nat}
    {bs : List VarId} (h : denseRegisterBits reg fb k = (r, bs)) : ∀ b ∈ bs, r.Valid b := by
  have := (denseRegisterBits_props reg fb k).2.2; rw [h] at this; exact this

theorem denseBuildReencodeCached_props (reg : VarRegistry)
    (csIdx : DenseCovIndex) (arrCs : Array (DenseExpr p))
    (cache : DenseReencodeRootCache p) (xs : List VarId) (freshBase : String) :
    reg.Extends (denseBuildReencodeCached reg csIdx arrCs cache xs freshBase).1
    ∧ (∀ i, (denseBuildReencodeCached reg csIdx arrCs cache xs freshBase).1.isInput i
        = reg.isInput i)
    ∧ (∀ bits hm,
        (denseBuildReencodeCached reg csIdx arrCs cache xs freshBase).2.1
          = some (bits, hm) →
        ∀ b ∈ bits,
          (denseBuildReencodeCached reg csIdx arrCs cache xs freshBase).1.Valid b) := by
  fun_cases denseBuildReencodeCached reg csIdx arrCs cache xs freshBase <;>
    first
      | exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl,
          by intro bits hm h; simp at h⟩
      | (refine ⟨denseRegisterBits_extends_of_eq (by assumption),
                fun i => denseRegisterBits_isInput_of_eq (by assumption) i, ?_⟩
         intro bits hm heq b hb
         dsimp only at heq
         rw [Option.some.injEq, Prod.mk.injEq] at heq
         obtain ⟨rfl, -⟩ := heq
         exact denseRegisterBits_valid_of_eq (by assumption) b hb)


theorem coveredBy_of_occ {r : VarRegistry} {d : DenseConstraintSystem p}
    (h : ∀ i ∈ d.occ, r.Valid i) : d.CoveredBy r := by
  grind [DenseConstraintSystem.CoveredBy, DenseExpr.CoveredBy, denseBICovered, denseBIVars,
    DenseConstraintSystem.mem_occ_of_constraint, DenseConstraintSystem.mem_occ_of_bi]

theorem csCoveredBy_mono {r r' : VarRegistry} (h : r.Extends r') {d : DenseConstraintSystem p}
    (hc : d.CoveredBy r) : d.CoveredBy r' :=
  ⟨fun e he => (hc.1 e he).mono h,
   fun bi hbi => ⟨(hc.2 bi hbi).1.mono h, fun e he => ((hc.2 bi hbi).2 e he).mono h⟩⟩

theorem denseCM_coveredBy_of_vars {r : VarRegistry} (cm : DenseComputationMethod p)
    (h : ∀ i ∈ cm.vars, r.Valid i) : cm.CoveredBy r := by
  induction cm with
  | const c => exact True.intro
  | quotientOrZero num den =>
      exact ⟨fun i hi => h i (List.mem_append_left _ hi),
             fun i hi => h i (List.mem_append_right _ hi)⟩
  | ifEqZero cond thenM elseM iht ihe =>
      refine ⟨fun i hi => h i ?_, iht (fun i hi => h i ?_), ihe (fun i hi => h i ?_)⟩
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hi)
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hi)
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hi

theorem denseReencodeOut_covered (reg1 : VarRegistry) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) (hcov1 : d.CoveredBy reg1)
    (hbits : ∀ b ∈ bits, reg1.Valid b)
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits) :
    (denseReencodeOut d xs bits hm).CoveredBy reg1 := by
  apply coveredBy_of_occ
  intro i hi
  rcases denseReencodeOut_vars_subset d xs bits hm hσ i hi with h | h
  · exact DenseConstraintSystem.occ_valid hcov1 i h
  · exact hbits i h

theorem denseBitCM_covered (reg1 : VarRegistry) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hxsValid : ∀ x ∈ xs, reg1.Valid x)
    (hbits : ∀ b ∈ bits, reg1.Valid b) :
    DenseDerivations.CoveredBy reg1
      (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b))) := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨hbits b hb, denseCM_coveredBy_of_vars _
    (fun i hi => hxsValid i (denseBitCM_vars _ xs hm b i hi))⟩


/-- `stepIdentityPost` for the cached step, which does not carry the variable-set invariant
    (its `varSet` over-approximates the live variables; see `DenseReencodeCacheState`). -/
theorem stepIdentityPostC (reg reg' : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p)
    (hext : reg.Extends reg') (hii : ∀ i, reg'.isInput i = reg.isInput i)
    (hcov : d.CoveredBy reg) :
    reg.Extends reg' ∧ (∀ i, reg'.isInput i = reg.isInput i) ∧ d.CoveredBy reg'
    ∧ DenseDerivations.CoveredBy reg' ([] : DenseDerivations p)
    ∧ DensePassCorrect reg'.isInput d d ([] : DenseDerivations p) bs :=
  ⟨hext, hii, csCoveredBy_mono hext hcov, (by intro x hx; simp at hx),
   DensePassCorrect.refl reg'.isInput d bs⟩

/-! ## Group variables occur in `d`, straight from the certificate

The cached step's `varSet` gate no longer witnesses `xs ⊆ d.occ` (the set is over-approximating),
so the accept case derives it from the certificate itself: `denseCheckReencode`'s domain lookup
returns, for every group variable, a covered constraint of `d` mentioning it. -/

private theorem DenseExpr.mentions_mem_vars {i : VarId} :
    ∀ {e : DenseExpr p}, e.mentions i = true → i ∈ e.vars := by
  intro e
  induction e with
  | const n => intro h; simp [DenseExpr.mentions] at h
  | var j =>
      intro h
      simp only [DenseExpr.mentions, beq_iff_eq] at h
      simp [DenseExpr.vars, h]
  | add a b iha ihb =>
      intro h
      rcases Bool.or_eq_true .. |>.mp h with h | h
      · exact List.mem_append_left _ (iha h)
      · exact List.mem_append_right _ (ihb h)
  | mul a b iha ihb =>
      intro h
      rcases Bool.or_eq_true .. |>.mp h with h | h
      · exact List.mem_append_left _ (iha h)
      · exact List.mem_append_right _ (ihb h)

private theorem denseFindDomainAlg_mentions {i : VarId} :
    ∀ {all : List (DenseExpr p)} {dm : List (ZMod p)},
      denseFindDomainAlg all i = some dm → ∃ c ∈ all, c.mentions i = true
  | [], dm, h => by simp [denseFindDomainAlg] at h
  | c :: rest, dm, h => by
      rw [denseFindDomainAlg] at h
      by_cases hm : c.mentions i = true
      · exact ⟨c, List.mem_cons_self .., hm⟩
      · rw [if_neg (by simpa using hm)] at h
        obtain ⟨c', hc', hm'⟩ := denseFindDomainAlg_mentions h
        exact ⟨c', List.mem_cons_of_mem _ hc', hm'⟩

private theorem denseGroupDoms_mentions {es : List (DenseExpr p)} :
    ∀ {xs : List VarId} {doms : List (VarId × List (ZMod p))},
      denseGroupDoms es xs = some doms → ∀ x ∈ xs, ∃ c ∈ es, c.mentions x = true
  | [], _, _, x, hx => absurd hx (by simp)
  | i :: rest, doms, h, x, hx => by
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some dm =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rcases List.mem_cons.1 hx with rfl | hmem
              · exact denseFindDomainAlg_mentions hd
              · exact denseGroupDoms_mentions hr x hmem

theorem denseCheckReencode_xsOcc (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hchk : denseCheckReencode d xs bits hm = true) :
    ∀ x ∈ xs, x ∈ d.occ := by
  intro x hx
  unfold denseCheckReencode at hchk
  cases hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => rw [hdoms] at hchk; exact absurd hchk (by simp)
  | some doms =>
      obtain ⟨c, hc, hmn⟩ := denseGroupDoms_mentions hdoms x hx
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc)
        (DenseExpr.mentions_mem_vars hmn)

theorem denseCheckReencode_polyVars (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hchk : denseCheckReencode d xs bits hm = true) :
    ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits := by
  grind [denseCheckReencode, List.contains_iff_mem]

theorem denseBuildReencodeCached_ext_of_eq {reg reg1 : VarRegistry}
    {csIdx : DenseCovIndex} {arrCs : Array (DenseExpr p)}
    {cache cache1 : DenseReencodeRootCache p} {xs : List VarId} {freshBase : String}
    {o : Option (List VarId × Std.HashMap VarId (DenseExpr p))}
    (h : denseBuildReencodeCached reg csIdx arrCs cache xs freshBase =
      (reg1, o, cache1)) : reg.Extends reg1 := by
  have := (denseBuildReencodeCached_props reg csIdx arrCs cache xs freshBase).1
  rw [h] at this
  exact this

theorem denseBuildReencodeCached_isInput_of_eq {reg reg1 : VarRegistry}
    {csIdx : DenseCovIndex} {arrCs : Array (DenseExpr p)}
    {cache cache1 : DenseReencodeRootCache p} {xs : List VarId} {freshBase : String}
    {o : Option (List VarId × Std.HashMap VarId (DenseExpr p))}
    (h : denseBuildReencodeCached reg csIdx arrCs cache xs freshBase =
      (reg1, o, cache1)) (i : VarId) :
    reg1.isInput i = reg.isInput i := by
  have :=
    (denseBuildReencodeCached_props reg csIdx arrCs cache xs freshBase).2.1 i
  rw [h] at this
  exact this

theorem denseBuildReencodeCached_bits_valid_of_eq {reg reg1 : VarRegistry}
    {csIdx : DenseCovIndex} {arrCs : Array (DenseExpr p)}
    {cache cache1 : DenseReencodeRootCache p} {xs : List VarId} {freshBase : String}
    {bits : List VarId} {hm : Std.HashMap VarId (DenseExpr p)}
    (h : denseBuildReencodeCached reg csIdx arrCs cache xs freshBase =
      (reg1, some (bits, hm), cache1)) :
    ∀ bb ∈ bits, reg1.Valid bb := by
  have := (denseBuildReencodeCached_props reg csIdx arrCs cache xs freshBase).2.2
    bits hm (by rw [h])
  rw [h] at this
  exact this

set_option maxHeartbeats 1000000 in
theorem denseFilterConstraints_coveredBy {d : DenseConstraintSystem p} {reg : VarRegistry}
    {keep : DenseExpr p → Bool} (h : d.CoveredBy reg) :
    (d.filterConstraints keep).CoveredBy reg :=
  ⟨fun e he => h.1 e (List.mem_of_mem_filter he), h.2⟩

/-! ### The variable-superset invariant

`denseWorkStep` decides bit freshness from `state.varSet` rather than scanning the system. What
licenses that is `DenseWorkVarsOk`: every variable occurring in the working system is in `varSet`.
The seed satisfies it by construction (`varSet = ofList d.occ`), and an accept preserves it because
the rewritten system's variables are old variables or fresh bits
(`denseReencodeOut_vars_subset`), and the fresh bits are exactly what the state update inserts. -/

/-- Every variable of the working system is recorded in `vs`. -/
def DenseWorkVarsOk (vs : Std.HashSet VarId) (w : DenseReencodeWork p) : Prop :=
  ∀ v ∈ (denseWorkView w).occ, vs.contains v = true

theorem denseIsZero_vars {c : DenseExpr p} (h : denseIsZero c = true) : c.vars = [] := by
  cases c <;> simp_all [denseIsZero, DenseExpr.vars]

/-- The raw working pieces have no variable the view lacks: the view only drops `.const 0`
    tombstones, which carry none. -/
theorem denseWorkRaw_occ_sub (w : DenseReencodeWork p) :
    ∀ v ∈ ({ algebraicConstraints := w.cs,
             busInteractions := w.bis } : DenseConstraintSystem p).occ,
      v ∈ (denseWorkView w).occ := by
  intro v hv
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · have hkeep : (!denseIsZero c) = true := by
      cases hz : denseIsZero c with
      | false => rfl
      | true => rw [denseIsZero_vars hz] at hcv; simp at hcv
    refine DenseConstraintSystem.mem_occ_of_constraint (c := c) ?_ hcv
    show c ∈ w.cs.filter (fun c => !denseIsZero c) ++ w.bools
    exact List.mem_append.2 (Or.inl (List.mem_filter.2 ⟨hc, hkeep⟩))
  · exact DenseConstraintSystem.mem_occ_of_bi (bi := bi) hbi hbiv

/-- Filtering constraints cannot introduce a variable. -/
theorem denseFilterConstraints_occ_sub (d : DenseConstraintSystem p)
    (keep : DenseExpr p → Bool) :
    ∀ v ∈ (d.filterConstraints keep).occ, v ∈ d.occ := by
  intro v hv
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.filterConstraints,
    List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc) hcv
  · exact DenseConstraintSystem.mem_occ_of_bi hbi hbiv

/-- Freshness holds for any bit the system does not mention. -/
theorem denseFreshScan_of_notMemOcc (d : DenseConstraintSystem p) (bits : List VarId)
    (h : ∀ b ∈ bits, b ∉ d.occ) : denseFreshScan d bits = true := by
  have hb : ∀ (e : DenseExpr p), (∀ b ∈ bits, b ∉ e.vars) →
      e.mentionsAny (Std.HashSet.ofList bits) = false := by
    intro e he
    exact (DenseExpr.mentionsAny_ofList_false_iff bits e).2 (fun b hbm =>
      by
        cases hm : e.mentions b with
        | false => rfl
        | true => exact absurd (DenseExpr.mentions_mem_vars hm) (he b hbm))
  simp only [denseFreshScan, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨fun c hc => hb c (fun b hbm hv => h b hbm ?_), fun bi hbi => ⟨hb _ (fun b hbm hv =>
    h b hbm ?_), fun e he => hb e (fun b hbm hv => h b hbm ?_)⟩⟩
  · exact DenseConstraintSystem.mem_occ_of_constraint hc hv
  · exact DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append]; exact Or.inl hv)
  · exact DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨e, he, hv⟩)

/-- The step's certificate: the `varSet` test plus the remaining conjuncts give the full
    certificate, on the strength of the invariant. -/
theorem denseCheckReencodeVS_sound {w : DenseReencodeWork p}
    {state : DenseReencodeCacheState p} {xs bits : List VarId}
    {hm : Std.HashMap VarId (DenseExpr p)} (hvs : DenseWorkVarsOk state.varSet w)
    (h : denseCheckReencodeVS state
      { algebraicConstraints := w.cs, busInteractions := w.bis } xs bits hm = true) :
    denseCheckReencode { algebraicConstraints := w.cs, busInteractions := w.bis } xs bits hm
      = true := by
  rw [denseCheckReencodeVS, Bool.and_eq_true] at h
  obtain ⟨hnv, hnf⟩ := h
  refine denseCheckReencode_of_parts _ xs bits hm hnf (denseFreshScan_of_notMemOcc _ bits ?_)
  intro b hb hmem
  have hcontains : state.varSet.contains b = true :=
    hvs b (denseWorkRaw_occ_sub w b hmem)
  have := List.all_eq_true.mp hnv b hb
  rw [hcontains] at this
  exact Bool.noConfusion this

/-! ### The bus-side index invariant

`denseWorkOut` rewrites the bus list only at the positions it is handed, so it needs those positions
to cover everywhere `denseBIRewriteGate` could fire. `DenseBusIdxOk` is what supplies that: the
`useBis` buckets list every position by each of its variables, and `foldBis` lists every position
carrying a variable-free composite node. Both hold at the seed by construction and are maintained by
the state update, which folds over the very list the splice consumed. -/

/-- Insert-folding into a set never loses a member. -/
theorem denseNatFold_mono (l : List Nat) :
    ∀ (s : Std.HashSet Nat) (v : Nat), s.contains v = true →
      (l.foldl (·.insert ·) s).contains v = true := by
  intro s v
  induction l generalizing s with
  | nil => intro h; exact h
  | cons a rest ih => intro h; exact ih _ (by simp [Std.HashSet.contains_insert, h])

/-- A member of the folded list ends up in the set. -/
theorem denseNatFold_mem (l : List Nat) :
    ∀ (s : Std.HashSet Nat) (v : Nat), v ∈ l → (l.foldl (·.insert ·) s).contains v = true := by
  intro s v
  induction l generalizing s with
  | nil => intro h; simp at h
  | cons a rest ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · exact denseNatFold_mono rest _ v (by simp [Std.HashSet.contains_insert])
      · exact ih _ h

/-- `denseBuild_complete` in the `getElem?` form the invariant uses. -/
theorem denseBuild_complete' {α : Type} (varsOf : α → List VarId) (items : List α) (i : Nat)
    (a : α) (hi : items[i]? = some a) (v : VarId) (hv : v ∈ varsOf a) :
    i ∈ (denseCovBuild varsOf items).buckets.getD v [] := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hi
  subst hget
  exact denseBuild_complete varsOf items i hlt v hv

/-- The seed's fold-position scan lists every interaction carrying a variable-free composite node. -/
theorem denseFoldBisSeed_complete (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (n : Nat) (s : Std.HashSet Nat) (k : Nat) (bi : BusInteraction (DenseExpr p)),
      bis[k]? = some bi → denseBiHasFold bi = true →
      ((bis.zipIdx n).foldl
        (fun s x => if denseBiHasFold x.1 then s.insert x.2 else s) s).contains (n + k) = true := by
  have hmono : ∀ (l : List (BusInteraction (DenseExpr p) × Nat)) (s : Std.HashSet Nat) (j : Nat),
      s.contains j = true →
      (l.foldl (fun s x => if denseBiHasFold x.1 then s.insert x.2 else s) s).contains j = true := by
    intro l
    induction l with
    | nil => intro s j h; exact h
    | cons a rest ih =>
        intro s j h
        refine ih _ j ?_
        by_cases hf : denseBiHasFold a.1 = true
        · simp [hf, Std.HashSet.contains_insert, h]
        · simp [hf, h]
  intro n s k bi
  induction bis generalizing n s k with
  | nil => intro h; simp at h
  | cons a rest ih =>
      intro hk hfold
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simp only [List.zipIdx_cons, List.foldl_cons]
          refine hmono _ _ _ ?_
          simp [hfold, Std.HashSet.contains_insert]
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          simp only [List.zipIdx_cons, List.foldl_cons]
          have := ih (n + 1) (if denseBiHasFold a then s.insert n else s) k hk hfold
          have heq : n + 1 + k = n + (k + 1) := by omega
          rwa [heq] at this

/-- Every position of the system whose interaction is listed by its variables, and every position
    carrying a variable-free composite node. -/
def DenseBusIdxOk (state : DenseReencodeCacheState p) (w : DenseReencodeWork p) : Prop :=
  (∀ (i : Nat) (bi : BusInteraction (DenseExpr p)), w.bis[i]? = some bi →
      ∀ v ∈ denseBIVars bi, i ∈ state.useBis.buckets.getD v [])
  ∧ (∀ (i : Nat) (bi : BusInteraction (DenseExpr p)), w.bis[i]? = some bi →
      denseBiHasFold bi = true → state.foldBis.get.contains i = true)

/-- The position list the step builds. -/
def denseBusPosList (state : DenseReencodeCacheState p) (xs : List VarId) : List Nat :=
  ((denseCandidates state.useBis xs).foldl (·.insert ·) state.foldBis.get).toList.mergeSort (· ≤ ·)

theorem denseBusPosList_sorted (state : DenseReencodeCacheState p) (xs : List VarId) :
    (denseBusPosList state xs).Pairwise (· ≤ ·) :=
  List.pairwise_mergeSort' (fun a b => a ≤ b) _

/-- The invariant makes the position list complete for the gate. -/
theorem denseBusPosList_cover {state : DenseReencodeCacheState p} {w : DenseReencodeWork p}
    (xs : List VarId) (hidx : DenseBusIdxOk state w) :
    ∀ k bi, w.bis[k]? = some bi → denseBiGateFires xs bi = true → k ∈ denseBusPosList state xs := by
  intro k bi hk hf
  have hset : ((denseCandidates state.useBis xs).foldl (·.insert ·)
      state.foldBis.get).contains k = true := by
    have hvar : ∀ (e : DenseExpr p), e.sharesVarIn xs = true → (∀ v ∈ e.vars, v ∈ denseBIVars bi) →
        ((denseCandidates state.useBis xs).foldl (·.insert ·) state.foldBis.get).contains k = true := by
      intro e he hsub
      obtain ⟨v, hv, hvxs⟩ := denseSharesVarIn_exists he
      exact denseNatFold_mem _ _ k
        (denseMem_candidates state.useBis xs v k hvxs (hidx.1 k bi hk v (hsub v hv)))
    have hfold : denseBiHasFold bi = true →
        ((denseCandidates state.useBis xs).foldl (·.insert ·) state.foldBis.get).contains k = true :=
      fun h => denseNatFold_mono _ _ k (hidx.2 k bi hk h)
    simp only [denseBiGateFires, Bool.or_eq_true, List.any_eq_true] at hf
    rcases hf with (hm | hm) | ⟨e, he, hee⟩
    · exact hvar bi.multiplicity hm (fun v hv => by
        simp only [denseBIVars, List.mem_append]; exact Or.inl hv)
    · exact hfold (by simp [denseBiHasFold, hm])
    · rcases hee with h | h
      · exact hvar e h (fun v hv => by
          simp only [denseBIVars, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨e, he, hv⟩)
      · exact hfold (by
          simp only [denseBiHasFold, Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨e, he, h⟩)
  rw [denseBusPosList, List.mem_mergeSort]
  simpa [Std.HashSet.mem_toList] using hset

/-- Bucket inserts never lose a member. -/
theorem denseBucketFold_mono (vs : List VarId) (i : Nat) :
    ∀ (m : Std.HashMap VarId (List Nat)) (v : VarId) (k : Nat), k ∈ m.getD v [] →
      k ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD v [] := by
  intro m v k
  induction vs generalizing m with
  | nil => intro h; exact h
  | cons a rest ih =>
      intro h
      refine ih _ ?_
      by_cases hva : v = a
      · subst hva
        rw [Std.HashMap.getD_insert_self]
        exact List.mem_cons_of_mem _ h
      · have hne : (m.insert a (i :: m.getD a [])).getD v [] = m.getD v [] := by
          rw [Std.HashMap.getD_insert]
          rw [if_neg (show ¬((a == v) = true) by simpa using Ne.symm hva)]
        rw [hne]; exact h

/-- A variable of the inserted list gets the position. -/
theorem denseBucketFold_mem (vs : List VarId) (i : Nat) :
    ∀ (m : Std.HashMap VarId (List Nat)) (v : VarId), v ∈ vs →
      i ∈ (vs.foldl (fun m v => m.insert v (i :: m.getD v [])) m).getD v [] := by
  intro m v
  induction vs generalizing m with
  | nil => intro h; simp at h
  | cons a rest ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · refine denseBucketFold_mono rest i _ _ i ?_
        rw [Std.HashMap.getD_insert_self]
        exact List.mem_cons_self ..
      · exact ih _ h

/-- Positions the fold does not visit keep their fold-set membership. -/
theorem denseBusIdxFold_keep_of_not_mem (arrB : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat) (acc : DenseCovIndex × Std.HashSet Nat) (i : Nat), i ∉ ps →
      acc.2.contains i = true → (denseBusIdxFold arrB ps acc).2.contains i = true := by
  intro ps
  induction ps with
  | nil => intro acc i _ h; rw [denseBusIdxFold]; exact h
  | cons j rest ih =>
      intro acc i hni h
      have hij : i ≠ j := fun hh => hni (hh ▸ List.mem_cons_self ..)
      rw [denseBusIdxFold]
      split
      · refine ih _ i (fun hmem => hni (List.mem_cons_of_mem _ hmem)) ?_
        show (if denseBiHasFold _ then acc.2.insert j else acc.2.erase j).contains i = true
        split
        · simp [Std.HashSet.contains_insert, h]
        · simp [Std.HashSet.contains_erase, h, Ne.symm hij]
      · exact ih _ i (fun hmem => hni (List.mem_cons_of_mem _ hmem)) h

/-- A position whose interaction carries a fold node keeps its membership through the fold: every
    visit to it re-inserts it, since the decision is a function of the (unchanging) content. -/
theorem denseBusIdxFold_keep_of_hasFold (arrB : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat) (acc : DenseCovIndex × Std.HashSet Nat) (i : Nat) (h : i < arrB.size),
      denseBiHasFold arrB[i] = true → acc.2.contains i = true →
      (denseBusIdxFold arrB ps acc).2.contains i = true := by
  intro ps
  induction ps with
  | nil => intro acc i _ _ h; rw [denseBusIdxFold]; exact h
  | cons j rest ih =>
      intro acc i hlt hfold h
      rw [denseBusIdxFold]
      split
      · refine ih _ i hlt hfold ?_
        show (if denseBiHasFold _ then acc.2.insert j else acc.2.erase j).contains i = true
        by_cases hij : i = j
        · subst hij; rw [if_pos hfold]; simp [Std.HashSet.contains_insert]
        · split
          · simp [Std.HashSet.contains_insert, h]
          · simp [Std.HashSet.contains_erase, h, Ne.symm hij]
      · exact ih _ i hlt hfold h

/-- Visited in-range positions get their interaction's variables into the buckets. -/
theorem denseBusIdxFold_buckets (arrB : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat) (acc : DenseCovIndex × Std.HashSet Nat),
      (∀ v k, k ∈ acc.1.buckets.getD v [] →
        k ∈ (denseBusIdxFold arrB ps acc).1.buckets.getD v [])
      ∧ (∀ i, i ∈ ps → ∀ (h : i < arrB.size), ∀ v ∈ denseBIVars arrB[i],
          i ∈ (denseBusIdxFold arrB ps acc).1.buckets.getD v []) := by
  intro ps
  induction ps with
  | nil =>
      intro acc
      exact ⟨fun v k h => by rw [denseBusIdxFold]; exact h, fun i h => absurd h (by simp)⟩
  | cons j rest ih =>
      intro acc
      rw [denseBusIdxFold]
      split
      · next hj =>
        obtain ⟨ih1, ih2⟩ := ih (⟨(HashedDedup.hashedDedup (hash ·)
            (denseBIVars arrB[j])).foldl (fun m v => m.insert v (j :: m.getD v [])) acc.1.buckets,
            acc.1.varless⟩,
          if denseBiHasFold arrB[j] then acc.2.insert j else acc.2.erase j)
        refine ⟨fun v k h => ih1 v k (denseBucketFold_mono _ _ _ v k h), ?_⟩
        intro i hi h v hv
        rcases List.mem_cons.1 hi with rfl | hi
        · refine ih1 v i (denseBucketFold_mem _ _ _ v ?_)
          rw [HashedDedup.hashedDedup_eq]
          exact List.mem_dedup.2 (by simpa using hv)
        · exact ih2 i hi h v hv
      · next hj =>
        obtain ⟨ih1, ih2⟩ := ih acc
        refine ⟨ih1, ?_⟩
        intro i hi h v hv
        rcases List.mem_cons.1 hi with rfl | hi
        · exact absurd h hj
        · exact ih2 i hi h v hv

/-- A visited in-range position carrying a fold node ends up in the fold set. -/
theorem denseBusIdxFold_mem_of_hasFold (arrB : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat) (acc : DenseCovIndex × Std.HashSet Nat) (i : Nat) (h : i < arrB.size),
      i ∈ ps → denseBiHasFold arrB[i] = true →
      (denseBusIdxFold arrB ps acc).2.contains i = true := by
  intro ps
  induction ps with
  | nil => intro _ i _ hi _; exact absurd hi (by simp)
  | cons j rest ih =>
      intro acc i hlt hi hfold
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [denseBusIdxFold, dif_pos hlt]
        refine denseBusIdxFold_keep_of_hasFold arrB rest _ i hlt hfold ?_
        show (if denseBiHasFold arrB[i] then acc.2.insert i else acc.2.erase i).contains i = true
        rw [if_pos hfold]
        simp [Std.HashSet.contains_insert]
      · rw [denseBusIdxFold]
        split
        · exact ih _ i hlt hi hfold
        · exact ih _ i hlt hi hfold

/-- The index invariant survives an accept: the update folds over the positions the rewrite visited,
    recording the new interactions' variables, and every other position kept its content. -/
theorem denseBusIdxOk_update {state : DenseReencodeCacheState p} {w w' : DenseReencodeWork p}
    {xs bits : List VarId} {hm : Std.HashMap VarId (DenseExpr p)}
    (hidx : DenseBusIdxOk state w)
    (hnew : ∀ i bi, w'.bis[i]? = some bi → i ∉ denseBusPosList state xs →
      w.bis[i]? = some bi) :
    DenseBusIdxOk
      (denseReencodeStateUpdate state (denseBusPosList state xs) w'.bis xs bits hm) w' := by
  set ps := denseBusPosList state xs with hps
  have hproj : (denseReencodeStateUpdate state ps w'.bis xs bits hm).useBis
      = (denseBusIdxFold w'.bis.toArray ps (state.useBis, state.foldBis.get)).1 := rfl
  have hprojF : (denseReencodeStateUpdate state ps w'.bis xs bits hm).foldBis.get
      = (denseBusIdxFold w'.bis.toArray ps (state.useBis, state.foldBis.get)).2 := rfl
  obtain ⟨hb1, hb2⟩ :=
    denseBusIdxFold_buckets w'.bis.toArray ps (state.useBis, state.foldBis.get)
  constructor
  · intro i bi hi v hv
    obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.1 hi
    have hlt : i < w'.bis.toArray.size := by simpa using hlt'
    have hidx' : w'.bis.toArray[i] = bi := by simpa using hget
    rw [hproj]
    by_cases hmem : i ∈ ps
    · exact hb2 i hmem hlt v (by rw [hidx']; exact hv)
    · exact hb1 v i (hidx.1 i bi (hnew i bi hi hmem) v hv)
  · intro i bi hi hfold
    obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.1 hi
    have hlt : i < w'.bis.toArray.size := by simpa using hlt'
    have hidx' : w'.bis.toArray[i] = bi := by simpa using hget
    rw [hprojF]
    by_cases hmem : i ∈ ps
    · exact denseBusIdxFold_mem_of_hasFold w'.bis.toArray ps _ i hlt hmem
        (by rw [hidx']; exact hfold)
    · exact denseBusIdxFold_keep_of_not_mem w'.bis.toArray ps _ i hmem
        (hidx.2 i bi (hnew i bi hi hmem) hfold)

set_option maxHeartbeats 1000000 in
theorem denseWorkStep_correct [Fact p.Prime] (b : DegreeBound)
    (reg : VarRegistry) (w : DenseReencodeWork p) (state : DenseReencodeCacheState p)
    (xs : List VarId) (freshBase : String) (bs : BusSemantics p)
    (hcov : (denseWorkView w).CoveredBy reg)
    (hpos : w.bounded = true → DenseWorkPosOk w.lastPos w.lastFold w.cs)
    (hbools : DenseWorkBoolsOk w.bitSet w.bools)
    (hvs : DenseWorkVarsOk state.varSet w)
    (hidxB : DenseBusIdxOk state w) :
    reg.Extends (denseWorkStep b reg w state xs freshBase).1
    ∧ (∀ i, (denseWorkStep b reg w state xs freshBase).1.isInput i = reg.isInput i)
    ∧ (denseWorkView (denseWorkStep b reg w state xs freshBase).2.1).CoveredBy
        (denseWorkStep b reg w state xs freshBase).1
    ∧ DenseDerivations.CoveredBy (denseWorkStep b reg w state xs freshBase).1
        (denseWorkStep b reg w state xs freshBase).2.2.1
    ∧ DensePassCorrect (denseWorkStep b reg w state xs freshBase).1.isInput (denseWorkView w)
        (denseWorkView (denseWorkStep b reg w state xs freshBase).2.1)
        (denseWorkStep b reg w state xs freshBase).2.2.1 bs := by
  fun_cases denseWorkStep b reg w state xs freshBase
  all_goals first
    | exact stepIdentityPostC reg reg (denseWorkView w) bs (VarRegistry.Extends.refl reg)
        (fun _ => rfl) hcov
    | exact stepIdentityPostC reg _ (denseWorkView w) bs
        (denseBuildReencodeCached_ext_of_eq (by assumption))
        (fun i => denseBuildReencodeCached_isInput_of_eq (by assumption) i) hcov
    | skip
  rename_i hgate hbit hcoll reg1 bits hm rootCache hbeq state1 hbits hdpr hA hB hC hD ro hwd
  have hbext : reg.Extends reg1 := denseBuildReencodeCached_ext_of_eq hbeq
  have hbii : ∀ i, reg1.isInput i = reg.isInput i := fun i =>
    denseBuildReencodeCached_isInput_of_eq hbeq i
  have hbval : ∀ bb ∈ bits, reg1.Valid bb := denseBuildReencodeCached_bits_valid_of_eq hbeq
  have hxsB' : ∀ x ∈ xs, w.bitSet.contains x = false := by simpa using hbit
  have hbitsB' : ∀ bb ∈ bits, w.bitSet.contains bb = false := by simpa using hbits
  have hchkView : denseCheckReencode (denseWorkView w) xs bits hm = true := by
    rw [denseWorkView_check hm hbools hxsB' hbitsB']
    exact denseCheckReencodeVS_sound hvs hD
  have hview : denseWorkView ro.1
      = (denseReencodeOut (denseWorkView w) xs bits hm).filterConstraints
          (fun c => !denseIsZero c) := by
    have h := denseWorkOut_view (usePosB := denseBusPosList state1 xs)
        b (denseWorkEnsureBounded w) xs bits hm
      (denseWorkEnsureBounded_posOk hpos)
      (by rw [denseWorkEnsureBounded_bitSet, denseWorkEnsureBounded_bools]; exact hbools)
      (by rw [denseWorkEnsureBounded_bitSet]; exact hxsB')
      (denseBusPosList_sorted state1 xs)
      (by
        intro k bi hk hf
        exact denseBusPosList_cover xs hidxB k bi (by rwa [denseWorkEnsureBounded_bis] at hk) hf)
    rwa [denseWorkEnsureBounded_view] at h
  have hpolyVars := denseCheckReencode_polyVars (denseWorkView w) xs bits hm hchkView
  have hxsInput : ∀ x ∈ xs, reg1.isInput x = true := fun x hx => by
    rw [hbii x]
    exact List.all_eq_true.mp hgate x hx
  have hxsOcc : ∀ x ∈ xs, x ∈ (denseWorkView w).occ :=
    denseCheckReencode_xsOcc (denseWorkView w) xs bits hm hchkView
  have hxsBits : ∀ x ∈ xs, x ∉ bits := fun x hx =>
    of_decide_eq_true (List.all_eq_true.mp hB x hx)
  have hbnInput : ∀ bb ∈ bits, reg1.isInput bb = false := fun bb hbb => by
    have hpd : (reg1.resolve bb).powdrId? = none :=
      of_decide_eq_true (List.all_eq_true.mp hC bb hbb)
    show (reg1.resolve bb).powdrId?.isSome = false
    rw [hpd]
    rfl
  have hxsValid : ∀ x ∈ xs, reg1.Valid x := fun x hx =>
    hbext.valid (DenseConstraintSystem.occ_valid hcov x (hxsOcc x hx))
  refine ⟨hbext, hbii, ?_, ?_, ?_⟩
  · rw [hview]
    exact denseFilterConstraints_coveredBy
      (denseReencodeOut_covered reg1 (denseWorkView w) xs bits hm
        (csCoveredBy_mono hbext hcov) hbval hpolyVars)
  · exact denseBitCM_covered reg1 xs bits hm hxsValid hbval
  · rw [hview]
    have h1 := denseCheckReencode_sound (denseWorkView w) bs reg1.isInput xs bits hm
      hxsInput hxsOcc hxsBits hbnInput hchkView
    have h2 := DensePassCorrect.denseFilterConstraintsEntailed
      (denseReencodeOut (denseWorkView w) xs bits hm) bs reg1.isInput (fun c => !denseIsZero c)
      (fun c _ hk => denseIsZero_eval (by simpa using hk))
    simpa using h1.andThen h2

theorem denseBitSetFold_mono (bits : List VarId) :
    ∀ (s : Std.HashSet VarId) (v : VarId), s.contains v = true →
      (bits.foldl (·.insert ·) s).contains v = true := by
  intro s v
  induction bits generalizing s with
  | nil => intro h; exact h
  | cons bb rest ih =>
      intro h
      exact ih _ (by simp [Std.HashSet.contains_insert, h])

theorem denseBitSetFold_mem (bits : List VarId) :
    ∀ (s : Std.HashSet VarId) (v : VarId), v ∈ bits →
      (bits.foldl (·.insert ·) s).contains v = true := by
  intro s v
  induction bits generalizing s with
  | nil => intro h; simp at h
  | cons bb rest ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact denseBitSetFold_mono rest _ v (by simp [Std.HashSet.contains_insert])
      · exact ih _ h

theorem denseWorkStep_inv (b : DegreeBound) (reg : VarRegistry) (w : DenseReencodeWork p)
    (state : DenseReencodeCacheState p) (xs : List VarId) (freshBase : String)
    (hpos : w.bounded = true → DenseWorkPosOk w.lastPos w.lastFold w.cs)
    (hbools : DenseWorkBoolsOk w.bitSet w.bools)
    (hvs : DenseWorkVarsOk state.varSet w)
    (hidxB : DenseBusIdxOk state w) :
    ((denseWorkStep b reg w state xs freshBase).2.1.bounded = true →
      DenseWorkPosOk (denseWorkStep b reg w state xs freshBase).2.1.lastPos
        (denseWorkStep b reg w state xs freshBase).2.1.lastFold
        (denseWorkStep b reg w state xs freshBase).2.1.cs)
    ∧ DenseWorkBoolsOk (denseWorkStep b reg w state xs freshBase).2.1.bitSet
        (denseWorkStep b reg w state xs freshBase).2.1.bools
    ∧ DenseWorkVarsOk (denseWorkStep b reg w state xs freshBase).2.2.2.varSet
        (denseWorkStep b reg w state xs freshBase).2.1
    ∧ DenseBusIdxOk (denseWorkStep b reg w state xs freshBase).2.2.2
        (denseWorkStep b reg w state xs freshBase).2.1 := by
  fun_cases denseWorkStep b reg w state xs freshBase
  all_goals try exact ⟨hpos, hbools, hvs, hidxB⟩
  rename_i hgate hbit hcoll reg1 bits hm rootCache hbeq state1 hbits hdpr hA hB hC hD ro hwd
  have hxsB' : ∀ x ∈ xs, w.bitSet.contains x = false := by simpa using hbit
  have hbitsB' : ∀ bb ∈ bits, w.bitSet.contains bb = false := by simpa using hbits
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    show DenseWorkPosOk _ _ _
    rw [densePosOk_from0]
    set w' := denseWorkEnsureBounded w with hw'
    exact denseWorkSpliceCs_posOk b.identities xs bits (denseGroupSubst xs hm)
      (denseAssignments (denseBitBox bits)) (denseWorkMaxPos w'.lastPos w'.lastFold xs)
      w'.cs 0 [] w'.lastPos w'.lastFold true rfl (by intro j c hj; simp at hj)
      (densePosOk_from0.mp (denseWorkEnsureBounded_posOk hpos))
  · show DenseWorkBoolsOk (bits.foldl (·.insert ·) (denseWorkEnsureBounded w).bitSet)
      ((denseWorkEnsureBounded w).bools ++ bits.map (denseBoolConstraint (p := p)))
    rw [denseWorkEnsureBounded_bitSet, denseWorkEnsureBounded_bools]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨bb, rfl, hbb⟩ := hbools c hc
      exact ⟨bb, rfl, denseBitSetFold_mono bits w.bitSet bb hbb⟩
    · obtain ⟨bb, hbb, rfl⟩ := List.mem_map.1 hc
      exact ⟨bb, rfl, denseBitSetFold_mem bits w.bitSet bb hbb⟩
  · -- the variable superset survives an accept: the rewritten system's variables are old ones or
    -- fresh bits, and the fresh bits are exactly what the state update inserts
    have hchkView : denseCheckReencode (denseWorkView w) xs bits hm = true := by
      rw [denseWorkView_check hm hbools hxsB' hbitsB']
      exact denseCheckReencodeVS_sound hvs hD
    have hpolyVars := denseCheckReencode_polyVars (denseWorkView w) xs bits hm hchkView
    have hview : denseWorkView ro.1
        = (denseReencodeOut (denseWorkView w) xs bits hm).filterConstraints
            (fun c => !denseIsZero c) := by
      have h := denseWorkOut_view (usePosB := denseBusPosList state1 xs)
          b (denseWorkEnsureBounded w) xs bits hm
        (denseWorkEnsureBounded_posOk hpos)
        (by rw [denseWorkEnsureBounded_bitSet, denseWorkEnsureBounded_bools]; exact hbools)
        (by rw [denseWorkEnsureBounded_bitSet]; exact hxsB')
        (denseBusPosList_sorted state1 xs)
        (by
          intro k bi hk hf
          exact denseBusPosList_cover (w := w) xs hidxB k bi
            (by rwa [denseWorkEnsureBounded_bis] at hk) hf)
      rwa [denseWorkEnsureBounded_view] at h
    intro v hv
    show (bits.foldl (·.insert ·) state.varSet).contains v = true
    rw [hview] at hv
    rcases denseReencodeOut_vars_subset (denseWorkView w) xs bits hm hpolyVars v
        (denseFilterConstraints_occ_sub _ _ v hv) with h | h
    · exact denseBitSetFold_mono bits state.varSet v (hvs v h)
    · exact denseBitSetFold_mem bits state.varSet v h
  · -- the bus index invariant survives an accept
    have hcov : ∀ k bi, (denseWorkEnsureBounded w).bis[k]? = some bi →
        denseBiGateFires xs bi = true → k ∈ denseBusPosList state1 xs := by
      intro k bi hk hf
      exact denseBusPosList_cover (w := w) xs hidxB k bi
        (by rwa [denseWorkEnsureBounded_bis] at hk) hf
    have hnew : ∀ i bi, ro.1.bis[i]? = some bi → i ∉ denseBusPosList state1 xs →
        w.bis[i]? = some bi := by
      intro i bi hi hni
      have hro : ro.1.bis = (denseGateBisPos b.busInteractions xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) (denseBusPosList state1 xs) 0
          (denseWorkEnsureBounded w).bis [] true).1 := rfl
      rw [hro] at hi
      have := denseGateBisPos_untouched b.busInteractions xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) (denseBusPosList state1 xs)
        (denseWorkEnsureBounded w).bis (denseBusPosList_sorted state1 xs) hcov i bi hi hni
      rwa [denseWorkEnsureBounded_bis] at this
    exact denseBusIdxOk_update hidxB hnew

set_option maxHeartbeats 1000000 in
theorem denseWorkLoop_correct [Fact p.Prime] (b : DegreeBound) (bs : BusSemantics p) :
    ∀ (targets : List (List VarId)) (idx : Nat) (reg : VarRegistry) (w : DenseReencodeWork p)
      (state : DenseReencodeCacheState p) (nc nb : Nat),
      (denseWorkView w).CoveredBy reg →
      (w.bounded = true → DenseWorkPosOk w.lastPos w.lastFold w.cs) →
      DenseWorkBoolsOk w.bitSet w.bools →
      DenseWorkVarsOk state.varSet w →
      DenseBusIdxOk state w →
      reg.Extends (denseWorkLoop b targets idx reg w state nc nb).1
      ∧ (∀ i, (denseWorkLoop b targets idx reg w state nc nb).1.isInput i = reg.isInput i)
      ∧ (denseWorkView (denseWorkLoop b targets idx reg w state nc nb).2.1).CoveredBy
          (denseWorkLoop b targets idx reg w state nc nb).1
      ∧ DenseDerivations.CoveredBy (denseWorkLoop b targets idx reg w state nc nb).1
          (denseWorkLoop b targets idx reg w state nc nb).2.2
      ∧ DensePassCorrect (denseWorkLoop b targets idx reg w state nc nb).1.isInput
          (denseWorkView w) (denseWorkView (denseWorkLoop b targets idx reg w state nc nb).2.1)
          (denseWorkLoop b targets idx reg w state nc nb).2.2 bs := by
  intro targets
  induction targets with
  | nil =>
      intro idx reg w state nc nb hcov _ _ _ _
      show reg.Extends reg ∧ (∀ i, reg.isInput i = reg.isInput i)
        ∧ (denseWorkView w).CoveredBy reg
        ∧ DenseDerivations.CoveredBy reg ([] : DenseDerivations p)
        ∧ DensePassCorrect reg.isInput (denseWorkView w) (denseWorkView w)
            ([] : DenseDerivations p) bs
      exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl, hcov,
        (by intro x hx; simp at hx), DensePassCorrect.refl reg.isInput (denseWorkView w) bs⟩
  | cons xs rest ih =>
      intro idx reg w state nc nb hcov hpos hbools hvs hidxB
      simp only [denseWorkLoop]
      rcases hstep : denseWorkStep b reg w state xs s!"rnc{nc}_{nb}_{idx}"
          with ⟨reg1, w1, derivs1, state1⟩
      have hsp := denseWorkStep_correct b reg w state xs s!"rnc{nc}_{nb}_{idx}" bs hcov hpos hbools
        hvs hidxB
      have hinv := denseWorkStep_inv b reg w state xs s!"rnc{nc}_{nb}_{idx}" hpos hbools hvs hidxB
      simp only [hstep] at hsp hinv
      obtain ⟨hs_ext, hs_ii, hs_cov, hs_dcov, hs_correct⟩ := hsp
      obtain ⟨hi_pos, hi_bools, hi_vs, hi_idxB⟩ := hinv
      rcases hrec : denseWorkLoop b rest (idx + 1) reg1 w1 state1
          (denseWorkNameCountsS derivs1 w1 state1 nc nb).1
          (denseWorkNameCountsS derivs1 w1 state1 nc nb).2
          with ⟨reg2, w2, derivs2⟩
      have hih := ih (idx + 1) reg1 w1 state1
          (denseWorkNameCountsS derivs1 w1 state1 nc nb).1
          (denseWorkNameCountsS derivs1 w1 state1 nc nb).2
          hs_cov hi_pos hi_bools hi_vs hi_idxB
      simp only [hrec] at hih
      obtain ⟨hr_ext, hr_ii, hr_cov, hr_dcov, hr_correct⟩ := hih
      refine ⟨hs_ext.trans hr_ext, fun i => (hr_ii i).trans (hs_ii i), hr_cov, ?_, ?_⟩
      · exact DenseDerivations.coveredBy_append
          (DenseDerivations.CoveredBy.mono hr_ext hs_dcov) hr_dcov
      · have hfe : reg2.isInput = reg1.isInput := funext hr_ii
        have hstepcert : DensePassCorrect reg2.isInput (denseWorkView w) (denseWorkView w1)
            derivs1 bs := by rw [hfe]; exact hs_correct
        exact hstepcert.andThen hr_correct

theorem denseWorkSeed_view (d : DenseConstraintSystem p) :
    denseWorkView (denseWorkSeed d) = d.filterConstraints (fun c => !denseIsZero c) := by
  simp [denseWorkView, denseWorkSeed, DenseConstraintSystem.filterConstraints]

set_option maxHeartbeats 1000000 in
theorem denseReencodeF_props (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    reg.Extends (denseReencodeF pw b reg bs facts d).1
    ∧ (denseReencodeF pw b reg bs facts d).2.1.CoveredBy (denseReencodeF pw b reg bs facts d).1
    ∧ DenseDerivations.CoveredBy (denseReencodeF pw b reg bs facts d).1
        (denseReencodeF pw b reg bs facts d).2.2
    ∧ DensePassCorrect (denseReencodeF pw b reg bs facts d).1.isInput d
        (denseReencodeF pw b reg bs facts d).2.1 (denseReencodeF pw b reg bs facts d).2.2 bs := by
  unfold denseReencodeF
  by_cases hpr : pw.isPrime = true
  · rw [if_pos hpr]
    haveI : Fact p.Prime := ⟨pw.correct hpr⟩
    extract_lets csVs svSet targets
    have hseedCov : (denseWorkView (denseWorkSeed d)).CoveredBy reg := by
      rw [denseWorkSeed_view]
      exact denseFilterConstraints_coveredBy hcov
    have hseedPos : (denseWorkSeed d).bounded = true →
        DenseWorkPosOk (denseWorkSeed d).lastPos (denseWorkSeed d).lastFold
          (denseWorkSeed d).cs := by intro hb; simp [denseWorkSeed] at hb
    have hseedBools : DenseWorkBoolsOk (denseWorkSeed d).bitSet (denseWorkSeed d).bools := by
      intro c hc; simp [denseWorkSeed] at hc
    set st : DenseReencodeCacheState p :=
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
        dWithin := false } with hst
    have hseedVars : DenseWorkVarsOk st.varSet (denseWorkSeed d) := by
      intro v hv
      rw [denseWorkSeed_view] at hv
      have hd := denseFilterConstraints_occ_sub d (fun c => !denseIsZero c) v hv
      rw [hst]
      show (Std.HashSet.ofList d.occ).contains v = true
      simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using hd
    have hseedIdxB : DenseBusIdxOk st (denseWorkSeed d) := by
      constructor
      · intro i bi hi v hv
        rw [hst]
        show i ∈ (denseCovBuild denseBIVars d.busInteractions).buckets.getD v []
        exact denseBuild_complete' denseBIVars d.busInteractions i bi (by simpa using hi) v hv
      · intro i bi hi hfold
        rw [hst]
        show ((d.busInteractions.zipIdx).foldl
          (fun s x => if denseBiHasFold x.1 then s.insert x.2 else s)
          (∅ : Std.HashSet Nat)).contains i = true
        simpa using denseFoldBisSeed_complete d.busInteractions 0 ∅ i bi (by simpa using hi) hfold
    obtain ⟨he, _, hc, hd, hcorr⟩ :=
      denseWorkLoop_correct b bs targets 0 reg (denseWorkSeed d) st
        (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length d.busInteractions.length
        hseedCov hseedPos hseedBools hseedVars hseedIdxB
    refine ⟨he, hc, hd, ?_⟩
    -- the seed drops trivially-true constraints, itself a verified step
    have hpre : DensePassCorrect
        (denseWorkLoop b targets 0 reg (denseWorkSeed d) st
          (d.algebraicConstraints.filter (fun c => !denseIsZero c)).length
          d.busInteractions.length).1.isInput d (denseWorkView (denseWorkSeed d))
        ([] : DenseDerivations p) bs := by
      rw [denseWorkSeed_view]
      exact DensePassCorrect.denseFilterConstraintsEntailed d bs _
        (fun c => !denseIsZero c) (fun c _ hk => denseIsZero_eval (by simpa using hk))
    simpa using hpre.andThen hcorr
  · rw [if_neg hpr]
    refine ⟨VarRegistry.Extends.refl reg, hcov, ?_, DensePassCorrect.refl reg.isInput d bs⟩
    intro x hx; simp at hx

/-- **Unproven on this branch (measurement).** The array-backed engine's obligations, in the shape
    `denseReencodeF_props` discharges for the list engine. -/
theorem denseRncF_props (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    reg.Extends (denseRncF pw b reg bs facts d).1
    ∧ (denseRncF pw b reg bs facts d).2.1.CoveredBy (denseRncF pw b reg bs facts d).1
    ∧ DenseDerivations.CoveredBy (denseRncF pw b reg bs facts d).1
        (denseRncF pw b reg bs facts d).2.2
    ∧ DensePassCorrect (denseRncF pw b reg bs facts d).1.isInput d
        (denseRncF pw b reg bs facts d).2.1 (denseRncF pw b reg bs facts d).2.2 bs := by
  sorry

/-- The registered witness re-encoding pass (see `denseRncF` in `Reencode.lean`). -/
def denseReencodePass (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofExtending (denseRncF pw b)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.2.1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.2.2)

end ApcOptimizer.Dense
