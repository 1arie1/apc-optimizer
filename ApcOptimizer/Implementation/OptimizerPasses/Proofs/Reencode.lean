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

/-! ## The array engine

The engine of `Reencode.lean` keeps the system on stable array positions with `VarId`-keyed indexes.
Everything it computes off those indexes is *untrusted*: the certificate below is the audited
`denseCheckReencode` on the covered set the index gathered, and the accept's edits are re-derived
from each position's current content, so an index that over-reports costs a decision and never
soundness. Two facts carry the correctness: the gathered covered set *is* the filter
(`denseRncEs_eq`, from anchor completeness), and the written state's view *is*
`denseReencodeOut` of the old view with trivially-true constraints dropped (`denseRncWrite_view`) —
the same two facts the list engine established with `denseWorkView_check` and `denseWorkOut_view`. -/

/-! ### Expression predicate characterisations -/

theorem denseHasVar_iff (e : DenseExpr p) : e.hasVar = true ↔ e.vars ≠ [] := by
  induction e with
  | const n => simp [DenseExpr.hasVar, DenseExpr.vars]
  | var y => simp [DenseExpr.hasVar, DenseExpr.vars]
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.hasVar, DenseExpr.vars, Bool.or_eq_true, iha, ihb,
        ne_eq, List.append_eq_nil_iff, not_and_or]

theorem denseVarsInF_iff (xs : List VarId) (e : DenseExpr p) :
    e.varsInF xs = true ↔ ∀ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [DenseExpr.varsInF, DenseExpr.vars]
  | var y =>
      simp only [DenseExpr.varsInF, DenseExpr.vars, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h v hv; rw [hv]; exact denseContainsFast_sound xs y h
      · intro h; exact denseContainsFast_of_mem xs y (h y rfl)
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.varsInF, DenseExpr.vars, Bool.and_eq_true, iha, ihb, List.mem_append]
      exact ⟨fun ⟨ha, hb⟩ v hv => hv.elim (ha v) (hb v),
        fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩⟩

theorem denseSharesVarIn_iff (xs : List VarId) (e : DenseExpr p) :
    e.sharesVarIn xs = true ↔ ∃ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [DenseExpr.sharesVarIn, DenseExpr.vars]
  | var y =>
      simp only [DenseExpr.sharesVarIn, DenseExpr.vars, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h; exact ⟨y, rfl, denseContainsFast_sound xs y h⟩
      · rintro ⟨v, hv, hx⟩; rw [hv] at hx; exact denseContainsFast_of_mem xs y hx
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.sharesVarIn, DenseExpr.vars, Bool.or_eq_true, iha, ihb, List.mem_append]
      constructor
      · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
        · exact ⟨v, Or.inl hv, hx⟩
        · exact ⟨v, Or.inr hv, hx⟩
      · rintro ⟨v, hv | hv, hx⟩
        · exact Or.inl ⟨v, hv, hx⟩
        · exact Or.inr ⟨v, hv, hx⟩

/-! ### The capped variable arrays

`denseRncCapVars` stops at nine distinct variables, so it is exact below the cap; every consumer
either stays below it or falls back to the tree walk. -/

theorem denseRncCapGo_mono (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId),
      (∀ v ∈ acc, v ∈ denseRncCapGo cap e acc) ∧ acc.size ≤ (denseRncCapGo cap e acc).size := by
  intro e
  induction e with
  | const n => intro acc; exact ⟨fun v hv => hv, Nat.le_refl _⟩
  | var y =>
      intro acc
      rw [denseRncCapGo]
      split
      · exact ⟨fun v hv => hv, Nat.le_refl _⟩
      · exact ⟨fun v hv => by simp [hv], by simp⟩
  | add a b iha ihb | mul a b iha ihb =>
      intro acc
      rw [denseRncCapGo]
      obtain ⟨hma, hsa⟩ := iha acc
      split
      · exact ⟨hma, hsa⟩
      · obtain ⟨hmb, hsb⟩ := ihb (denseRncCapGo cap a acc)
        exact ⟨fun v hv => hmb v (hma v hv), Nat.le_trans hsa hsb⟩

theorem denseRncCapGo_sound (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId) (v : VarId),
      v ∈ denseRncCapGo cap e acc → v ∈ acc ∨ v ∈ e.vars := by
  intro e
  induction e with
  | const n => intro acc v hv; exact Or.inl hv
  | var y =>
      intro acc v hv
      rw [denseRncCapGo] at hv
      split at hv
      · exact Or.inl hv
      · rcases Array.mem_push.1 hv with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [DenseExpr.vars, h])
  | add a b iha ihb | mul a b iha ihb =>
      intro acc v hv
      rw [denseRncCapGo] at hv
      split at hv
      · rcases iha acc v hv with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [DenseExpr.vars, h])
      · rcases ihb _ v hv with h | h
        · rcases iha acc v h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by simp [DenseExpr.vars, h'])
        · exact Or.inr (by simp [DenseExpr.vars, h])

/-- Below the cap the walk never bailed out, so every variable of the expression is present. -/
theorem denseRncCapGo_complete (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId),
      (denseRncCapGo cap e acc).size < cap → ∀ v ∈ e.vars, v ∈ denseRncCapGo cap e acc := by
  intro e
  induction e with
  | const n => intro acc _ v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro acc hlt v hv
      have hy : v = y := by simpa [DenseExpr.vars] using hv
      subst hy
      rw [denseRncCapGo] at hlt ⊢
      split at hlt
      · next hc =>
          rw [if_pos hc]
          have hc' : cap ≤ acc.size ∨ acc.contains v = true := by simpa using hc
          rcases hc' with h | h
          · omega
          · exact Array.mem_of_contains_eq_true h
      · next hc =>
          rw [if_neg hc]
          simp
  | add a b iha ihb | mul a b iha ihb =>
      intro acc hlt v hv
      rw [denseRncCapGo] at hlt ⊢
      split at hlt
      · next hsplit => rw [if_pos hsplit]; omega
      · next hsplit =>
        rw [if_neg hsplit]
        have hva : ∀ w ∈ a.vars, w ∈ denseRncCapGo cap a acc := iha acc (by omega)
        have hmono := (denseRncCapGo_mono cap b (denseRncCapGo cap a acc)).1
        rcases List.mem_append.1 (by simpa [DenseExpr.vars] using hv) with h | h
        · exact hmono v (hva v h)
        · exact ihb _ hlt v h

/-- The capped array is exact when it stayed below the cap. -/
theorem denseRncCapVars_mem_iff {c : DenseExpr p} (h : (denseRncCapVars c).size ≤ 8) (v : VarId) :
    v ∈ denseRncCapVars c ↔ v ∈ c.vars := by
  constructor
  · intro hv
    rcases denseRncCapGo_sound 9 c #[] v hv with h' | h'
    · simp at h'
    · exact h'
  · intro hv
    exact denseRncCapGo_complete 9 c #[] (by simpa [denseRncCapVars] using Nat.lt_succ_of_le h) v hv

theorem denseRncCapVars_size_pos_iff {c : DenseExpr p} (h : (denseRncCapVars c).size ≤ 8) :
    1 ≤ (denseRncCapVars c).size ↔ c.hasVar = true := by
  rw [denseHasVar_iff]
  constructor
  · intro hpos hnil
    have hmem : (denseRncCapVars c)[0] ∈ denseRncCapVars c := Array.getElem_mem (by omega)
    rw [denseRncCapVars_mem_iff h, hnil] at hmem
    simp at hmem
  · intro hne
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    have hmem : v ∈ denseRncCapVars c := (denseRncCapVars_mem_iff h v).2 hv
    simpa using Array.size_pos_of_mem hmem

theorem denseRncSubset_eq {xs : List VarId} {c : DenseExpr p}
    (h : (denseRncCapVars c).size ≤ 8) :
    denseRncSubset xs (denseRncCapVars c) = c.varsInF xs := by
  unfold denseRncSubset
  cases hv : c.varsInF xs with
  | true =>
      have hall := (denseVarsInF_iff xs c).1 hv
      refine Array.all_eq_true'.2 (fun w hw => ?_)
      exact denseContainsFast_of_mem xs w (hall w ((denseRncCapVars_mem_iff h w).1 hw))
  | false =>
      have hnot : ¬ (∀ w ∈ c.vars, w ∈ xs) := fun hall => by
        rw [(denseVarsInF_iff xs c).2 hall] at hv; exact Bool.noConfusion hv
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      exact hnot (fun w hw => denseContainsFast_sound xs w
        (Array.all_eq_true'.1 hcon w ((denseRncCapVars_mem_iff h w).2 hw)))

/-- The array-level covered test is `denseCoveredBy`. -/
theorem denseRncCovered_eq (xs : List VarId) (c : DenseExpr p) :
    denseRncCovered xs (denseRncCapVars c) c = denseCoveredBy xs c := by
  unfold denseRncCovered
  split
  · next h =>
      rw [denseCoveredBy, denseRncSubset_eq h]
      cases hv : c.hasVar with
      | true => simp [(denseRncCapVars_size_pos_iff h).2 hv]
      | false =>
          have hz : ¬ (1 ≤ (denseRncCapVars c).size) := fun hpos => by
            rw [(denseRncCapVars_size_pos_iff h).1 hpos] at hv; exact Bool.noConfusion hv
          simp [hz]
  · rfl

/-- The array-level `sharesVarIn` test. -/
theorem denseRncShares_eq (xs : List VarId) (c : DenseExpr p) :
    denseRncShares xs (denseRncCapVars c) c = c.sharesVarIn xs := by
  unfold denseRncShares
  split
  · next h =>
      cases hs : c.sharesVarIn xs with
      | true =>
          obtain ⟨w, hw, hx⟩ := (denseSharesVarIn_iff xs c).1 hs
          exact Array.any_eq_true'.2
            ⟨w, (denseRncCapVars_mem_iff h w).2 hw, denseContainsFast_of_mem xs w hx⟩
      | false =>
          by_contra hcon
          rw [Bool.not_eq_false] at hcon
          obtain ⟨w, hw, hx⟩ := Array.any_eq_true'.1 hcon
          have := (denseSharesVarIn_iff xs c).2
            ⟨w, (denseRncCapVars_mem_iff h w).1 hw, denseContainsFast_sound xs w hx⟩
          rw [hs] at this
          exact Bool.noConfusion this
  · rfl

/-! ### State invariants

Each says the index over-approximates nothing it must find. All are maintained by the write and
consumed either by the covered gather or by the accept's edit list. -/

/-- `cvs` mirrors `cs` positionwise. -/
def DenseRncCvsOk (st : DenseRncState p) : Prop :=
  ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c → st.cvs[i]? = some (denseRncCapVars c)

/-- Every position is listed under its first variable. -/
def DenseRncAnchorOk (st : DenseRncState p) : Prop :=
  ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    ∀ v ∈ denseRncAnchorVars c, i ∈ st.anchor.buckets.getD v []

/-- Every position is listed under each of its variables, and every foldable one is recorded. -/
def DenseRncUseOk (st : DenseRncState p) : Prop :=
  (∀ m, st.useCs = some m → ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    ∀ v ∈ c.vars, i ∈ denseRncBGet m v) ∧
  (∀ s, st.foldCs = some s → ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    denseRncHasFold c = true → s.contains i = true)

def DenseRncBusOk (st : DenseRncState p) : Prop :=
  (∀ m, st.useBis = some m → ∀ (i : Nat) (bi : BusInteraction (DenseExpr p)),
    st.bis[i]? = some bi → ∀ v ∈ denseBIVars bi, i ∈ denseRncBGet m v) ∧
  (∀ s, st.foldBis = some s → ∀ (i : Nat) (bi : BusInteraction (DenseExpr p)),
    st.bis[i]? = some bi → denseRncBiHasFold bi = true → s.contains i = true)

/-- Every live variable is `denseRncSeen` — what decides bit freshness in `O(|bits|)`. -/
def DenseRncVarsOk (st : DenseRncState p) : Prop :=
  ∀ v ∈ (denseRncView st).occ, denseRncSeen st v = true

/-! ### The gathered covered set is the filter -/

theorem denseCoveredIdxPos_map_snd (idx : DenseCovIndex) (arr : Array (DenseExpr p))
    (xs : List VarId) :
    (denseCoveredIdxPos idx arr xs).map Prod.snd
      = denseCoveredIdx idx arr (denseCoveredBy xs) xs := by
  unfold denseCoveredIdxPos denseCoveredIdx
  rw [List.map_filterMap]
  refine List.filterMap_congr (fun i _ => ?_)
  by_cases h : i < arr.size
  · simp only [dif_pos h]
    by_cases hq : denseCoveredBy xs arr[i] = true <;> simp [hq]
  · simp only [dif_neg h, Option.map_none]

/-- A constraint with a variable has a first capped variable, so it is anchored. -/
theorem denseRncAnchorVars_of_hasVar {c : DenseExpr p} (h : c.hasVar = true) :
    ∃ v, denseRncAnchorVars c = [v] ∧ v ∈ c.vars := by
  have hpos : 0 < (denseRncCapVars c).size := by
    by_cases hcap : (denseRncCapVars c).size ≤ 8
    · exact (denseRncCapVars_size_pos_iff hcap).2 h
    · omega
  refine ⟨(denseRncCapVars c)[0], ?_, ?_⟩
  · unfold denseRncAnchorVars
    rw [Array.getElem?_eq_getElem hpos]
  · rcases denseRncCapGo_sound 9 c #[] _ (Array.getElem_mem hpos) with h' | h'
    · simp at h'
    · exact h'

/-- The covered constraints the index gathers are exactly the covered constraints of the view. -/
theorem denseRncEs_eq {st : DenseRncState p} (hanchor : DenseRncAnchorOk st) (xs : List VarId) :
    (denseCoveredIdxPos st.anchor st.cs xs).map Prod.snd
      = denseCoveredCsOf (denseRncView st) xs := by
  rw [denseCoveredIdxPos_map_snd]
  have hcomplete : ∀ (i : Nat) (hi : i < st.cs.toList.length),
      denseCoveredBy xs st.cs.toList[i] = true → i ∈ denseCandidates st.anchor xs := by
    intro i hi hcov
    have hget : st.cs[i]? = some st.cs.toList[i] := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi]
    have hhv : (st.cs.toList[i]).hasVar = true := by
      rw [denseCoveredBy, Bool.and_eq_true] at hcov; exact hcov.1
    obtain ⟨v, hav, hvmem⟩ := denseRncAnchorVars_of_hasVar hhv
    have hvxs : v ∈ xs := by
      rw [denseCoveredBy, Bool.and_eq_true] at hcov
      exact (denseVarsInF_iff xs _).1 hcov.2 v hvmem
    exact denseMem_candidates st.anchor xs v i hvxs
      (hanchor i _ hget v (by rw [hav]; exact List.mem_singleton_self v))
  have hfilter := denseCoveredIdx_eq_filter_of_complete st.anchor st.cs.toList
    (denseCoveredBy xs) xs hcomplete
  rw [Array.toArray_toList] at hfilter
  rw [hfilter]
  show st.cs.toList.filter (denseCoveredBy xs) = _
  unfold denseCoveredCsOf denseRncView
  show _ = ((st.cs.filter (fun c => !denseIsZero c)).toList).filter (denseCoveredBy xs)
  rw [Array.toList_filter]
  exact (List.filter_filter_of st.cs.toList _ _
    (fun c _ hz => denseIsZero_not_covered (by simpa using hz))).symm

/-- The one-pass `(hasVar, hasConstFoldableNode)` walk computes both. -/
theorem denseRncFoldPair_eq (e : DenseExpr p) :
    denseRncFoldPair e = (e.hasVar, e.hasConstFoldableNode) := by
  induction e with
  | const n => rfl
  | var y => rfl
  | add a b iha ihb | mul a b iha ihb =>
      simp only [denseRncFoldPair, iha, ihb, DenseExpr.hasVar, DenseExpr.hasConstFoldableNode]

theorem denseRncHasFold_eq (e : DenseExpr p) : denseRncHasFold e = e.hasConstFoldableNode := by
  rw [denseRncHasFold, denseRncFoldPair_eq]

theorem denseRncBiHasFold_eq (bi : BusInteraction (DenseExpr p)) :
    denseRncBiHasFold bi = denseBiHasFold bi := by
  unfold denseRncBiHasFold denseBiHasFold
  rw [denseRncHasFold_eq]
  have : ∀ (l : List (DenseExpr p)), l.any denseRncHasFold
      = l.any (fun e => e.hasConstFoldableNode) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih => rw [List.any_cons, List.any_cons, denseRncHasFold_eq, ih]
  rw [this]

/-! ### The certificate

`denseRncCert` is the audited `denseCheckReencode` with two substitutions: the covered set comes from
the index (`denseRncEs_eq`) and freshness from `varSeen` (the invariant plus
`denseFreshScan_of_notMemOcc`). -/

theorem denseRncCert_sound {st : DenseRncState p} {xs : List VarId} {cd : DenseRncCand p}
    (hanchor : DenseRncAnchorOk st) (hvars : DenseRncVarsOk st)
    (hes : cd.es = (denseCoveredIdxPos st.anchor st.cs xs).map Prod.snd)
    (h : denseRncCert st xs cd = true) :
    denseCheckReencode (denseRncView st) xs cd.bits cd.hm.get = true := by
  rw [denseRncCert, Bool.and_eq_true] at h
  obtain ⟨hfresh, hchk⟩ := h
  refine denseCheckReencode_of_parts _ xs cd.bits cd.hm.get ?_ ?_
  · rw [denseCheckReencodeNoFresh_eq_Es, ← denseRncEs_eq hanchor xs, ← hes]
    exact hchk
  · refine denseFreshScan_of_notMemOcc _ cd.bits ?_
    intro b hb hmem
    have hseen := hvars b hmem
    have hnb := List.all_eq_true.mp hfresh b hb
    rw [hseen] at hnb
    exact Bool.noConfusion hnb

/-! ### Writing a list of positional edits into an array

The accept installs its edits by folding `Array.setIfInBounds` over distinct positions. These three
lemmas are what turn that fold into a positionwise map. -/

section ArrFold
variable {α : Type}

def denseArrSet (a : Array α) (q : Nat × α) : Array α := a.setIfInBounds q.1 q.2

theorem denseArrFold_size (l : List (Nat × α)) :
    ∀ (a : Array α), (l.foldl denseArrSet a).size = a.size := by
  induction l with
  | nil => intro a; rfl
  | cons q rest ih => intro a; rw [List.foldl_cons, ih]; simp [denseArrSet]

theorem denseArrFold_stable (l : List (Nat × α)) :
    ∀ (a : Array α) (j : Nat), j ∉ l.map Prod.fst → (l.foldl denseArrSet a)[j]? = a[j]? := by
  induction l with
  | nil => intro a j _; rfl
  | cons q rest ih =>
      intro a j hj
      simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [List.foldl_cons, ih _ j hj.2, denseArrSet,
        Array.getElem?_setIfInBounds_ne (fun h => hj.1 h.symm)]

theorem denseArrFold_hit (l : List (Nat × α)) :
    ∀ (a : Array α) (i : Nat) (x : α), (l.map Prod.fst).Nodup → (i, x) ∈ l → i < a.size →
      (l.foldl denseArrSet a)[i]? = some x := by
  induction l with
  | nil => intro a i x _ hmem _; simp at hmem
  | cons q rest ih =>
      intro a i x hnd hmem hlt
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hmem with heq | hmem'
      · subst heq
        rw [List.foldl_cons, denseArrFold_stable rest _ i hnd.1, denseArrSet,
          Array.getElem?_setIfInBounds_self_of_lt hlt]
      · rw [List.foldl_cons]
        exact ih _ i x hnd.2 hmem' (by rw [denseArrSet]; simpa using hlt)

end ArrFold

/-! ### The accept's write

`denseRncWrite` installs the constraint edits, the bus edits and the booleanity constraints. Each
setter touches one field at one position, so the fold is the positionwise `denseTombify` map — and
from there `denseTombify_filter` (the list engine's lemma) finishes the view. -/

theorem denseRncCsStep_cs (ctx : DenseRncCtx p) (st : DenseRncState p) (e : DenseRncCsEdit p) :
    (denseRncCsStep ctx st e).cs = st.cs.setIfInBounds e.pos (e.content ctx) := by
  cases e <;> rfl

theorem denseRncCsFold_cs (ctx : DenseRncCtx p) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p),
      (es.foldl (denseRncCsStep ctx) st).cs
        = (es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih =>
      intro st
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, denseRncCsStep_cs]
      rfl

theorem denseRncBiFold_bis :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p),
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).bis = es.foldl denseArrSet st.bis := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih, List.foldl_cons]; rfl

theorem denseRncCsFold_bis (ctx : DenseRncCtx p) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p),
      (es.foldl (denseRncCsStep ctx) st).bis = st.bis := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih]; cases e <;> rfl

theorem denseRncBiFold_cs :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p),
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).cs = st.cs := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih]; rfl

theorem denseRncBoolFold_cs :
    ∀ (bits : List VarId) (st : DenseRncState p),
      (bits.foldl (fun st b => st.pushBool b) st).cs
        = st.cs ++ (bits.map (denseBoolConstraint (p := p))).toArray := by
  intro bits
  induction bits with
  | nil => intro st; simp
  | cons b rest ih =>
      intro st
      rw [List.foldl_cons, ih, List.map_cons]
      show (st.cs.push (denseBoolConstraint b)) ++ _ = _
      simp

theorem denseRncBoolFold_bis :
    ∀ (bits : List VarId) (st : DenseRncState p),
      (bits.foldl (fun st b => st.pushBool b) st).bis = st.bis := by
  intro bits
  induction bits with
  | nil => intro st; rfl
  | cons b rest ih => intro st; rw [List.foldl_cons, ih]; rfl

/-! ### What the edit builders produce

Three facts per builder: the positions are a sublist of the (duplicate-free) candidate list, each
edit installs the positionwise `denseTombify` (resp. the gated bus rewrite), and every position the
rewrite can change is listed. -/

theorem denseRncPosList_nodup (bs : Array (Array Nat)) (xs : List VarId) (extra : List Nat) :
    (denseRncPosList bs xs extra).Nodup :=
  Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h)

theorem denseRncPosList_mem (bs : Array (Array Nat)) (xs : List VarId) (extra : List Nat)
    (i : Nat) (h : (∃ v ∈ xs, i ∈ denseRncBGet bs v) ∨ i ∈ extra) :
    i ∈ denseRncPosList bs xs extra := by
  rw [denseRncPosList, Std.HashSet.mem_toList, mem_foldl_insert]
  refine Or.inr ?_
  rw [List.mem_append]
  rcases h with ⟨v, hv, hi⟩ | hi
  · exact Or.inl (List.mem_flatMap.2 ⟨v, hv, by simpa using hi⟩)
  · exact Or.inr hi

section CsEdits
variable (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId) (cd : DenseRncCand p)

/-- The builder's per-position body, as a standalone function so the three lemmas share it. -/
private def csBody (i : Nat) (acc : List (DenseRncCsEdit p) × Bool) :
    List (DenseRncCsEdit p) × Bool :=
  match st.cs[i]?, st.cvs[i]? with
  | some c, some vs =>
    if denseRncCovered xs vs c then (.tomb i :: acc.1, acc.2)
    else if denseRncShares xs vs c || denseRncHasFold c then
      let c' := denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get c
      let cv' := denseRncCapVars c'
      (.cst i c' cv' (denseRncFullVars c' cv') :: acc.1,
        acc.2 && decide (c'.degree ≤ ctx.dmaxC))
    else acc
  | _, _ => acc

private theorem csEdits_eq_foldr :
    (denseRncCsEdits ctx st xs cd).1
      = ((denseRncPosList (match st.useCs with | some m => m | none => #[]) xs
          (match st.foldCs with | some s => s | none => ∅).toList).foldr (csBody ctx st xs cd)
          ([], true)).1 := rfl

private theorem csBody_sublist (l : List Nat) :
    ((l.foldr (csBody ctx st xs cd) ([], true)).1.map DenseRncCsEdit.pos).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i rest ih =>
      rw [List.foldr_cons]
      cases hc : st.cs[i]? with
      | none => simpa only [csBody, hc] using ih.trans (List.sublist_cons_self i rest)
      | some c =>
        cases hvs : st.cvs[i]? with
        | none => simpa only [csBody, hc, hvs] using ih.trans (List.sublist_cons_self i rest)
        | some vs =>
          simp only [csBody, hc, hvs]
          by_cases hcov : denseRncCovered xs vs c = true
          · rw [if_pos hcov]
            simpa only [List.map_cons, DenseRncCsEdit.pos] using List.cons_sublist_cons.2 ih
          · rw [if_neg hcov]
            by_cases hg : denseRncShares xs vs c || denseRncHasFold c
            · rw [if_pos hg]
              simpa only [List.map_cons, DenseRncCsEdit.pos] using List.cons_sublist_cons.2 ih
            · rw [if_neg hg]
              exact ih.trans (List.sublist_cons_self i rest)

private theorem csBody_content (hcvs : DenseRncCvsOk st)
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (l : List Nat) :
    ∀ e ∈ (l.foldr (csBody ctx st xs cd) ([], true)).1, ∃ c, st.cs[e.pos]? = some c ∧
      e.content ctx
        = denseTombify xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get c := by
  induction l with
  | nil => intro e he; simp at he
  | cons i rest ih =>
      intro e he
      rw [List.foldr_cons] at he
      cases hc : st.cs[i]? with
      | none => exact ih e (by simpa only [csBody, hc] using he)
      | some c =>
        have hvs : st.cvs[i]? = some (denseRncCapVars c) := hcvs i c hc
        simp only [csBody, hc, hvs] at he
        rw [denseRncCovered_eq] at he
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov] at he
          rcases List.mem_cons.1 he with rfl | he'
          · exact ⟨c, by simpa [DenseRncCsEdit.pos] using hc,
              by simp [DenseRncCsEdit.content, hzero, denseTombify, hcov]⟩
          · exact ih e he'
        · rw [if_neg hcov] at he
          by_cases hg : denseRncShares xs (denseRncCapVars c) c || denseRncHasFold c
          · rw [if_pos hg] at he
            rcases List.mem_cons.1 he with rfl | he'
            · refine ⟨c, by simpa [DenseRncCsEdit.pos] using hc, ?_⟩
              have hcov' : denseCoveredBy xs c = false := by simpa using hcov
              simp only [DenseRncCsEdit.content, denseTombify, hcov', if_false,
                Bool.false_eq_true]
            · exact ih e he'
          · rw [if_neg hg] at he
            exact ih e he

private theorem csBody_complete (hcvs : DenseRncCvsOk st) (l : List Nat) (j : Nat)
    (c : DenseExpr p) (hj : j ∈ l) (hc : st.cs[j]? = some c)
    (hfires : denseCoveredBy xs c = true ∨ c.sharesVarIn xs = true ∨
      c.hasConstFoldableNode = true) :
    j ∈ (l.foldr (csBody ctx st xs cd) ([], true)).1.map DenseRncCsEdit.pos := by
  induction l with
  | nil => simp at hj
  | cons i rest ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj'
      · have hvs : st.cvs[j]? = some (denseRncCapVars c) := hcvs j c hc
        simp only [csBody, hc, hvs]
        rw [denseRncCovered_eq]
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov]; simp [DenseRncCsEdit.pos]
        · rw [if_neg hcov, denseRncShares_eq, denseRncHasFold_eq]
          have hg : (c.sharesVarIn xs || c.hasConstFoldableNode) = true := by
            rcases hfires with h | h | h
            · exact absurd h hcov
            · simp [h]
            · simp [h]
          rw [if_pos hg]
          simp [DenseRncCsEdit.pos]
      · have hrec := ih hj'
        cases hc0 : st.cs[i]? with
        | none => simpa only [csBody, hc0] using hrec
        | some c0 =>
          cases hvs0 : st.cvs[i]? with
          | none => simpa only [csBody, hc0, hvs0] using hrec
          | some vs0 =>
            simp only [csBody, hc0, hvs0]
            by_cases hcov : denseRncCovered xs vs0 c0 = true
            · rw [if_pos hcov]; simpa using Or.inr hrec
            · rw [if_neg hcov]
              by_cases hg : denseRncShares xs vs0 c0 || denseRncHasFold c0
              · rw [if_pos hg]; simpa using Or.inr hrec
              · rw [if_neg hg]; exact hrec

end CsEdits

section BiEdits
variable (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId) (cd : DenseRncCand p)

private def biBody (i : Nat) (acc : List (Nat × BusInteraction (DenseExpr p)) × Bool) :
    List (Nat × BusInteraction (DenseExpr p)) × Bool :=
  match st.bis[i]? with
  | some bi =>
    if bi.multiplicity.sharesVarIn xs || denseRncHasFold bi.multiplicity
        || bi.payload.any (fun e => e.sharesVarIn xs || denseRncHasFold e) then
      let bi' : BusInteraction (DenseExpr p) :=
        { bi with
          multiplicity := denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get)
            cd.patts.get bi.multiplicity,
          payload := bi.payload.map
            (denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get) }
      ((i, bi') :: acc.1,
        acc.2 && decide (bi'.multiplicity.degree ≤ ctx.dmaxB)
          && bi'.payload.all (fun e => decide (e.degree ≤ ctx.dmaxB)))
    else acc
  | none => acc

private theorem biEdits_eq_foldr :
    (denseRncBiEdits ctx st xs cd).1
      = ((denseRncPosList (match st.useBis with | some m => m | none => #[]) xs
          (match st.foldBis with | some s => s | none => ∅).toList).foldr (biBody ctx st xs cd)
          ([], true)).1 := rfl

/-- The gate test the builder uses is `denseBiGateFires`. -/
private theorem biBody_fires (bi : BusInteraction (DenseExpr p)) :
    (bi.multiplicity.sharesVarIn xs || denseRncHasFold bi.multiplicity
      || bi.payload.any (fun e => e.sharesVarIn xs || denseRncHasFold e))
      = denseBiGateFires xs bi := by
  unfold denseBiGateFires
  rw [denseRncHasFold_eq]
  have hp : ∀ (l : List (DenseExpr p)),
      l.any (fun e => e.sharesVarIn xs || denseRncHasFold e)
        = l.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih => rw [List.any_cons, List.any_cons, denseRncHasFold_eq, ih]
  rw [hp]

private theorem biBody_sublist (l : List Nat) :
    ((l.foldr (biBody ctx st xs cd) ([], true)).1.map Prod.fst).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i rest ih =>
      rw [List.foldr_cons]
      cases hb : st.bis[i]? with
      | none => simpa only [biBody, hb] using ih.trans (List.sublist_cons_self i rest)
      | some bi =>
        simp only [biBody, hb]
        split
        · simpa only [List.map_cons] using List.cons_sublist_cons.2 ih
        · exact ih.trans (List.sublist_cons_self i rest)

private theorem biBody_content (l : List Nat) :
    ∀ q ∈ (l.foldr (biBody ctx st xs cd) ([], true)).1, ∃ bi, st.bis[q.1]? = some bi ∧
      q.2 = denseBIRewriteGate xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get bi := by
  induction l with
  | nil => intro q hq; simp at hq
  | cons i rest ih =>
      intro q hq
      rw [List.foldr_cons] at hq
      cases hb : st.bis[i]? with
      | none => exact ih q (by simpa only [biBody, hb] using hq)
      | some bi =>
        simp only [biBody, hb] at hq
        split at hq
        · next hgate =>
            rcases List.mem_cons.1 hq with rfl | hq'
            · refine ⟨bi, hb, ?_⟩
              have hgate' : (bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
                  || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode)) = true := by
                rw [biBody_fires (p := p) xs bi] at hgate
                simpa [denseBiGateFires] using hgate
              unfold denseBIRewriteGate
              rw [if_pos (by simpa using hgate')]
              simp only [denseGroupRewriteGate_eq]
            · exact ih q hq'
        · exact ih q hq

private theorem biBody_complete (l : List Nat) (j : Nat) (bi : BusInteraction (DenseExpr p))
    (hj : j ∈ l) (hb : st.bis[j]? = some bi) (hfires : denseBiGateFires xs bi = true) :
    j ∈ (l.foldr (biBody ctx st xs cd) ([], true)).1.map Prod.fst := by
  induction l with
  | nil => simp at hj
  | cons i rest ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj'
      · simp only [biBody, hb]
        rw [if_pos (by rw [biBody_fires]; exact hfires)]
        simp
      · have hrec := ih hj'
        cases hb0 : st.bis[i]? with
        | none => simpa only [biBody, hb0] using hrec
        | some bi0 =>
          simp only [biBody, hb0]
          split
          · simpa using Or.inr hrec
          · exact hrec

end BiEdits

/-! ### The write installs the positionwise `denseTombify` -/

theorem denseRncCsEdits_nodup (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ((denseRncCsEdits ctx st xs cd).1.map DenseRncCsEdit.pos).Nodup := by
  rw [csEdits_eq_foldr]
  exact (denseRncPosList_nodup _ xs _).sublist (csBody_sublist ctx st xs cd _)

theorem denseRncBiEdits_nodup (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ((denseRncBiEdits ctx st xs cd).1.map Prod.fst).Nodup := by
  rw [biEdits_eq_foldr]
  exact (denseRncPosList_nodup _ xs _).sublist (biBody_sublist ctx st xs cd _)

theorem denseRncCsEdits_complete {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf) :
    ∀ (j : Nat) (c : DenseExpr p), st.cs[j]? = some c →
      (denseCoveredBy xs c = true ∨ c.sharesVarIn xs = true ∨ c.hasConstFoldableNode = true) →
      j ∈ (denseRncCsEdits ctx st xs cd).1.map DenseRncCsEdit.pos := by
  intro j c hc hfires
  rw [csEdits_eq_foldr]
  refine csBody_complete ctx st xs cd hcvs _ j c ?_ hc hfires
  rw [hm, hs]
  refine denseRncPosList_mem _ _ _ j ?_
  rcases hfires with hcov | hsh | hfd
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs c).1 (denseCoveredBy_sharesVarIn hcov)
    exact Or.inl ⟨v, hx, huse.1 m hm j c hc v hv⟩
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs c).1 hsh
    exact Or.inl ⟨v, hx, huse.1 m hm j c hc v hv⟩
  · refine Or.inr ?_
    have hcontains := huse.2 sf hs j c hc (by rw [denseRncHasFold_eq]; exact hfd)
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    exact hcontains

theorem denseRncBiEdits_complete {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hbus : DenseRncBusOk st) (hm : st.useBis = some m) (hs : st.foldBis = some sf) :
    ∀ (j : Nat) (bi : BusInteraction (DenseExpr p)), st.bis[j]? = some bi →
      denseBiGateFires xs bi = true → j ∈ (denseRncBiEdits ctx st xs cd).1.map Prod.fst := by
  intro j bi hb hfires
  rw [biEdits_eq_foldr]
  refine biBody_complete ctx st xs cd _ j bi ?_ hb hfires
  rw [hm, hs]
  refine denseRncPosList_mem _ _ _ j ?_
  rw [denseBiGateFires, Bool.or_eq_true, Bool.or_eq_true] at hfires
  rcases hfires with (hmul | hfd) | hpl
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs _).1 hmul
    exact Or.inl ⟨v, hx, hbus.1 m hm j bi hb v (by simp [denseBIVars, hv])⟩
  · refine Or.inr ?_
    have hcontains := hbus.2 sf hs j bi hb (by
      rw [denseRncBiHasFold_eq]; simp [denseBiHasFold, hfd])
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    exact hcontains
  · rw [List.any_eq_true] at hpl
    obtain ⟨e, he, hor⟩ := hpl
    rw [Bool.or_eq_true] at hor
    rcases hor with hsh | hfd
    · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs e).1 hsh
      refine Or.inl ⟨v, hx, hbus.1 m hm j bi hb v ?_⟩
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨e, he, hv⟩
    · refine Or.inr ?_
      have hcontains := hbus.2 sf hs j bi hb (by
        rw [denseRncBiHasFold_eq]
        simp only [denseBiHasFold, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨e, he, hfd⟩)
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
      exact hcontains

/-- The constraint array after the write: the positionwise tombify, then the booleanity
    constraints. -/
theorem denseRncWrite_cs_toList {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf) :
    (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1).cs.toList
      = st.cs.toList.map (denseTombify xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get)
        ++ cd.bits.map denseBoolConstraint := by
  set σ := denseGroupSubst xs cd.hm.get with hσ
  set patts := cd.patts.get with hpatts
  set es := (denseRncCsEdits ctx st xs cd).1 with hes
  have hcs : (denseRncWrite ctx st cd.bits es (denseRncBiEdits ctx st xs cd).1).cs
      = (es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs
        ++ (cd.bits.map (denseBoolConstraint (p := p))).toArray := by
    show ((cd.bits.foldl (fun st b => st.pushBool b)
      (((denseRncBiEdits ctx st xs cd).1).foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (es.foldl (denseRncCsStep ctx) st))).domReset).cs = _
    show (cd.bits.foldl (fun st b => st.pushBool b)
      (((denseRncBiEdits ctx st xs cd).1).foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (es.foldl (denseRncCsStep ctx) st))).cs = _
    rw [denseRncBoolFold_cs, denseRncBiFold_cs, denseRncCsFold_cs]
  rw [hcs]
  have hlen : ((es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs).size
      = st.cs.size := denseArrFold_size _ _
  rw [Array.toList_append, List.toList_toArray]
  refine congrArg (· ++ cd.bits.map denseBoolConstraint) ?_
  refine List.ext_getElem? (fun j => ?_)
  rw [Array.getElem?_toList, List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < st.cs.size
  · have hcget : st.cs[j]? = some st.cs[j] := Array.getElem?_eq_getElem hj
    rw [hcget, Option.map_some]
    by_cases hedit : j ∈ es.map DenseRncCsEdit.pos
    · obtain ⟨e, hemem, hepos⟩ := List.mem_map.1 hedit
      obtain ⟨c0, hc0, hcontent⟩ := csBody_content ctx st xs cd hcvs hzero _ e
        (by rwa [hes, csEdits_eq_foldr] at hemem)
      have hc0' : c0 = st.cs[j] := by rw [hepos] at hc0; rw [hcget] at hc0; exact (Option.some.inj hc0).symm
      subst hc0'
      have := denseArrFold_hit (es.map (fun e => (e.pos, e.content ctx))) st.cs e.pos
        (e.content ctx)
        (by simpa [List.map_map, Function.comp_def] using denseRncCsEdits_nodup ctx st xs cd)
        (List.mem_map.2 ⟨e, hemem, rfl⟩) (by rw [hepos]; exact hj)
      rw [hepos] at this
      rw [this, hcontent]
    · have hstable := denseArrFold_stable (es.map (fun e => (e.pos, e.content ctx))) st.cs j
        (by simpa [List.map_map, Function.comp_def] using hedit)
      rw [hstable, hcget]
      have hnf : ¬ (denseCoveredBy xs st.cs[j] = true ∨ st.cs[j].sharesVarIn xs = true ∨
          st.cs[j].hasConstFoldableNode = true) := fun hfires =>
        hedit (denseRncCsEdits_complete hcvs huse hm hs j st.cs[j] hcget hfires)
      rw [not_or, not_or] at hnf
      obtain ⟨h1, h2, h3⟩ := hnf
      simp only [denseTombify, Bool.not_eq_true] at *
      rw [if_neg (by simpa using h1),
        denseGroupRewrite_eq_self (by simpa using h2) (by simpa using h3)]
  · have hnone : st.cs[j]? = none := Array.getElem?_eq_none (by omega)
    rw [hnone, Option.map_none, Array.getElem?_eq_none (by omega)]

/-- The interaction array after the write: the positionwise gated rewrite. -/
theorem denseRncWrite_bis_toList {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hbus : DenseRncBusOk st) (hm : st.useBis = some m) (hs : st.foldBis = some sf) :
    (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1).bis.toList
      = st.bis.toList.map
          (denseBIRewriteGate xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get) := by
  set es := (denseRncBiEdits ctx st xs cd).1 with hes
  have hbis : (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1 es).bis
      = es.foldl denseArrSet st.bis := by
    show (cd.bits.foldl (fun st b => st.pushBool b)
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        ((denseRncCsEdits ctx st xs cd).1.foldl (denseRncCsStep ctx) st))).bis = _
    rw [denseRncBoolFold_bis, denseRncBiFold_bis, denseRncCsFold_bis]
  rw [hbis]
  refine List.ext_getElem? (fun j => ?_)
  rw [Array.getElem?_toList, List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < st.bis.size
  · have hbget : st.bis[j]? = some st.bis[j] := Array.getElem?_eq_getElem hj
    rw [hbget, Option.map_some]
    by_cases hedit : j ∈ es.map Prod.fst
    · obtain ⟨q, hqmem, hqpos⟩ := List.mem_map.1 hedit
      obtain ⟨bi0, hb0, hcontent⟩ := biBody_content ctx st xs cd _ q
        (by rwa [hes, biEdits_eq_foldr] at hqmem)
      have hb0' : bi0 = st.bis[j] := by
        rw [hqpos] at hb0; rw [hbget] at hb0; exact (Option.some.inj hb0).symm
      subst hb0'
      have := denseArrFold_hit es st.bis q.1 q.2 (denseRncBiEdits_nodup ctx st xs cd)
        (by simpa using hqmem) (by rw [hqpos]; exact hj)
      rw [hqpos] at this
      rw [this, hcontent]
    · rw [denseArrFold_stable es st.bis j (by simpa using hedit), hbget]
      have hnf : denseBiGateFires xs st.bis[j] = false := by
        cases hf : denseBiGateFires xs st.bis[j] with
        | false => rfl
        | true => exact absurd (denseRncBiEdits_complete hbus hm hs j st.bis[j] hbget hf) hedit
      unfold denseBIRewriteGate
      rw [if_neg (by simpa [denseBiGateFires] using hnf)]
  · have hsz : (es.foldl denseArrSet st.bis).size = st.bis.size := denseArrFold_size _ _
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega), Option.map_none]

/-- The written state's view is the re-encoded system with trivially-true constraints dropped —
    the array engine's counterpart of `denseWorkOut_view`. -/
theorem denseRncWrite_view {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m mB : Array (Array Nat)} {sf sfB : Std.HashSet Nat}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (hpatts : cd.patts.get = denseAssignments (denseBitBox cd.bits))
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st) (hbus : DenseRncBusOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf)
    (hmB : st.useBis = some mB) (hsB : st.foldBis = some sfB) :
    denseRncView (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1)
      = (denseReencodeOut (denseRncView st) xs cd.bits cd.hm.get).filterConstraints
          (fun c => !denseIsZero c) := by
  have hcsL := denseRncWrite_cs_toList (xs := xs) (cd := cd) hzero hcvs huse hm hs
  have hbisL := denseRncWrite_bis_toList (ctx := ctx) (xs := xs) (cd := cd) hbus hmB hsB
  rw [hpatts] at hcsL hbisL
  unfold denseRncView DenseConstraintSystem.filterConstraints denseReencodeOut
  dsimp only
  refine congrArg₂ DenseConstraintSystem.mk ?_ ?_
  · rw [Array.toList_filter, hcsL, List.filter_append, denseBoolConstraints_not_zero,
      List.filter_append, denseBoolConstraints_not_zero, Array.toList_filter, denseTombify_filter]
  · rw [hbisL, denseBIRewriteGate_eq]

/-! ### The indexes survive the write

Every setter writes one position of one array and only ever *adds* index entries, so each invariant
is preserved pointwise. The bundled `DenseRncOk` is what the loop threads. -/

structure DenseRncOk (st : DenseRncState p) : Prop where
  sizes : st.cvs.size = st.cs.size
  cvs : DenseRncCvsOk st
  anchor : DenseRncAnchorOk st
  use : DenseRncUseOk st
  bus : DenseRncBusOk st

theorem denseRncCapVars_const_zero : denseRncCapVars (DenseExpr.const 0 : DenseExpr p) = #[] := rfl

theorem denseRncCapVars_bool (b : VarId) :
    denseRncCapVars (denseBoolConstraint b : DenseExpr p) = #[b] := by
  simp [denseRncCapVars, denseRncCapGo, denseBoolConstraint]

theorem denseRncAnchorVars_const_zero :
    denseRncAnchorVars (DenseExpr.const 0 : DenseExpr p) = [] := rfl

/-- Growing an array does not change any existing entry. -/
theorem denseArrEnsure_getD {α : Type} (a : Array α) (i j : Nat) (d : α) :
    (denseArrEnsure a i d).getD j d = a.getD j d := by
  unfold denseArrEnsure
  split
  · rfl
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    by_cases hj : j < a.size
    · rw [Array.getElem?_append_left hj]
    · have hR : a[j]? = none := Array.getElem?_eq_none (by omega)
      have hL : ((a ++ Array.replicate (max (i + 1) (2 * a.size) - a.size) d)[j]?).getD d = d := by
        rw [Array.getElem?_append_right (by omega), Array.getElem?_replicate]
        split <;> rfl
      rw [hL, hR]
      rfl

theorem denseArrEnsure_size {α : Type} (a : Array α) (i : Nat) (d : α) :
    i < (denseArrEnsure a i d).size := by
  unfold denseArrEnsure
  split
  · omega
  · rw [Array.size_append, Array.size_replicate]
    omega

theorem denseRncBAdd_mono (m : Array (Array Nat)) (w : VarId) (i j : Nat) (v : VarId)
    (h : j ∈ denseRncBGet m v) : j ∈ denseRncBGet (denseRncBAdd m w i) v := by
  have hkeep : (denseArrEnsure m w.index #[]).getD v.index #[] = m.getD v.index #[] :=
    denseArrEnsure_getD m w.index v.index #[]
  unfold denseRncBGet denseRncBAdd at *
  rw [← hkeep] at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  rw [Array.getD_eq_getD_getElem?] at h
  by_cases hw : w.index = v.index
  · rw [if_pos hw]
    cases hget : (denseArrEnsure m w.index #[])[v.index]? with
    | none => rw [hget] at h; simp at h
    | some a =>
        rw [hget] at h
        simp only [Option.map_some, Option.getD_some] at h ⊢
        exact Array.mem_push.2 (Or.inl h)
  · rw [if_neg hw]
    exact h

theorem denseRncBAdd_self (m : Array (Array Nat)) (w : VarId) (i : Nat) :
    i ∈ denseRncBGet (denseRncBAdd m w i) w := by
  unfold denseRncBGet denseRncBAdd
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, if_pos rfl,
    Array.getElem?_eq_getElem (denseArrEnsure_size m w.index #[])]
  simp

theorem denseRncAnchorAdd_mono (idx : DenseCovIndex) (ks : List VarId) (i j : Nat) (v : VarId)
    (h : j ∈ idx.buckets.getD v []) : j ∈ (denseRncAnchorAdd idx ks i).buckets.getD v [] := by
  unfold denseRncAnchorAdd
  cases ks with
  | nil => exact h
  | cons w rest =>
      by_cases hw : v = w
      · subst hw
        show j ∈ (idx.buckets.insert v (i :: idx.buckets.getD v [])).getD v []
        rw [Std.HashMap.getD_insert_self]
        exact List.mem_cons_of_mem i h
      · show j ∈ (idx.buckets.insert w (i :: idx.buckets.getD w [])).getD v []
        rw [Std.HashMap.getD_insert, if_neg (by simpa using fun hh => hw hh.symm)]
        exact h

theorem denseRncAnchorAdd_self (idx : DenseCovIndex) (v : VarId) (rest : List VarId) (i : Nat) :
    i ∈ (denseRncAnchorAdd idx (v :: rest) i).buckets.getD v [] := by
  show i ∈ (idx.buckets.insert v (i :: idx.buckets.getD v [])).getD v []
  rw [Std.HashMap.getD_insert_self]
  exact List.mem_cons_self

theorem denseRncBFoldL_mono (i : Nat) :
    ∀ (vs : List VarId) (m : Array (Array Nat)) (v : VarId) (j : Nat), j ∈ denseRncBGet m v →
      j ∈ denseRncBGet (vs.foldl (fun m w => denseRncBAdd m w i) m) v := by
  intro vs
  induction vs with
  | nil => intro m v j h; exact h
  | cons w rest ih => intro m v j h; exact ih _ v j (denseRncBAdd_mono m w i j v h)

theorem denseRncBFoldL_self (i : Nat) :
    ∀ (vs : List VarId) (m : Array (Array Nat)) (v : VarId), v ∈ vs →
      i ∈ denseRncBGet (vs.foldl (fun m w => denseRncBAdd m w i) m) v := by
  intro vs
  induction vs with
  | nil => intro m v hv; simp at hv
  | cons w rest ih =>
      intro m v hv
      rcases List.mem_cons.1 hv with rfl | hv'
      · exact denseRncBFoldL_mono i rest _ v i (denseRncBAdd_self m v i)
      · exact ih _ v hv'

theorem denseRncFullVars_mem {c : DenseExpr p} {v : VarId} (h : v ∈ c.vars) :
    v ∈ denseRncFullVars c (denseRncCapVars c) := by
  unfold denseRncFullVars
  split
  · next hle => exact (denseRncCapVars_mem_iff hle v).2 h
  · rw [HashedDedup.hashedDedup_eq]
    simpa using List.mem_dedup.2 h

theorem denseRncSet_getElem?_ne {α : Type} (a : Array α) (i j : Nat) (x : α) (h : i ≠ j) :
    (a.setIfInBounds i x)[j]? = a[j]? := Array.getElem?_setIfInBounds_ne h

theorem denseRncSet_getElem?_self {α : Type} (a : Array α) (i : Nat) (x y : α)
    (h : (a.setIfInBounds i x)[i]? = some y) : i < a.size ∧ y = x := by
  by_cases hlt : i < a.size
  · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at h
    exact ⟨hlt, (Option.some.inj h).symm⟩
  · rw [Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)] at h
    exact absurd h (by simp)

/-- The constraint write preserves every index invariant: it only ever adds bucket entries, and it
    keeps `cvs`, the anchor and the use index in step with the new content. -/
theorem denseRncOk_rewriteAt {st : DenseRncState p} {i : Nat} {c' : DenseExpr p}
    {cv' full : Array VarId} (h : DenseRncOk st) (hcv : cv' = denseRncCapVars c')
    (hfull : ∀ v ∈ c'.vars, v ∈ full) : DenseRncOk (st.rewriteAt i c' cv' full) := by
  have hcs : (st.rewriteAt i c' cv' full).cs = st.cs.setIfInBounds i c' := rfl
  have hcvs : (st.rewriteAt i c' cv' full).cvs = st.cvs.setIfInBounds i cv' := rfl
  have hanch : (st.rewriteAt i c' cv' full).anchor
      = denseRncAnchorAdd st.anchor (denseRncAnchorVars c') i := rfl
  have huse : (st.rewriteAt i c' cv' full).useCs
      = st.useCs.map (fun m => full.foldl (fun m v => denseRncBAdd m v i) m) := rfl
  have hfold : (st.rewriteAt i c' cv' full).foldCs
      = st.foldCs.map (fun s => if denseRncHasFold c' then s.insert i else s.erase i) := rfl
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hcs, hcvs, Array.size_setIfInBounds, Array.size_setIfInBounds]; exact h.sizes
  · intro j c hj
    rw [hcs] at hj
    rw [hcvs]
    by_cases hij : i = j
    · subst hij
      obtain ⟨hlt, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [h.sizes]; exact hlt), hcv]
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      rw [denseRncSet_getElem?_ne _ _ _ _ hij]
      exact h.cvs j c hj
  · intro j c hj v hv
    rw [hcs] at hj
    rw [hanch]
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      cases hav : denseRncAnchorVars c with
      | nil => rw [hav] at hv; simp at hv
      | cons w rest =>
          have hvw : v = w := by
            rw [hav] at hv
            rcases List.mem_cons.1 hv with h1 | h1
            · exact h1
            · exact absurd h1 (by
                unfold denseRncAnchorVars at hav
                split at hav <;> simp_all)
          subst hvw
          exact denseRncAnchorAdd_self st.anchor v rest i
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncAnchorAdd_mono _ _ i j v (h.anchor j c hj v hv)
  · intro m hm j c hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hcs] at hj
    have hfl : full.foldl (fun m v => denseRncBAdd m v i) m0
        = full.toList.foldl (fun m v => denseRncBAdd m v i) m0 := by
      conv_lhs => rw [← Array.toArray_toList (xs := full)]
      rw [List.foldl_toArray]
    rw [hfl]
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      exact denseRncBFoldL_self i full.toList m0 v (by simpa using hfull v hv)
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncBFoldL_mono i full.toList m0 v j (h.use.1 m0 hm0 j c hj v hv)
  · intro sf hsf j c hj hfd
    rw [hfold] at hsf
    obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.1 hsf
    rw [hcs] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      rw [if_pos hfd]
      simp
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      have hmem := h.use.2 s0 hs0 j c hj hfd
      split
      · rw [Std.HashSet.contains_insert]; simp [hmem]
      · rw [Std.HashSet.contains_erase]; simp [hmem, hij]
  · exact h.bus

theorem denseRncHasFold_bool (b : VarId) :
    denseRncHasFold (denseBoolConstraint b : DenseExpr p) = false := rfl

theorem denseBoolConstraint_vars (b : VarId) :
    ∀ v ∈ (denseBoolConstraint b : DenseExpr p).vars, v = b := by
  intro v hv
  simpa [denseBoolConstraint, DenseExpr.vars] using hv

theorem denseRncAnchorVars_bool (b : VarId) :
    denseRncAnchorVars (denseBoolConstraint b : DenseExpr p) = [b] := by
  unfold denseRncAnchorVars
  rw [denseRncCapVars_bool]
  rfl

/-- Appending a booleanity constraint preserves every index invariant. -/
theorem denseRncOk_pushBool {st : DenseRncState p} (h : DenseRncOk st) (b : VarId) :
    DenseRncOk (st.pushBool b) := by
  have hcs : (st.pushBool b).cs = st.cs.push (denseBoolConstraint b) := rfl
  have hcvs : (st.pushBool b).cvs = st.cvs.push #[b] := rfl
  have hanch : (st.pushBool b).anchor = denseRncAnchorAdd st.anchor [b] st.cs.size := rfl
  have huse : (st.pushBool b).useCs = st.useCs.map (fun m => denseRncBAdd m b st.cs.size) := rfl
  have hfold : (st.pushBool b).foldCs = st.foldCs := rfl
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hcs, hcvs, Array.size_push, Array.size_push, h.sizes]
  · intro j c hj
    rw [hcs, Array.getElem?_push] at hj
    rw [hcvs, Array.getElem?_push, h.sizes]
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj ⊢
      rw [← Option.some.inj hj, denseRncCapVars_bool]
    · rw [if_neg heq] at hj ⊢
      exact h.cvs j c hj
  · intro j c hj v hv
    rw [hcs, Array.getElem?_push] at hj
    rw [hanch]
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      rw [denseRncAnchorVars_bool] at hv
      have hvb : v = b := by simpa using hv
      subst hvb
      subst heq
      exact denseRncAnchorAdd_self st.anchor v [] st.cs.size
    · rw [if_neg heq] at hj
      exact denseRncAnchorAdd_mono _ _ _ j v (h.anchor j c hj v hv)
  · intro m hm j c hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hcs, Array.getElem?_push] at hj
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      have hvb : v = b := denseBoolConstraint_vars b v hv
      subst hvb
      subst heq
      exact denseRncBAdd_self m0 v st.cs.size
    · rw [if_neg heq] at hj
      exact denseRncBAdd_mono m0 b st.cs.size j v (h.use.1 m0 hm0 j c hj v hv)
  · intro sf hsf j c hj hfd
    rw [hfold] at hsf
    rw [hcs, Array.getElem?_push] at hj
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      rw [denseRncHasFold_bool] at hfd
      exact absurd hfd (by simp)
    · rw [if_neg heq] at hj
      exact h.use.2 sf hsf j c hj hfd
  · exact h.bus

/-- The bus write preserves the invariants: the constraint side is untouched and the bus index only
    grows. -/
theorem denseRncOk_rewriteBiAt {st : DenseRncState p} (h : DenseRncOk st) (i : Nat)
    (bi' : BusInteraction (DenseExpr p)) : DenseRncOk (st.rewriteBiAt i bi') := by
  have hbis : (st.rewriteBiAt i bi').bis = st.bis.setIfInBounds i bi' := rfl
  have huse : (st.rewriteBiAt i bi').useBis
      = st.useBis.map (fun m => (denseBIVars bi').foldl (fun m v => denseRncBAdd m v i) m) := rfl
  have hfold : (st.rewriteBiAt i bi').foldBis
      = st.foldBis.map (fun s => if denseRncBiHasFold bi' then s.insert i else s.erase i) := rfl
  refine ⟨h.sizes, h.cvs, h.anchor, h.use, ⟨?_, ?_⟩⟩
  · intro m hm j bi hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hbis] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hbb⟩ := denseRncSet_getElem?_self st.bis i bi' bi hj
      subst hbb
      exact denseRncBFoldL_self i (denseBIVars bi) m0 v hv
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncBFoldL_mono i (denseBIVars bi') m0 v j (h.bus.1 m0 hm0 j bi hj v hv)
  · intro sf hsf j bi hj hfd
    rw [hfold] at hsf
    obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.1 hsf
    rw [hbis] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hbb⟩ := denseRncSet_getElem?_self st.bis i bi' bi hj
      subst hbb
      rw [if_pos hfd]
      simp
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      have hmem := h.bus.2 s0 hs0 j bi hj hfd
      split
      · rw [Std.HashSet.contains_insert]; simp [hmem]
      · rw [Std.HashSet.contains_erase]; simp [hmem, hij]

theorem denseRncOk_domReset {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk st.domReset := ⟨h.sizes, h.cvs, h.anchor, h.use, h.bus⟩

/-- What the constraint-edit builder guarantees about each edit's payload. -/
def DenseRncEditOk : DenseRncCsEdit p → Prop
  | .tomb _ => True
  | .cst _ c' cv' full => cv' = denseRncCapVars c' ∧ ∀ v ∈ c'.vars, v ∈ full

theorem denseRncOk_csStep {ctx : DenseRncCtx p} {st : DenseRncState p} {e : DenseRncCsEdit p}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (h : DenseRncOk st) (he : DenseRncEditOk e) : DenseRncOk (denseRncCsStep ctx st e) := by
  cases e with
  | tomb i =>
      refine denseRncOk_rewriteAt h ?_ ?_
      · rw [hzero, denseRncCapVars_const_zero]
      · intro v hv; rw [hzero] at hv; simp [DenseExpr.vars] at hv
  | cst i c' cv' full => exact denseRncOk_rewriteAt h he.1 he.2

theorem denseRncOk_csFold {ctx : DenseRncCtx p}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p), DenseRncOk st →
      (∀ e ∈ es, DenseRncEditOk e) → DenseRncOk (es.foldl (denseRncCsStep ctx) st) := by
  intro es
  induction es with
  | nil => intro st h _; exact h
  | cons e rest ih =>
      intro st h he
      exact ih _ (denseRncOk_csStep hzero h (he e List.mem_cons_self))
        (fun e' he' => he e' (List.mem_cons_of_mem e he'))

theorem denseRncOk_biFold :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p), DenseRncOk st →
      DenseRncOk (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st) := by
  intro es
  induction es with
  | nil => intro st h; exact h
  | cons e rest ih => intro st h; exact ih _ (denseRncOk_rewriteBiAt h e.1 e.2)

theorem denseRncOk_boolFold :
    ∀ (bits : List VarId) (st : DenseRncState p), DenseRncOk st →
      DenseRncOk (bits.foldl (fun st b => st.pushBool b) st) := by
  intro bits
  induction bits with
  | nil => intro st h; exact h
  | cons b rest ih => intro st h; exact ih _ (denseRncOk_pushBool h b)

/-- The whole write preserves the index invariants. -/
theorem denseRncOk_write {ctx : DenseRncCtx p} {st : DenseRncState p} {bits : List VarId}
    {csEdits : List (DenseRncCsEdit p)} {biEdits : List (Nat × BusInteraction (DenseExpr p))}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (h : DenseRncOk st)
    (he : ∀ e ∈ csEdits, DenseRncEditOk e) :
    DenseRncOk (denseRncWrite ctx st bits csEdits biEdits) :=
  denseRncOk_domReset (denseRncOk_boolFold bits _
    (denseRncOk_biFold biEdits _ (denseRncOk_csFold hzero csEdits st h he)))

/-- The builder's edits carry the payload the invariants need. -/
theorem denseRncCsEdits_editOk (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ∀ e ∈ (denseRncCsEdits ctx st xs cd).1, DenseRncEditOk e := by
  rw [csEdits_eq_foldr]
  generalize (denseRncPosList (match st.useCs with | some m => m | none => #[]) xs
    (match st.foldCs with | some s => s | none => ∅).toList) = l
  induction l with
  | nil => intro e he; simp at he
  | cons i rest ih =>
      intro e he
      rw [List.foldr_cons] at he
      cases hc : st.cs[i]? with
      | none => exact ih e (by simpa only [csBody, hc] using he)
      | some c =>
        cases hvs : st.cvs[i]? with
        | none => exact ih e (by simpa only [csBody, hc, hvs] using he)
        | some vs =>
          simp only [csBody, hc, hvs] at he
          split at he
          · rcases List.mem_cons.1 he with rfl | he'
            · trivial
            · exact ih e he'
          · split at he
            · rcases List.mem_cons.1 he with rfl | he'
              · exact ⟨rfl, fun v hv => denseRncFullVars_mem hv⟩
              · exact ih e he'
            · exact ih e he

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
