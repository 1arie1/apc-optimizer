import ApcOptimizer.Spec
import ApcOptimizer.Utils.Size

set_option autoImplicit false

/-! # Evaluation depends only on the variables read

Membership in `Circuit.vars` and the `eval_congr` family: two assignments agreeing on a
circuit's variables are interchangeable for `satisfies` / `admissible` / `sideEffects`.
Imported by the pass framework (`OptimizerPasses/Basic.lean`) and, independently, by the
interface-encoding metatheory — which is why it sits here rather than in either. -/

variable {p : ℕ}

/-! ## Membership in `Circuit.vars` -/

theorem Circuit.mem_vars {cs : Circuit p} {x : Variable} :
    x ∈ cs.vars ↔
      (∃ c ∈ cs.algebraicConstraints, x ∈ c.vars) ∨
      (∃ bi ∈ cs.busInteractions, x ∈ bi.multiplicity.vars ∨ ∃ e ∈ bi.payload, x ∈ e.vars) := by
  simp only [Circuit.vars, List.mem_append, List.mem_flatMap]

theorem Circuit.mem_vars_of_constraint {cs : Circuit p} {c : Expression p}
    {x : Variable} (hc : c ∈ cs.algebraicConstraints) (hx : x ∈ c.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inl ⟨c, hc, hx⟩)

theorem Circuit.mem_vars_of_mult {cs : Circuit p}
    {bi : BusInteraction (Expression p)} {x : Variable} (hbi : bi ∈ cs.busInteractions)
    (hx : x ∈ bi.multiplicity.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inl hx⟩)

theorem Circuit.mem_vars_of_payload {cs : Circuit p}
    {bi : BusInteraction (Expression p)} {e : Expression p} {x : Variable}
    (hbi : bi ∈ cs.busInteractions) (he : e ∈ bi.payload) (hx : x ∈ e.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inr ⟨e, he, hx⟩⟩)

/-! ## Evaluation depends only on an expression's variables -/

theorem Expression.eval_congr (e : Expression p) (env1 env2 : Variable → ZMod p)
    (h : ∀ x ∈ e.vars, env1 x = env2 x) : e.eval env1 = e.eval env2 := by
  induction e with
  | const n => rfl
  | var x => exact h x (by simp [Expression.vars])
  | add a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]
  | mul a b iha ihb =>
      simp only [Expression.eval]
      rw [iha (fun x hx => h x (by simp [Expression.vars, hx])),
          ihb (fun x hx => h x (by simp [Expression.vars, hx]))]

theorem BusInteraction.eval_congr (bi : BusInteraction (Expression p))
    (env1 env2 : Variable → ZMod p) (h : ∀ x ∈ bi.vars, env1 x = env2 x) :
    bi.eval env1 = bi.eval env2 := by
  have hmult : bi.multiplicity.eval env1 = bi.multiplicity.eval env2 :=
    bi.multiplicity.eval_congr env1 env2
      (fun x hx => h x (by simp [BusInteraction.vars, hx]))
  have hpay : bi.payload.map (fun e => e.eval env1) = bi.payload.map (fun e => e.eval env2) := by
    apply List.map_congr_left
    intro e he
    exact e.eval_congr env1 env2
      (fun x hx => h x (by
        simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨e, he, hx⟩))
  simp only [BusInteraction.eval, hmult, hpay]

/-! ## Evaluation depends only on a circuit's variables

Two assignments agreeing on `cs.vars` are interchangeable for `satisfies`/`admissible`/
`sideEffects`. The master-theorem completeness proof uses these to swap the abstract
per-pass witness for `witgen`'s output; the metatheory uses them to swap a witness for any
assignment agreeing with it on the circuit's variables. -/

theorem Circuit.busEval_congr {cs : Circuit p} {f g : Variable → ZMod p}
    (h : ∀ x ∈ cs.vars, f x = g x) {bi : BusInteraction (Expression p)}
    (hbi : bi ∈ cs.busInteractions) : bi.eval f = bi.eval g :=
  BusInteraction.eval_congr bi f g (fun x hx => by
    simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨e, he, hx⟩
    · exact h x (Circuit.mem_vars_of_mult hbi hx)
    · exact h x (Circuit.mem_vars_of_payload hbi he hx))

theorem Circuit.satisfies_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.satisfies bs f ↔ cs.satisfies bs g := by
  have imp : ∀ e1 e2 : Variable → ZMod p, (∀ x ∈ cs.vars, e1 x = e2 x) →
      cs.satisfies bs e1 → cs.satisfies bs e2 := by
    intro e1 e2 hh hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · rw [← Expression.eval_congr c e1 e2
        (fun x hx => hh x (Circuit.mem_vars_of_constraint hc hx))]
      exact hsat.1 c hc
    · have hbe : bi.eval e1 = bi.eval e2 := Circuit.busEval_congr hh hbi
      show (bi.eval e2).multiplicity ≠ 0 → bs.accepts (bi.eval e2)
      rw [← hbe]
      exact hsat.2 bi hbi
  exact ⟨imp f g h, imp g f (fun x hx => (h x hx).symm)⟩

theorem Circuit.admissible_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.admissible bs f ↔ cs.admissible bs g := by
  have hmap : (cs.busInteractions.map (fun bi => bi.eval f))
      = (cs.busInteractions.map (fun bi => bi.eval g)) :=
    List.map_congr_left (fun bi hbi => Circuit.busEval_congr h hbi)
  unfold Circuit.admissible
  rw [hmap]

theorem Circuit.sideEffects_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.sideEffects bs f = cs.sideEffects bs g := by
  have hmap : cs.busInteractions.map (fun bi => bi.eval f)
      = cs.busInteractions.map (fun bi => bi.eval g) :=
    List.map_congr_left (fun bi hbi => Circuit.busEval_congr h hbi)
  unfold Circuit.sideEffects
  rw [hmap]
