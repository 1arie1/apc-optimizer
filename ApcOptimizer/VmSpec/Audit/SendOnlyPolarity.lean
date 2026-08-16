import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! **A decidable, syntactic check for `Circuit.statelessSendOnly`/`Circuit.statefulPolarity`.**

    This is neither spec (it proves a theorem about the two *existing* legality clauses, adding no
    new claim) nor `Implementation/` (nothing in the VM-level soundness argument calls it — it is a
    tool an optimizer, or a human, runs *on a candidate circuit* to check those two clauses hold,
    the translation-validation way: run the checker, get a `Bool`, and `checkMultiplicities_sound`
    turns a `true` into the actual `Prop`s `Circuit.legalGuest` needs).

    The check is a single pass over `c.busInteractions`: fold each multiplicity expression to a
    literal field constant (`Expression.foldConst`), and ask whether that constant is already in
    the legal set for its bus's statefulness — `{0, 1}` for a stateless send, `{0, 1, -1}` for a
    stateful one. It is sound but incomplete by construction: `Circuit.statelessSendOnly` quantifies
    over every algebraically-satisfying assignment, and folding a multiplicity that is a bare
    variable (e.g. a boolean flag range-checked elsewhere to `{0, 1}`) always returns `none`, so the
    checker rejects a chip that legitimately gates a lookup on such a flag. Recognizing that case —
    matching the multiplicity against a booleanity constraint elsewhere in `algebraicConstraints` —
    is a natural next tier this file does not attempt.

    The third clause of `Circuit.legalGuest`, `statefulSendsMaintain`, is not covered: it is a claim
    about payload *values* (byte discipline, timestamp ordering) that depends on how a chip computes
    what it sends, not on the multiplicity alone, and needs semantic reasoning this syntactic pass
    cannot give. -/

variable {p : ℕ}

/-- Fold an expression to a literal field constant when every leaf is a `.const` — the simplest
    sufficient witness that its value is fixed independent of the assignment. `none` on any `.var`,
    since no such witness exists for a value that can vary. -/
def Expression.foldConst : Expression p → Option (ZMod p)
  | .const n => some n
  | .var _ => none
  | .add e1 e2 => match e1.foldConst, e2.foldConst with
    | some v1, some v2 => some (v1 + v2)
    | _, _ => none
  | .mul e1 e2 => match e1.foldConst, e2.foldConst with
    | some v1, some v2 => some (v1 * v2)
    | _, _ => none

/-- What `Expression.foldConst` promises: the folded constant is the expression's value under
    *every* assignment. -/
theorem Expression.foldConst_eq {e : Expression p} {v : ZMod p} (h : e.foldConst = some v)
    (asg : Variable → ZMod p) : e.eval asg = v := by
  induction e generalizing v with
  | const n => cases h; rfl
  | var x => cases h
  | add e1 e2 ih1 ih2 =>
    simp only [Expression.foldConst] at h
    cases h1 : e1.foldConst with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : e2.foldConst with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        cases h
        exact congrArg₂ (· + ·) (ih1 h1) (ih2 h2)
  | mul e1 e2 ih1 ih2 =>
    simp only [Expression.foldConst] at h
    cases h1 : e1.foldConst with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : e2.foldConst with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        cases h
        exact congrArg₂ (· * ·) (ih1 h1) (ih2 h2)

/-- The multiplicities `Circuit.statelessSendOnly`/`Circuit.statefulPolarity` allow, keyed by
    whether the bus is stateful — `{0, 1, -1}` for a stateful send, `{0, 1}` for a stateless one.
    Matches the target sets those two definitions state directly. -/
def legalMultiplicity (stateful : Bool) (v : ZMod p) : Prop :=
  if stateful then v = 0 ∨ v = 1 ∨ v = -1 else v = 0 ∨ v = 1

instance {stateful : Bool} {v : ZMod p} : Decidable (legalMultiplicity stateful v) := by
  unfold legalMultiplicity; cases stateful <;> infer_instance

/-- **The static check.** For every bus interaction, its multiplicity folds to a literal constant
    already legal for its bus's statefulness (per `isStateful`, meant to be a
    `GuestBusRules.isStateful`). Decidable, and syntactic only — it never inspects
    `algebraicConstraints`. -/
def checkMultiplicities (isStateful : Nat → Bool) (c : Circuit p) : Bool :=
  c.busInteractions.all fun bi =>
    match bi.multiplicity.foldConst with
    | some v => decide (legalMultiplicity (isStateful bi.busId) v)
    | none => false

/-- **Soundness of the static check.** A `true` result gives both `Circuit.statelessSendOnly` and
    `Circuit.statefulPolarity`, for any `r` whose `isStateful` is the one the check ran against —
    the check needs nothing else about `r` (not `accepts`, not `payloadOk`), so it applies uniformly
    across every VM's `GuestBusRules`. -/
theorem checkMultiplicities_sound {isStateful : Nat → Bool} {c : Circuit p}
    (h : checkMultiplicities isStateful c = true) {r : GuestBusRules p}
    (hr : r.isStateful = isStateful) :
    c.statelessSendOnly r ∧ c.statefulPolarity r := by
  have hall : ∀ bi ∈ c.busInteractions, ∃ v : ZMod p, bi.multiplicity.foldConst = some v ∧
      legalMultiplicity (isStateful bi.busId) v := by
    intro bi hbi
    have hbi' := List.all_eq_true.mp h bi hbi
    cases hfold : bi.multiplicity.foldConst with
    | none => rw [hfold] at hbi'; simp at hbi'
    | some v => exact ⟨v, rfl, by rw [hfold] at hbi'; simpa using hbi'⟩
  constructor
  · intro asg _ bi hbi hst
    obtain ⟨v, hfold, hleg⟩ := hall bi hbi
    have hval : (bi.eval asg).multiplicity = v := Expression.foldConst_eq hfold asg
    rw [hr] at hst
    rw [hst] at hleg
    unfold legalMultiplicity at hleg
    simpa [hval] using hleg
  · intro asg _ bi hbi hst
    obtain ⟨v, hfold, hleg⟩ := hall bi hbi
    have hval : (bi.eval asg).multiplicity = v := Expression.foldConst_eq hfold asg
    rw [hr] at hst
    rw [hst] at hleg
    unfold legalMultiplicity at hleg
    simpa [hval] using hleg
