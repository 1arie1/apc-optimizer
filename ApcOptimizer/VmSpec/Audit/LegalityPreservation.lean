import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! **Soundness does not imply legality preservation — a formal witness.**

    `openVm_vmSoundReplacement` requires the optimizer's *output* to be legal, as a hypothesis
    rather than a consequence, and this file is why it cannot be a consequence: a per-chip
    `Circuit.isSoundReplacementOf` puts no constraint at all on a bus interaction's *multiplicity
    shape*, so a chip can be a perfectly sound replacement while violating
    `Circuit.statelessSendOnly` outright.

    The mechanism is simple, and it is not a proof-engineering accident — it falls straight out of
    what the two definitions quantify over:

    * `Circuit.isSoundReplacementOf` only has to reproduce a stateful bus's *net* multiplicity
      (`Circuit.sideEffects`), and only on assignments that are `Circuit.satisfies`-good — algebraic
      constraints *and* bus acceptance. A stateless bus does not even appear in `sideEffects`.
    * `Circuit.statelessSendOnly` (and `statefulPolarity`, `StepLayout.sendsOk` with it) is a
      claim about *every* algebraically-satisfying assignment, dropping the acceptance requirement
      entirely — because that is what a real AIR needs: no constraint system evaluates
      `legalGuest`, so a chip has to be built so the property holds identically, not merely on the
      runs that happen to occur.

    A chip that sends an *unconstrained* multiplicity to a stateless bus whose semantics accepts
    any magnitude, and asks nothing further of it, is illegal and yet a perfectly sound replacement
    of a chip that sends the same message with a legal, constant multiplicity —
    `illegalCircuit_isSoundReplacementOf` and `illegalCircuit_not_statelessSendOnly` make this
    precise. This is not a corner case specific to `statelessSendOnly`: the
    analogous move — splitting one stateful send into two interactions whose multiplicities cancel
    to the same net — breaks `statefulPolarity` exactly as directly, for the same reason.

    Both halves of `toyBusSemantics` are load-bearing, and the second is one a concrete VM can take
    back. `ApcOptimizer.OpenVM.accepts` does indeed never read a lookup's multiplicity — but
    `ApcOptimizer.OpenVM.maintainsInvariants` pins it to `1`, and `Circuit.isSoundReplacementOf`'s
    second conjunct transports that from the original chip, so this witness does *not* lift to
    OpenVM as it stands (`ApcOptimizer.OpenVM.looseTabled_not_isSoundReplacementOf`). The gap is
    real for OpenVM too, by the other route — an assignment the semantics does not accept, where
    the transported invariants say nothing:
    `ApcOptimizer.OpenVM.openVm_sound_but_illegal` in `Audit/SoundnessGivesLegality.lean`.

    What this means for discharging that hypothesis: it cannot come from an optimizer pass's
    soundness proof, however that proof is phrased. Each pass would need its own, separate
    legality-preservation argument — parallel to, not derived from, its existing
    `isSoundReplacementOf`/`isCompleteReplacementOf` proof. No pass in
    `ApcOptimizer/Implementation/OptimizerPasses/` carries one today; `legalGuest` and
    `StepLayout` postdate all of them. See `agent-docs/legality-preservation.md` for the fuller
    discussion. -/

variable {p : ℕ}

/-- A toy bus semantics with a single stateless bus (`0`) that accepts every message regardless of
    multiplicity — as every OpenVM lookup table does, `ApcOptimizer.OpenVM.accepts` never reading
    `BusInteraction.multiplicity` — and asks nothing of it afterwards, which OpenVM does *not* do
    (`ApcOptimizer.OpenVM.maintainsInvariants` pins a lookup to `1`). Chosen to isolate the
    mechanism at the level of `Spec.lean`'s interface; see the module docstring for what changes
    once a VM constrains multiplicities of its own. -/
def toyBusSemantics (p : ℕ) : BusSemantics p where
  isStateful _ := false
  accepts _ := True
  maintainsInvariants _ := True
  admissible _ := True

/-- The rules `toyBusSemantics` induces, restated directly rather than via `toGuestRules` (see
    `Legal.lean` for why the audited surface avoids that route) — `isStateful` and `accepts` match
    by construction; `payloadOk` is never consulted below. -/
def toyGuestRules (p : ℕ) : GuestBusRules p where
  isStateful _ := false
  accepts _ := True
  payloadOk _ := True
  execBusId := 0
  memBusId := 0
  getTimestamp _ := 0
  memPayloadOnly := fun _ hst _ => absurd hst (by decide)

/-- The original chip: one interaction on the stateless bus, multiplicity fixed at the literal `1`.
    Legal by inspection — `statelessSendOnly` is forced by the constant. -/
def legalCircuit (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions := [{ busId := 0, multiplicity := .const 1, payload := [] }]

/-- The "optimized" chip: the same interaction, but with its multiplicity replaced by a fresh,
    wholly unconstrained variable. A real optimizer would never intentionally produce this, but
    nothing in `Circuit.isSoundReplacementOf` rules it out — that is the point. -/
def illegalCircuit (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions := [{ busId := 0, multiplicity := .var ⟨"y", none⟩, payload := [] }]

/-- **The counterexample.** `illegalCircuit` is a sound replacement of `legalCircuit`: both
    circuits `satisfies` unconditionally (no constraints, and `toyBusSemantics.accepts` ignores
    multiplicity), both `sideEffects` are identically zero (the only bus is stateless), and both
    trivially `guaranteesInvariants` (`maintainsInvariants` is `True` everywhere). -/
theorem illegalCircuit_isSoundReplacementOf :
    (illegalCircuit p).isSoundReplacementOf (legalCircuit p) (toyBusSemantics p) := by
  have hnoConstraints : ∀ c : Circuit p, c.algebraicConstraints = [] →
      ∀ assignment, c.satisfiesAlgebraic assignment := by
    intro c hc assignment e he
    rw [hc] at he
    simp at he
  refine ⟨fun assignment _ =>
    ⟨assignment, ⟨hnoConstraints _ rfl assignment, fun bi hbi _ => trivial⟩, rfl⟩, ?_⟩
  intro _ assignment _ bi hbi _
  exact fun _ => trivial

/-- **`illegalCircuit` violates `statelessSendOnly`.** Assigning the free multiplicity variable
    `2` satisfies the (empty) algebraic constraints, yet `2 ∉ {0, 1}`. This needs `p ≠ 2` so that
    `(2 : ZMod p)` is neither `0` nor `1` — true of every field this development targets
    (`babyBear`, `koalaBear`), whose characteristic is far larger than `2`. -/
theorem illegalCircuit_not_statelessSendOnly [Fact p.Prime] (hp : 2 < p) :
    ¬ (illegalCircuit p).statelessSendOnly (toyGuestRules p) := by
  intro hlegal
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hforced := hlegal (fun _ => ((2 : ℕ) : ZMod p))
    (by simp [Circuit.satisfiesAlgebraic, illegalCircuit])
    { busId := 0, multiplicity := .var ⟨"y", none⟩, payload := [] } (by simp [illegalCircuit]) rfl
  simp only [BusInteraction.eval, Expression.eval] at hforced
  have hv2 : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_cast_of_lt hp
  rcases hforced with h0 | h1
  · have := congrArg ZMod.val h0
    rw [hv2, ZMod.val_zero] at this
    omega
  · have := congrArg ZMod.val h1
    rw [hv2, ZMod.val_one] at this
    omega

/-- **The two put together.** A per-chip sound replacement, entirely blind to
    `Circuit.legalGuest`'s multiplicity-shape clauses. Nothing about `isSoundReplacementOf` — the
    interface `vmSoundReplacement_of_forall₂` consumes — rules this out, so legality of the output
    cannot be derived from it; it has to be assumed or separately established, as
    `openVm_vmSoundReplacement` already does. -/
theorem soundness_not_legalityPreserving [Fact p.Prime] (hp : 2 < p) :
    (illegalCircuit p).isSoundReplacementOf (legalCircuit p) (toyBusSemantics p) ∧
      ¬ ∃ maxWindow maxLookback maxInteractions,
        (illegalCircuit p).legalGuest (toyGuestRules p) maxWindow maxLookback maxInteractions :=
  ⟨illegalCircuit_isSoundReplacementOf,
    fun ⟨_, _, _, hleg⟩ => illegalCircuit_not_statelessSendOnly hp hleg.sendOnly⟩
