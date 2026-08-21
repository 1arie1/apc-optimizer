# Does soundness imply legality preservation?

**Question.** `openVm_vmSoundReplacement` (`ApcOptimizer/VmSpec/Theorems.lean`) takes
`PreservesLegality` as a hypothesis rather than deriving it from the `List.Forall₂`
`Circuit.isSoundReplacementOf` hypothesis it also takes. Could `PreservesLegality` be derived —
i.e., does a sound replacement automatically preserve `Host.legalGuest`?

**Answer: no**, and not as an artifact of how the proof is currently structured — it falls
straight out of what the two definitions quantify over. `ApcOptimizer/VmSpec/Audit/
LegalityPreservation.lean` is a compiling Lean file proving this at the level of `Spec.lean`'s
interface: a concrete pair of circuits where the replacement is a sound
`Circuit.isSoundReplacementOf` and simultaneously violates `Circuit.statelessSendOnly` outright.
It holds for OpenVM specifically too, though by a different route and against a stronger bus
semantics — `Audit/SoundnessGivesLegality.lean`, and "Is there one for OpenVM?" below.

## The mechanism

`Circuit.legalGuest` (`Legal.lean`) has three clauses, and all three share a shape:
`Circuit.algebraicallyForces r stateful P` — some property `P` must hold of *every*
algebraically-satisfying assignment, full stop. No bus-acceptance is required. That is
deliberate: a real OpenVM AIR cannot check `legalGuest` at runtime (each clause quantifies over
all assignments, which no constraint system evaluates), so a chip has to be *built* so the
property is true identically, not merely true on the runs that occur.

`Circuit.isSoundReplacementOf`, by contrast, has two conjuncts, and both are weaker in exactly
the direction that matters. The first:

1. Every assignment satisfying `Circuit.satisfies` — algebraic constraints **and** bus
   acceptance — must have a matching original-circuit assignment with the same
   `Circuit.sideEffects`.
2. `sideEffects` covers only **stateful** buses, and only their **net** multiplicity per message
   (`Circuit.allEffects` restricted and summed) — never a stateless bus, and never the shape of
   the individual interactions that produced the net.

So a bus interaction's multiplicity is invisible to that conjunct in two independent ways: on a
stateless bus, it isn't tracked by `sideEffects` at all; on any bus, only the *sum* the guest
sends is compared, not what any one interaction sends.

The second conjunct transports `Circuit.guaranteesInvariants` from the original chip to the
replacement, and this is where a concrete VM gets a say: whatever a message has to satisfy under
its `BusSemantics.maintainsInvariants`, the replacement must go on satisfying. For OpenVM that is a real
multiplicity discipline (`= 1` on every lookup bus, `= ±1` on the execution bridge and memory), so
the toy witness below does *not* lift to OpenVM verbatim. But the transport is gated on
`Circuit.satisfies` too — see "Is there one for OpenVM?".

## The witness

`ApcOptimizer/VmSpec/Audit/LegalityPreservation.lean`:

- `toyBusSemantics` — one stateless bus, accepting every message regardless of multiplicity, and
  asking nothing of it afterwards (`maintainsInvariants` is `True`). The first half is real:
  `ApcOptimizer.OpenVM.accepts` never reads `BusInteraction.multiplicity` for any of OpenVM's four
  lookup tables, only the payload. The second half is not — see below.
- `legalCircuit` — one interaction on that bus, multiplicity the literal constant `1`. Legal by
  inspection.
- `illegalCircuit` — the same interaction, multiplicity replaced by a fresh, wholly unconstrained
  variable. No real optimizer pass would deliberately produce this; the point is that nothing in
  `Circuit.isSoundReplacementOf` rules it out.
- `illegalCircuit_isSoundReplacementOf` — `illegalCircuit` is a sound replacement of
  `legalCircuit`. Both `satisfies` unconditionally (empty constraints, magnitude-blind acceptance);
  both `sideEffects` are the identically-zero function (the only bus is stateless, so neither
  circuit's stateful net ever differs — there is nothing to compare).
- `illegalCircuit_not_statelessSendOnly` — assigning the free variable `2` satisfies the (empty)
  algebraic constraints and gives a multiplicity outside `{0, 1}`, refuting
  `Circuit.statelessSendOnly` directly.
- `soundness_not_legalityPreserving` bundles the two: a sound replacement that is provably not
  `legalGuest` at any rank/bound.

## Is there one for OpenVM?

Yes — but not this one, and the difference is instructive.

Transplant the witness onto a real OpenVM lookup bus (variable range checker, payload `(0, 0)`,
multiplicity freed) and it stops being a sound replacement:
`ApcOptimizer.OpenVM.maintainsInvariants` pins a lookup's multiplicity to `1`, the original chip
guarantees it, and the second conjunct makes the replacement guarantee it too — `y := 2` satisfies
the replacement and breaks it. That is
`ApcOptimizer.OpenVM.looseTabled_not_isSoundReplacementOf` in
`ApcOptimizer/VmSpec/Audit/SoundnessGivesLegality.lean`, which also measures how much of
`Circuit.legalGuest` the transport *does* give: all three bus-shape clauses, on the assignments the
semantics accepts (`Circuit.legalOnAccepted`).

The residue is the quantifier, and it is enough.
`ApcOptimizer.OpenVM.openVm_sound_but_illegal` (same file) is the OpenVM counterexample:

- `checkedStepChip` — one execution-bridge step plus an in-table range check at the literal
  multiplicity `1`. Proved a `Circuit.legalGuest` in full, `Circuit.advancesClock` included: a chip
  `openVmHost` will actually run.
- `poisonedStepChip` — the same step, and two range checks at one free multiplicity `y`: one of
  free width `b`, one at the in-table payload `(0, 0)`. Single constraint `(y - 1) (b - 18) = 0`.
- On `b = 18` the first check is in no table (the variable range checker caps at 17 bits), so the
  assignment is not `Circuit.satisfies` — and everything the transport gives is gated on
  `Circuit.satisfies`, a property of the **whole chip**. One unacceptable interaction anywhere in
  it voids the gate for every other interaction on that assignment, leaving `y = 2`.
- The theorem bundles: the original is legal, the replacement is sound, the replacement is
  *satisfiable* (`y = 1, b = 0` is an honest run, so none of this is vacuity), it is not
  `Circuit.statelessSendOnly`, and the message that breaks it — an in-table range check counted
  twice — is one the checker **accepts**. The multiplicity discipline exists to stop a lookup
  being counted a number of times that wraps the characteristic (whitepaper §2.2.4); this is a
  legitimate message counted twice, not a message no table would answer.

`ApcOptimizer.OpenVM.zeroMultiplicity_replaceable_by_receive` (same file) sharpens the vacuity
route separately: a message in no table has no satisfying assignment to constrain, so *both*
conjuncts hold for want of a witness and an interaction at multiplicity `0` may be replaced by one
at `-1`, literals throughout. Two chips holding `+1` and `-1` of the same unacceptable message
cancel, so global bus balance never sees them.

## Does the same trick break the stateful clauses too?

Yes, under `toyBusSemantics`, by an analogous move, though the file only formalizes the stateless
case (the mechanism is identical and a second Lean witness would not add anything). Under OpenVM
it needs the same detour as above — `maintainsInvariants` pins bridge and memory multiplicities to
`±1` and the second conjunct transports that, so the split has to hide behind an assignment the
semantics rejects. `Circuit.sideEffects` sums
*all* of a chip's interactions touching a given stateful message into one net value. So replace
one interaction sending the literal constant `1` with two interactions sending literal constants
`3` and `-2` to the same message: the net is still `1` (soundness sees no difference), but each
individual multiplicity is outside `{0, 1, -1}`, refuting `Circuit.statefulPolarity`. The same
argument extends to `Circuit.statefulSendsMaintain`: it is a claim about the payload of every
algebraically-satisfying send, and `guaranteesInvariants`-transfer (the invariant half of
`isSoundReplacementOf`) is likewise gated on `Circuit.satisfies`, not on every algebraic
assignment.

## What this means for the codebase

`PreservesLegality` cannot be obtained "for free" from an optimizer pass's existing correctness
proof, however that proof is phrased or strengthened — the gap is definitional, not a missing
lemma. Closing it for a real pass needs a **separate** legality-preservation argument per pass,
parallel to (not derived from) its `isSoundReplacementOf`/`isCompleteReplacementOf` proof: a proof
that whatever the pass does to a chip's bus interactions, the multiplicity and payload shapes
`Circuit.legalGuest` demands survive. `Circuit.legalGuest` and `Circuit.advancesClock` postdate
every pass in `ApcOptimizer/Implementation/OptimizerPasses/`, so none carries one today.

Under OpenVM the per-pass residue is smaller than "all of legality", and
`Audit/SoundnessGivesLegality.lean` measures it: the three bus-shape clauses come free on
accepted assignments, so what a pass still owes is those clauses on the algebraically-satisfying
assignments the semantics *rejects*, plus all of `Circuit.advancesClock`.

Practically, this is not as bad as it sounds: most passes either don't touch bus interactions at
all (pure algebraic simplification) or touch them in ways that are already syntactically
multiplicity-preserving (e.g. only rewriting a payload expression, leaving the multiplicity
expression untouched) — for those, `PreservesLegality` should be a short corollary of the pass's
existing correctness proof plus a syntactic side-condition, not a new semantic argument. The
translation-validation checker in `ApcOptimizer/VmSpec/Audit/SendOnlyPolarity.lean` is aimed
at exactly that residual case: instead of proving each pass preserves `statelessSendOnly`/
`statefulPolarity` in general, run the syntactic checker on the pass's *output* and treat a
`false` result as a bug (or a case the checker's constant-folding tier doesn't yet cover).
