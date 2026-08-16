# Does soundness imply legality preservation?

**Question.** `openVm_vmSoundReplacement` (`ApcOptimizer/VmSpec/Theorems.lean`) takes
`PreservesLegality` as a hypothesis rather than deriving it from the `List.Forall₂`
`Circuit.isSoundReplacementOf` hypothesis it also takes. Could `PreservesLegality` be derived —
i.e., does a sound replacement automatically preserve `Host.legalGuest`?

**Answer: no**, and not as an artifact of how the proof is currently structured — it falls
straight out of what the two definitions quantify over. `ApcOptimizer/VmSpec/Audit/
LegalityPreservation.lean` is a compiling Lean file proving this: a concrete pair of circuits
where the replacement is a sound `Circuit.isSoundReplacementOf` and simultaneously violates
`Circuit.statelessSendOnly` outright.

## The mechanism

`Circuit.legalGuest` (`Legal.lean`) has three clauses, and all three share a shape:
`Circuit.algebraicallyForces r stateful P` — some property `P` must hold of *every*
algebraically-satisfying assignment, full stop. No bus-acceptance is required. That is
deliberate: a real OpenVM AIR cannot check `legalGuest` at runtime (each clause quantifies over
all assignments, which no constraint system evaluates), so a chip has to be *built* so the
property is true identically, not merely true on the runs that occur.

`Circuit.isSoundReplacementOf`, by contrast, only has two obligations, and both are weaker in
exactly the direction that matters:

1. Every assignment satisfying `Circuit.satisfies` — algebraic constraints **and** bus
   acceptance — must have a matching original-circuit assignment with the same
   `Circuit.sideEffects`.
2. `sideEffects` covers only **stateful** buses, and only their **net** multiplicity per message
   (`Circuit.allEffects` restricted and summed) — never a stateless bus, and never the shape of
   the individual interactions that produced the net.

So a bus interaction's multiplicity is invisible to soundness in two independent ways: on a
stateless bus, it isn't tracked by `sideEffects` at all; on any bus, only the *sum* the guest
sends is compared, not what any one interaction sends.

## The witness

`ApcOptimizer/VmSpec/Audit/LegalityPreservation.lean`:

- `toyBusSemantics` — one stateless bus, accepting every message regardless of multiplicity. This
  is not a contrived choice: `ApcOptimizer.OpenVM.accepts` never reads `BusInteraction.multiplicity`
  for any of OpenVM's four lookup tables, only the payload. Every real OpenVM lookup bus behaves
  this way.
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

## Does the same trick break the stateful clauses too?

Yes, by an analogous move, though the file only formalizes the stateless case (the mechanism is
identical and a second Lean witness would not add anything). `Circuit.sideEffects` sums
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

Practically, this is not as bad as it sounds: most passes either don't touch bus interactions at
all (pure algebraic simplification) or touch them in ways that are already syntactically
multiplicity-preserving (e.g. only rewriting a payload expression, leaving the multiplicity
expression untouched) — for those, `PreservesLegality` should be a short corollary of the pass's
existing correctness proof plus a syntactic side-condition, not a new semantic argument. The
translation-validation checker in `ApcOptimizer/VmSpec/Audit/SendOnlyPolarity.lean` is aimed
at exactly that residual case: instead of proving each pass preserves `statelessSendOnly`/
`statefulPolarity` in general, run the syntactic checker on the pass's *output* and treat a
`false` result as a bug (or a case the checker's constant-folding tier doesn't yet cover).
