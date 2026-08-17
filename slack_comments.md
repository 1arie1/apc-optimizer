Arie  [8:14 AM]

> That last one is a strictly sharper witness than Audit/LegalityPreservation.lean's, and it exposes a problem with that file: its counterexample runs on toyBusSemantics whose maintainsInvariants := True, which makes clause 2 of isSoundReplacementOf vacuous. Its docstring blames accepts ignoring multiplicity, but accepts is not the field that transports. As a claim about isSoundReplacementOf in the abstract the theorem is fine; as evidence about OpenVM it is not, and it's on the audited surface. I left the file alone — narrowing that prose is your call.[8:14 AM]

some claude comment i'm trying to understand but wanted to share before it gets lost

Arie  [10:13 AM]

> The fix, and why it's the same thing as the residue
>
>Add a third conjunct to Circuit.isSoundReplacementOf, transported like clause 2:
>
>▎ original.multiplicityDiscipline bs → optimized.multiplicityDiscipline bs, where the discipline is 0/1 on stateless and 0/±1 on stateful buses, quantified over satisfiesAlgebraic.[10:13 AM]

leaving this for you rather than adding more changes
