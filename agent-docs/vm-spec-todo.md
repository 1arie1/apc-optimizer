# `VmSpec` TODO — handoff list

The one place to look when resuming work on `ApcOptimizer/VmSpec/`. Consolidated from
[`vm-spec-wip.md`](vm-spec-wip.md) (design log, "Next step on resume"),
[`vm-spec-audit.md`](vm-spec-audit.md) (audit findings A–F) and
[`legality-preservation.md`](legality-preservation.md). Those files hold the reasoning; this one
holds only the list. Keep it in sync when an item lands.

State as of 2026-08-21, branch `ao-vm-spec`, HEAD after "VmSpec: input chip is HINT_STOREW; Host
takes a list of input chips". `lake build` clean, `Scripts/check-proof-integrity.sh` passes.

## Waiting on a decision

**Arie's `multiplicityDiscipline` conjunct** ([`slack_comments.md`](../slack_comments.md), 10:13).
Add a third conjunct to `Circuit.isSoundReplacementOf`, transported like clause 2:
`original.multiplicityDiscipline bs → optimized.multiplicityDiscipline bs`, where the discipline is
`0`/`1` on stateless buses and `0`/`±1` on stateful ones, quantified over `satisfiesAlgebraic`.
Nothing in the tree mentions `multiplicityDiscipline` yet. This is the root-cause fix for the
`PreservesLegality` gap, it edits the audited `Spec.lean`, and he left it deliberately rather than
landing it himself. His earlier note (8:14) about `Audit/LegalityPreservation.lean`'s prose is
already addressed — the docstring now says both halves of `toyBusSemantics` are load-bearing and
points at the OpenVM route.

## Structural work, roughly by priority

1. **Record the wraparound side condition in the manuscript**, on `eq:stateless_as_pred`. The Lean
   has the honest version (`VmAssignment.withinBudget` plus `L * maxInstances < p`); the prose does
   not. Small, and independent of everything else here.
2. **Wire the VM-level statement to the optimizer.** `openVm_vmSoundReplacement` takes a
   `List.Forall₂` of per-chip `Circuit.isSoundReplacementOf`, which
   `openVmOptimizer_maintainsCorrectness` produces. `PreservesLegality` is what blocks assembly:
   not derivable from soundness (Phase 7, and `legality-preservation.md`), so each pass needs its
   own legality-preservation argument. Downstream of the `multiplicityDiscipline` decision above.
   Also what would let the VM-level statement *seed* `Scripts/unused-theorems.txt` instead of the
   hand-maintained ignore block the folder needs today.
3. ~~Model the connector chip and the execution-bridge terminator, to discharge
   `Host.pinsRanks`.~~ Done — `vm-spec-wip.md`, Phase 6.
4. ~~Check `Circuit.legalGuest` against a whole exported APC.~~ Done — finding G in
   `vm-spec-audit.md`, `ApcOptimizer/VmSpec/Audit/RealApcLegality.lean`. Both multiplicity clauses
   hold and are proved by static analysis; `Circuit.advancesClock` is false. **Replaced by: fix
   `Circuit.advancesClock`**, with step-by-step instructions in
   [`advances-clock-fix.md`](advances-clock-fix.md) — one free change (allow a memory access at
   exactly `base`) and one real one (take receives out of the clause and bound their timestamps at
   VM level, where they belong).
5. **Parameterize `openVmHost` by the bus map** rather than hard-wiring `defaultBusMap`.
6. **Model `HINT_BUFFER`** as a second entry in `Host.inputChips` — `Rv32HintStoreAir`'s other
   opcode, count off operand `a`, many words per instance. Phase 9 reshaped `Host` for exactly
   this, and it is what relieves Finding D's budget squeeze (one bridge arc per chunk again rather
   than per byte).
7. **The completeness half** (`CanProduce ⟨host, G⟩ e → CanProduce ⟨host, G'⟩ e`).
   `Circuit.isCompleteReplacementOf` is gated on `Circuit.admissible`, a list-order property
   (`admissibleMemoryBus`) that order-blind `VmSat` cannot supply. Either it becomes an explicit
   "real trace" hypothesis, or `MemoryBus.lean` changes.

## Open audit findings

Detail and mechanisms in [`vm-spec-audit.md`](vm-spec-audit.md).

- **A3 — `inputChunkOf` is not a function of what the VM did.** A self-cancelling witness
  (`ptrTime = base + 1`, `oldWord = #v[byte,0,0,0]`, `wordTime = base + 2`) collapses the whole
  contribution to the bridge pair for *any* `byte`, so `Classical.choose` recovers an unspecified
  datum. Confirmed unaffected by the `HINT_STOREW` rewrite. Fix: the AssertLt discipline
  (`prev_timestamp < timestamp`) on the witness, or make the witness part of the assignment rather
  than recovering it by choice.
- **B, quantitative half.** `Host.noMultOverflow` counts guest interactions plus `1`. The `1` pays
  for `Host.exemptChip` inside `maintains_of_stateful_active`; every other host chip is excluded
  qualitatively (`sinksAreTables`, `statefulChipsMaintain`), not counted. So the bound's safety
  lives in per-host proof obligations rather than in the budget field.
- **D — the configuration conditions are never instantiated, and they bind.** No `OpenVmParams`
  value exists anywhere in the repo. The probe is one concrete `example : OpenVmParams babyBear`
  at the sizes actually targeted. Sharper since Phase 9: `maxInputInstances` counts input *bytes*,
  sharing `windowOk`'s budget line, so at `maxInstances = 2²²` and `maxWindow = 478` there is room
  for fewer than 7711 input bytes per segment.
- **F — three audited definitions with no consumer.** `VmCompleteReplacement`, `VmEquivalent`,
  `PreservesDegree` are reachable only from `Validation.lean`'s sanity lemmas, so a mistake in them
  stays invisible until the completeness half is attempted.
- **Lower tier.** The input chip's *receive* timestamps (`ptrTime`/`wordTime`) are still free where
  `advancesClock` would put them inside the window — this is A3's mechanism. `openVmHost` still
  treats `ptrReg` as a VM-wide constant when it is instruction operand `b` (`TODO(AO)` on
  `InputRead.interactions`). `memoryInitHostChip` still allows arbitrary initial memory in address
  spaces `1`/`2`, so a segment's public inputs are an unobserved VM input.

## Housekeeping

- `arie/main` is 3 commits ahead of this branch (`11c7ca6`, `3bc9b66`, `ad4310b`). Rebase before
  opening or updating a PR — `AGENTS.md`'s own rule.
- The branch's tracked upstream is `arie/ao-vm-spec`; `alex/ao-vm-spec` also carries it.
