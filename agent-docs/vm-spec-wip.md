# VM-level multi-chip correctness spec — design notes (WIP, handoff doc)

Not a finished design doc — a snapshot for resuming this conversation on another machine.
Delete or fold into `architecture.md` once the design settles.

## Goal

Specify multi-circuit ("multi-chip") correctness for apc-optimizer: equivalence for a *list* of
guest chips together, generalizing the single-`Circuit` `refines` in `ApcOptimizer/Spec.lean`.
Source: the "VM equivalence" section — the last section before the bibliography — of
`~/repos/manuscript-powdr-ver/vm.tex` (`\vmGuestChips`/`\vmSat`/`\vmCanEffect`, equations
`eq:vm_eq_raw`/`eq:vm_eq`).

Manuscript's model: a VM assignment is a concrete number of instances for each chip type and an
assignment to all instances; some chip types (memory init, memory final, output, each lookup
table) can only be instantiated once. `VmSat(G, a)` holds when the VM is satisfied under the host
chips and guest chips `G` on assignment `a`. `CanEffect(G, e) := ∃ a, GetEffects(a) = e ∧
VmSat(G, a)`. Equivalence: `∀e, CanEffect(G,e) ↔ CanEffect(G',e)`.

## Status

Everything lives in `ApcOptimizer/VmSpec/`, with `ApcOptimizer/VmSpec.lean` as the aggregator
(`ApcOptimizer.lean` imports only that). Builds clean (`lake build`, zero warnings) and
`Scripts/check-proof-integrity.sh` passes; the soundness theorems rest on the three standard
axioms. Layout:

| file | contents | audited? |
| --- | --- | --- |
| `Basic.lean` | `HostChip`, `Host`, `Vm`, `VmAssignment`, `VmSat`, `CanProduce`, `VmSoundReplacement`/`VmCompleteReplacement`/`VmEquivalent` — the spec, definitions only | yes |
| `Legal.lean` | `Circuit.legalGuest` — what a VM requires of a guest chip (a *hypothesis*, so the risk is vacuity) | yes |
| `OpenVm.lean` | `openVmHost` and its nine host chips, plus `Circuit.advancesClock` | yes |
| `Theorems.lean` | the VM-level theorems; statements only, each proved by one-line delegation | yes |
| `Audit/OpenVmLegalAudit.lean` | real OpenVM circuit shapes checked against the audited hypotheses | yes (audits the audit surface) |
| `Audit/SendOnlyPolarity.lean` | decidable syntactic checker for two of `legalGuest`'s clauses | yes (audits the audit surface) |
| `Audit/LegalityPreservation.lean` | formal counterexample: soundness does not imply `PreservesLegality` | yes (audits the audit surface) |
| `Implementation/Rank.lean` | `RankModel` — the ordering the induction descends on; deliberately not a `Host` field | no |
| `Implementation/Counting.lean` | the honest ℕ counts (`countAt`, `uniformAt`) that keep balancing from wrapping `ZMod p` | no |
| `Implementation/Realizes.lean` | `Host.realizes`, `Host.pinsRanks`, `forcesAccepts_of_hostSound` | no |
| `Implementation/Connection.lean` | `soundWitness`, `vmSoundReplacement_cons`, and the assembly | no |
| `Implementation/OpenVmConnection.lean` | every host-side condition discharged for `openVmHost` | no |
| `Implementation/Chain.lean` | `VmChain.Chain` — balanced arcs on a `ZMod p` clock, and the walk that orders them | no |
| `Implementation/OpenVmChain.lean` | that walk applied to the execution bridge: `openVmHost_pinsRanks` | no |
| `Implementation/Validation.lean` | sanity theorems: instance order is invisible, the guest-chip list is a *set*, `VmSoundReplacement` is a preorder | no |

The audit boundary is the directory: everything directly under `VmSpec/` is audited, nothing under
`VmSpec/Implementation/` is — mirroring `AGENTS.md`'s rule for `ApcOptimizer/Implementation/`. There
is no leak: every hypothesis of `openVm_vmSoundReplacement` is expressed in audited terms.

Full current content of `Basic.lean` is reproduced verbatim at the bottom of this doc in case the
working-tree copy doesn't make it across machines.

The sections below are a chronological log and mostly predate the folder split, so they name files
by their old paths (`VmSpec.lean`, `VmSpecConnection.lean`, …); the table above is the map.

## Design decisions made so far, with rationale

1. **Host chips = "allowed interactions" only, no algebraic constraints of their own.** This is
   exactly what `BusSemantics` in `Spec.lean` already provides for a single circuit (a set of
   per-message predicates standing in for an opaque environment) — so `VmSpec.lean` does not
   import `BusSemantics` at all; `HostChip.legal : BusState p → Prop` supersedes it.

2. **Balance-only, no ordering discipline.** User's explicit call: *"In this Vm-level definition,
   memory isn't special or ordered. All we have is balancing. Some of the order requirements in
   the current spec are actually suspect and may need to change"* — a note for possibly
   reconsidering `MemoryBus.lean`'s `admissibleMemoryBus` later, **not** acted on now (that file
   is untouched). Consequences baked into the current file:
   - No reuse of `admissibleMemoryBus`/list-order reasoning anywhere.
   - Stateless (lookup) and stateful (memory) buses are treated identically: `VmSat` requires the
     net multiplicity of *every* message, summed over every guest chip's evaluated bus
     interactions and every host chip's contribution, to be zero. This one requirement subsumes
     what `BusSemantics.accepts` did for a single circuit — there's no separate acceptance check.
   - `Circuit.netContribution` (new helper) is `Circuit.sideEffects` generalized to cover every
     bus interaction, not just stateful ones.

3. **`Effect` is not one monolithic `BusState p`.** First cut used a single `BusState p` (net
   multiplicity per message, summed over host chips with a nonzero `effect` projection), but the
   user pointed out this can't represent a *stream*: `BusState` is order-blind (it nets by exact
   payload) — fine for a final memory snapshot, wrong for input, where position is the whole
   point ("I think of the inputs as a stream"). Landed on:
   - `Input p := List (ZMod p)` — flat stream; chunk boundaries between input-chip invocations
     are **not** part of the type, only the concatenation is observable (chunking is a guest
     implementation detail — how many bytes per `read()` call — not part of the VM's external
     interface; an optimization that merges/splits reads shouldn't change the observable effect).
   - `Output p := List (ZMod p)` — flat array read back from the output chip (single instance —
     "the output chip runs once" — so no ordering concern; user asked for this to also be a flat
     array rather than an address→value map, to match `Input`'s shape).
   - `Effect p := { input : Input p, output : Output p }`.
   - Which physical input-chip instance produced which stream position is **not** modeled
     globally. `CanEffect` instead existentially quantifies over a permutation of the input-chip
     instances lining up into the observed stream. This directly answers "how does chip
     execution order relate to stream order": it doesn't — no general ordering concept is
     reintroduced anywhere in the file; where a genuinely sequential resource (the input stream)
     needs an order, that order is chosen as part of the witness, not fixed by the model.

4. **`Vm` bundles the fixed VM description**: `hostChips`, `inputChipIndices` (which indices are
   input-chip instances — any number), `inputChunk` (how to read one instance's contribution as
   its stream chunk), `outputChipIndex` (the single output chip), `outputArray` (how to read its
   contribution as the output array). Payload-layout decoding is deliberately left abstract here
   — same spirit as `Spec.lean` leaving `BusSemantics` abstract, to be concretized per-VM later
   (analogous to how `OpenVmSemantics.lean` concretizes `BusSemantics`).

## RESOLVED — instance counts are now part of the witness

User caught a real gap: the original definition did not let a `VmAssignment` choose the number
of instances of each chip — instance counts were fixed externally (`guestChips.length`,
`vm.hostChips.length`, `vm.inputChipIndices.length`), never part of the witness. This contradicted
the manuscript's literal wording ("a VM assignment is a concrete number of instances for each
chip type **and** an assignment to all instances"), and mattered practically: a real guest
program's basic-block trip counts, and the input chip's invocation count, are data-dependent —
not knowable or fixable by the optimizer — so a useful equivalence needs to hold across *every*
possible instance count, not one fixed multiset baked into the theorem statement.

### Fix implemented

Split **types** (fixed, matched 1-1 before/after — what the optimizer actually preserves) from
**instances** (existentially counted, part of the witness):

- `guestChips`/`guestChips'` stay lists of *types*, but `VmAssignment.guestAssignment` is now
  `(t : Fin guestChips.length) → List (Variable → ZMod p)` — a list of instance-assignments per
  type, whose length is the existentially-chosen trip count. `VmSat`'s balance sum is a nested
  sum: over types, then over that type's realized instances.
- Same move for host chips: `Vm.inputChipType : Fin hostChips.length` designates a single input
  chip *type*; `VmAssignment.hostContribution` is `(t : Fin hostChips.length) → List (BusState p)`,
  so the assignment gives that type however many contributions it wants. `CanEffect` no longer
  needs a fixed `inputChipIndices` list — it reads the stream straight off
  `a.hostContribution vm.inputChipType` in list order (`((a.hostContribution
  vm.inputChipType).map vm.inputChunk).flatten = e.input`). A first cut wrapped this in an
  existential permutation, but that's redundant: `VmSat` never constrains a chip type's
  instance-list order (`legal` is a membership check, the balance check sums — both
  order-blind), so that order is already a free choice of the witness `a`; any ordering the
  permutation could produce, `a` could have been constructed in directly. Removed.
- Singleton-ness is **opt-in**: `HostChip` gained a `singleton : Prop := False` field (defaults
  to unbounded instances); `VmSat` adds the conjunct `(hostChips.get t).singleton →
  (a.hostContribution t).length ≤ 1`. It's "at most one," not "exactly one" — for the output
  chip, `CanEffect`'s own extraction (`∃ c, a.hostContribution vm.outputChipType = [c] ∧ ...`)
  additionally forces exactly one whenever an effect is actually produced; other singleton host
  chips (mem init/final, each lookup table) are only constrained to ≤ 1 by `VmSat` itself.

Builds clean end to end (`lake build`, zero warnings). Still definitions only, no theorems.

## Order-invariance, now an actual proved theorem

User asked to turn the "the permutation is redundant" claim into a theorem. It's fully proved
(not a `sorry` — this repo's `Scripts/check-proof-integrity.sh` forbids `sorry`/`admit`/`axiom`
outright, so a stub wasn't an option). Two lemmas, right after `VmSat`'s `ANCHOR_END: vmSat`:

- `VmSat.of_perm`: if `a'` and `a` agree up to permutation at every guest- and host-chip type
  (`∀ t, (a'.guestAssignment t).Perm (a.guestAssignment t)` and likewise for
  `hostContribution`), then `VmSat a → VmSat a'`.
- `VmSat.perm_iff`: the `Iff` version (apply `of_perm` both ways, using `.symm` on the `Perm`s).

Proof is mechanical: `VmSat`'s membership check and singleton-length check transport directly
across `List.Perm.mem_iff`/`.length_eq`; the balance sum transports via `Finset.sum_congr` +
`List.Perm.map`/`.sum_eq` (permuting a list doesn't change what a commutative-monoid sum of it
is). Needed `omit [Fact p.Prime] in` before each — neither actually uses field-ness, and Lean's
`linter.unusedSectionVars` flags the auto-bound instance if left in.

**Gotcha hit along the way:** `Scripts/check-proof-integrity.sh`'s forbidden-tactic grep is a
bare `\badmit\b` word-boundary match over the whole source, including doc-comment prose — the
module docstring originally said guest-chip lists "admit exactly the same effects" (a legitimate
English word), which the grep can't distinguish from the `admit` tactic. Had to reword to "can
each produce exactly the same effects". Worth remembering if writing more prose in this file:
avoid the bare words `sorry`/`admit`/`native_decide` even as English.

**`Scripts/unused-theorems.txt` gotcha:** the unused-theorem checker only considers a theorem
"used" if reachable from `Optimizer.lean`'s `*_maintainsCorrectness` roots — and `VmSpec.lean`
isn't wired into that pipeline at all yet, so *any* theorem added here, no matter how it's used
internally, gets flagged. Added `VmSat.of_perm`/`VmSat.perm_iff` to `[ignore]` with a comment
explaining this is a different class of false-positive than the existing entries (which are
about `rfl`-lemmas invisible to the term-walk) — this file just isn't reachable from the audited
roots by construction, not because the lemmas are dead. **Revisit this ignore-list entry once
`VmSpec.lean` is wired into (or itself seeds) the correctness roots** — at that point these
lemmas should become genuinely reachable and the entry should be removed.

Full proof-integrity check (`bash Scripts/check-proof-integrity.sh`) passes end to end.

## `VmSat` split into named pieces

User asked to split up `VmSat` (it had grown into one 4-way `∧` blob). Broke it into five
`VmAssignment` dot-notation methods, right before the `VmSat` def, matching how `Spec.lean`
itself splits `Circuit.satisfies`/`Circuit.admissible`/`Circuit.guaranteesInvariants` rather than
inlining everything into one `Circuit.isCorrect`-style def:

- `VmAssignment.guestSatisfies` — guest algebraic constraints.
- `VmAssignment.hostLegal` — host contributions are legal.
- `VmAssignment.singletonsRespected` — singleton-opted-in host types stay ≤ 1 instance.
- `VmAssignment.netContribution : BusState p` — the balance sum itself, now a first-class value
  (not just an inline expression), so `VmSat.of_perm`'s proof can talk about `a'.netContribution
  = a.netContribution` directly instead of the raw nested-sum expression.
- `VmAssignment.balances` — that `netContribution` is zero everywhere.
- `VmSat := guestSatisfies ∧ hostLegal ∧ singletonsRespected ∧ balances`.

Had to touch `VmSat.of_perm`'s proof (the balance-sum step no longer matches via plain `rw` once
the goal is folded behind `a'.netContribution message = 0` instead of the raw sum) — rewrote it
to prove `a'.netContribution = a.netContribution` as a standalone `have` (via `funext` + `show`
to unfold back to the raw sums for the `Finset.sum_congr` rewrite), then combined with `h4`
via `congrFun`/`.trans`. `VmSat.perm_iff` needed no change (it only calls `of_perm` twice).
None of the new `def`s tripped the unused-theorem checker — it only scans `theorem`/`lemma`.

Full build + `check-proof-integrity.sh` both clean after the split.

## Draft OpenVM host chips (`ApcOptimizer/VmSpecOpenVm.lean`, new file)

User asked for concrete `HostChip` drafts matching OpenVM's actual host chips, built against
`ApcOptimizer.OpenVM`'s existing semantics (`OpenVmSemantics.lean`) rather than invented from
scratch. Sits alongside `VmSpec.lean` the same way `OpenVmSemantics.lean` sits alongside
`Spec.lean` — `VmSpec.lean` itself stays VM-generic and untouched. Wired into the root
`ApcOptimizer.lean` aggregator; builds clean, no theorems added (so nothing new for the
unused-theorem checker to flag).

Contents: `busStateOf` (a local helper turning an explicit `List (BusInteraction (ZMod p))` into
a `BusState p`, same rule as `Circuit.allEffects`), `lookupTableHostChip` (generic: legal only to
touch an accepted payload on one bus id) instantiated for all four of `OpenVM.accepts`'s
stateless tables (`pcLookupHostChip`, `bitwiseLookupHostChip`, `variableRangeCheckerHostChip`,
`tupleRangeCheckerHostChip` — mirroring `OpenVM.accepts`'s exact conditions, including its known
PC-lookup arity-only approximation), plus `memoryInitHostChip` (sends each address's initial
word once, `singleton := True`), `memoryFinalizeHostChip` (receives any final word in address
spaces `1`/`2`, `singleton := True`), `outputHostChip` (receives any final word at address space `3`,
`singleton := True`), and `inputHostChip` (peeks a pointer and word-count register, then writes
that many unconstrained words at consecutive addresses; `singleton := False` since it may run
any number of times).

Simplifications flagged in the docstrings: no timestamp ordering is modeled (consistent with
this file's balance-only design — nothing here checks timestamps at all, they're hardcoded to
`0`); each written word carries one input value in its low limb rather than packing four bytes
per word (real OpenVM byte-packing is orthogonal to what these chips illustrate).

**Update — now wired into a concrete `openVm : Vm p`.** The array-extraction gap above is
resolved by *tightening* `outputHostChip`/`inputHostChip`'s `legal` predicates: instead of "any
final word" they now pin the contribution *exactly* to the messages a witness struct would
produce —

- `OutputRead (p)`: `count`/`words`, laid out contiguously in address space `3` from address
  `0` (`.interactions` builds the `-1`-multiplicity receives). `outputHostChip.legal contribution
  := ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)`.
- `InputRead (p)`: `ptr`/`count`/`bytes`/`oldWords`, `.interactions` builds the register-peek
  pairs plus the `count` write pairs (mirrors the earlier inline version, just factored out so
  it's shared between `legal` and the extractor). `inputHostChip.legal` is the analogous
  `∃ r, contribution = busStateOf (r.interactions ...)`.

`inputChunkOf`/`outputArrayOf` then recover *a* witness via `Classical.choice`
(`open Classical in noncomputable def ... := if h : ∃ r, ... then h.choose.bytes else []`) —
they don't need the witness to be *the* unique one, only *some* witness whose reconstructed
messages match, since that's all `legal` itself promises; nothing here proves injectivity (a
claim an earlier docstring draft overreached on and had to be walked back). Off-spec
(non-`VmSat`-legal) contributions fall back to `[]`, which is never reached in practice since
these functions are only ever applied within `CanEffect` to a contribution `VmSat` already
proved `legal`.

`openVm (ptrReg countReg) (memBusId := 1)` assembles all eight `HostChip`s
into one list and wires `inputChipType`/`outputChipType`/`inputChunk`/`outputArray` together
(indices `⟨7, by simp⟩`/`⟨6, by simp⟩` — `by decide` failed here since the list's *elements*
contain free variables (`ptrReg` etc.), even though only the list's *length* — which doesn't
depend on element values — matters; `simp` reduces the length symbolically instead). `openVm`
and both extractors are `noncomputable` (unavoidable — `Classical.choice` isn't computable).
Builds clean end to end, no new theorems (so nothing for the unused-theorem checker to flag).

## `Vm` split into `Host` + `Vm` (user-driven restructuring, propagated throughout)

User started rewriting `VmSpec.lean`'s definitions directly (not through discussion first this
time) and asked me to propagate the fixes through the rest of the file, which was left
half-migrated (compiled up through `VmSat`, broken from `VmSat.of_perm` on — stale field names,
a 4-way `obtain` pattern that no longer matched the new 3-way `VmSat`, wrong argument counts).
Also broke `VmSpecOpenVm.lean`, which imports `VmSpec.lean` and had to follow.

**What changed, structurally:**
- `HostChip` unchanged in spirit (`legal`, `singleton := False`), doc comments trimmed.
- New `abbrev ChipAssignment (p) := Variable → ZMod p` — names what used to be written out as
  `Variable → ZMod p` everywhere.
- **`Vm` is no longer one flat structure.** It split into `Host` (the host-chip side: `chips`,
  `inputChip`/`getInputChunk`, `outputChip`/`getOutput`, plus a new `outputSingleton :
  (chips.get outputChip).singleton` field) and `Vm` (`host : Host p`, `guestChips : List (Circuit
  p)`). `VmAssignment`/`VmSat` take a bundled `vm : Vm p` (both sides fixed at once — that's what
  satisfiability needs); `CanEffect`/`vmEquivalent` take `host : Host p` and `guestChips`
  separately (since guest chips are what varies between before/after, host doesn't) — internally
  building a `let vm : Vm p := { host, guestChips }` to hand to `VmSat`.
- **`outputSingleton` is a genuine improvement, not just a rename.** Previously, the output
  chip's type actually being `HostChip.singleton` was only a docstring convention ("expected —
  by convention, opt into..."); nothing enforced it. Now `Host` can't be constructed at all
  unless you supply a proof that its designated `outputChip` opts into `singleton` — so
  `CanEffect`'s `∃ c, ... = [c]` clause is doing real, structurally-backed work (ruling out zero
  instances; `VmSat` + `outputSingleton` already rule out two or more).
- Field renames: `guestAssignment` → `guestAssignments`, `hostContribution` → `hostAssignment`,
  `netContribution` → `netBus` (`VmAssignment.netBus`; the name `VmAssignment.effects` was
  briefly used for this, then freed up for the `VmEffect` extraction — see the section below),
  `inputChipType`/`inputChunk` → `Host.inputChip`/`Host.getInputChunk`,
  `outputChipType`/`outputArray` → `Host.outputChip`/`Host.getOutput`.
- `satisfiesHost` now bundles what used to be two separate methods (`hostLegal` +
  `singletonsRespected`) into one `∧`. The version I found mid-edit had a real bug —
  `legal contribution ∧ singleton → length ≤ 1` parses (via `∧` binding tighter than `→`) as
  `(legal ∧ singleton) → length ≤ 1`, which drops the legality *requirement* entirely (turns it
  into a hypothesis of an implication whose conclusion doesn't even mention `contribution`).
  Fixed to `(∀ t, ∀ contribution ∈ ..., legal contribution) ∧ (∀ t, singleton → length ≤ 1)` —
  two separate universally-quantified conjuncts, matching what the two former methods asserted.
- `VmSat.of_perm`'s proof needed restructuring beyond renames: `VmSat` is now `guest ∧ (host ∧
  balances)`-shaped (3-way, right-associated) with `host` itself `legal ∧ singleton` (2-way), so
  the old flat `obtain ⟨h1,h2,h3,h4⟩`/`⟨h1,h2,h3,h4⟩` no longer matches the actual nesting —
  became `obtain ⟨h1, ⟨h2,h3⟩, h4⟩` / `⟨h1, ⟨h2,h3⟩, h4⟩` on the way out.

**`VmSpecOpenVm.lean` propagation:** all eight `HostChip` drafts were untouched (they don't
reference `Vm`/`Host` at all), only the final assembly did. `openVm : Vm p` became `openVmHost :
Host p` (renamed since it now only builds the host side; pair it with a guest-chip list to get a
`Vm p`) — literal field renames (`hostChips`→`chips` etc.) plus one new field,
`outputSingleton := trivial` (the output chip's `singleton := True` makes this discharge for
free once `chips.get outputChip` reduces to it).

Full build + `check-proof-integrity.sh` both clean after propagating everything. `Scripts/unused-
theorems.txt`'s `[ignore]` entries for `VmSat.of_perm`/`VmSat.perm_iff` didn't need updating —
names unchanged, only signatures.

## `VmAssignment.effects` now takes the `VmSat` proof (the resolved TODO)

`VmAssignment.effects : VmAssignment p vm → VmEffect p` used to read the output with a partial
`match`:

```lean
output := match a.hostAssignment vm.host.outputChip with
  | [c] => vm.host.getOutput c
  | _   => []          -- ← junk fallback, unreachable for satisfying assignments
```

and carried a TODO asking whether the output chip's singleton-ness could retire that fallback.
It can, and the ingredients were already in place: `Host.outputSingleton` proves the designated
output chip opts into `HostChip.singleton`, and `VmAssignment.satisfiesHost`'s second conjunct
turns that into `(a.hostAssignment vm.host.outputChip).length = 1` — note **`= 1`**, not the
`≤ 1` that earlier drafts of this doc describe; the user tightened it, which is exactly what
makes the list provably non-empty rather than merely short.

So `effects` now takes the satisfaction proof as an argument and uses `List.head`:

```lean
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) (h : VmSat vm a) : VmEffect p :=
  { input := (a.hostAssignment vm.host.inputChip).map vm.host.getInputChunk |>.flatten,
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).head (by
      obtain ⟨-, ⟨-, hsingle⟩, -⟩ := h
      have hlen := hsingle vm.host.outputChip vm.host.outputSingleton
      intro hnil
      simp [hnil] at hlen)) }
```

Notes on this shape:
- Returning **data** that depends on a **proof** is fine here — `List.head`'s non-emptiness
  argument is a `Prop`, so definitional proof irrelevance means the result doesn't vary with
  which proof of `VmSat vm a` you hand it.
- `obtain` on `h : VmSat vm a` works even though `VmSat` and `satisfiesHost` are `def`s rather
  than literal `And`s — `rcases` whnf's through them (`VmSat.of_perm` already relied on this).
- The declaration order matters: `effects` must come *after* `VmSat` in the file now that it
  mentions it. It already did.

`CanEffect` threads the proof through, becoming a nested existential rather than a conjunction:

```lean
∃ (a : VmAssignment p vm) (h : VmSat vm a), a.effects h = e
```

This is equivalent to the pre-TODO formulation, which spelled the input and output components
out inline (`... ∧ ∃ c, a.hostAssignment host.outputChip = [c] ∧ host.getOutput c = e.output`):
`VmSat` forces that list to be exactly `[head]`, so the old `∃ c, ... = [c]` clause and the new
`head` read pick out the same instance. The gain is that the output convention now lives in one
place (`effects`) instead of being restated at the `CanEffect` use site.

Knock-on doc fix in `VmSpecOpenVm.lean`: `busStateOf`'s docstring cited
"`Circuit.allEffects`/`VmAssignment.effects`" for the net-multiplicity rule, which was right
when `effects` *was* the net contribution — now that name means the `VmEffect` extraction, so it
points at `VmAssignment.netBus`.

Full build + `check-proof-integrity.sh` clean.

## Memory init/finalize tightened; `HostChip.legal` → `HostChip.canEffect`

**Naming:** `HostChip`'s predicate field is now `canEffect`, not `legal` (user rename, matching
the top-level `CanEffect` — a host chip "can effect" a `BusState`, a VM "can effect" a
`VmEffect`). Sections above this one still say `legal`; they describe earlier states of the
file and were left as-is.

**Memory init is all-zero.** `memoryInitHostChip` used to take an
`initialWord : ZMod p → ZMod p → Vector (ZMod p) 4` parameter, abstracting over what each
address starts as; it's now hardcoded to `f.data = #v[0, 0, 0, 0]`, and the parameter is gone
from `memoryInitHostChip` and from `openVmHost`. The abstraction wasn't buying anything: memory
genuinely does start zeroed, and program input enters through `inputHostChip` (which writes over
those zeros) rather than through a specially-seeded initial image.

**Memory finalization only covers address spaces 1 and 2.** `memoryFinalizeHostChip` previously
accepted a `-1` on any address; it now additionally requires
`memoryPayload? message.2 = some f ∧ (f.addressSpace.val = 1 ∨ f.addressSpace.val = 2)`
(registers and main memory). The point is address space `3`: that's the output space, and
`outputHostChip` is what receives it — a read that *is* externally observable. Without this
restriction the two chips overlap on AS-3, so a VM could route its output words into
finalization instead, balancing the bus while producing an empty observed output. The
restriction is what forces AS-3 through the observable path.

Note the resulting asymmetry, which is intended: **init** covers AS 1/2/3 (it seeds the output
space with zeros too), while **finalize** covers only AS 1/2 and the **output chip** finalizes
AS 3. The three together still tile every address space exactly once, which is what balance
needs.

`MemoryPayload.isByteChecked` from `OpenVmSemantics.lean` happens to be definitionally the same
condition (`addressSpace.val = 1 ∨ = 2`), but it is deliberately *not* reused here — it means
"OpenVM byte-range-checks writes to this space", which is a different claim that merely happens
to hold of the same two spaces.

## The connecting theorem, soundness half (`ApcOptimizer/VmSpecConnection.lean`, new file)

Proved: `canEffect_of_isSoundReplacementOf` — if every chip of `G'` is a
`Circuit.isSoundReplacementOf` the corresponding chip of `G`, then `CanEffect host G' e →
CanEffect host G e`. Depends only on Lean's three standard axioms. This is the `←` half of
`VmEquivalent`; completeness is not attempted (see the gap list below for why it is harder).

**The witness construction.** Given a satisfying `a'` for the optimized VM: keep the host's
*stateful* chips (memory init/finalize, input, output) byte-for-byte; replace each guest
instance's assignment by the one soundness promises (`soundWitness`, a `Classical.choose` behind
a `dite`, same pattern as `inputChunkOf`); let the host's *lookup* chips absorb whatever
stateless imbalance that leaves. Effect preservation is then free — `getInputChunk`/`getOutput`
read only the input/output chip contributions, which never moved.

**Two vocabulary gaps, each filled by one condition on the `Host`:**

1. `Circuit.satisfies` demands `BusSemantics.accepts` on every active message;
   `VmAssignment.satisfiesGuest` demands only the algebraic constraints. Without recovering
   `accepts` the per-chip hypotheses cannot be invoked at all. → `Host.forcesAccepts`.
2. `Circuit.sideEffects` — what a sound replacement preserves — covers only *stateful* buses,
   while `VmAssignment.netBus` sums over all of them. So a legal optimization (dropping a
   redundant range check) can unbalance a lookup bus, and the host's lookup chips must be
   rebuilt. → `Host.absorbsStateless`.

Nice consequence worth remembering: the balance-over-*all*-buses decision is what *creates* gap
2, and also what makes gap 1 closable in principle — a guest send on a lookup bus has nowhere to
go but a chip that only receives table entries.

**`Host.forcesAccepts` is FALSE for `openVmHost` as `VmSat` currently stands.** This is the main
finding, and it is not a proof-engineering obstacle but a real hole in the definition.
Multiplicities live in `ZMod p` and `VmSat` puts **no bound on realized instance counts**, so:
realize `p` instances of one guest chip, each sending the *same* unaccepted lookup message. Their
net multiplicity is `p = 0`, no host chip needs to receive it, and `VmSat` holds anyway — with
every other chip at the zero `BusState` (the three `singleton` chips take a single zero
contribution; the output chip takes the empty `OutputRead`, whose `interactions` list is `[]`).
So an arbitrarily bogus lookup survives.

Fixing this means bounding realized instance counts below `p` inside `VmSat` — an audited-surface
change to `VmSpec.lean`, deliberately **not** made unilaterally. Note the single-circuit spec
never had to confront this: it assumes `BusSemantics.accepts` outright rather than deriving it
from balance, so the wraparound question never arises there. Deriving acceptance is strictly more
honest, and this is the bill for it.

`Host.absorbsStateless`, by contrast, does look dischargeable for `openVmHost` (not yet done):
`δ`'s side condition forces it onto stateless buses whose payloads `accepts` admits, which for
`defaultBusMap` means exactly the four lookup buses (an unknown bus id is stateless but `accepts`
is `False` there, so it is excluded); each lookup chip can absorb its own bus's slice by
appending one instance, since `lookupTableHostChip` constrains *which* payloads carry a nonzero
net, not what that net is, and is not `singleton`.

**Mechanical notes.** `Spec.lean`'s imports do not bring in `ring`/`linear_combination`, so this
file imports `Mathlib.Tactic.LinearCombination` (as `OptimizerPasses/DegenRange.lean` already
does). Reindexing `Fin G.length → Fin G'.length` uses `Fintype.sum_equiv (finCongr hlen.symm)`;
`(finCongr h) t = Fin.cast h t` holds by `rfl`, which keeps the `show` steps working.
The `Host` conditions have to be stated without a `Vm` in scope, so they quantify over a bare
`HostAssignment` (see the simplification-pass section below, which moved that vocabulary into
`VmSpec.lean`). All the theorems went into `Scripts/unused-theorems.txt`'s `[ignore]`, same
rationale as the `VmSpec.lean` entries.

## Reading the manuscript's `bus_int.tex` — what it settled, and one gap it has

Up to this point the Lean work had only used `vm.tex`. Reading `bus_int.tex` and `main.tex`
settled three open questions and turned up one problem in the manuscript itself.

**Settled — binary multiplicities.** `eq:legal:stateless:mult` is exactly the missing per-chip
assumption: `ConAlg ⟹ [⋀ᵢ (idᵢ ∈ IdStateless) ⟹ (mᵢ ∈ {0,+1})]`. Note it is conditioned on
`ConAlg` — the algebraic constraints *alone*. That matters: conditioning on `Circuit.satisfies`
would be circular, because `satisfies` bundles the `accepts` obligation being derived.

**Settled — the vocabulary map.** `ConAlg` = `VmAssignment.satisfiesGuest`;
`ConAlgPlus` (= `ConAlg` + `eq:stateless_as_pred`) = `Circuit.satisfies`. `Host.forcesAccepts` is
the arrow between them, i.e. the manuscript's stateless induction.

**Settled — `absorbsStateless` was never a gap.** The manuscript already says a table sink "can
balance *any* legal interactions with its bus… It is only on B that equivalence must hold during
optimization." That is the justification for `Circuit.sideEffects` being stateful-only, and
`Host.absorbsStateless` is its formal counterpart. The earlier framing of this as an impedance
mismatch was wrong; it is deliberate architecture.

**Gap found — the stateless induction wraps.** The manuscript argues with `mᵢ > 0` / `mᵢ < 0`,
and `main.tex` says inequalities use "the canonical embedding in ℤ". But balancing is an equation
in `ZMod p`. Each multiplicity being `0`/`1` in ℤ does not make the *sum over instances* an
ℤ-sum: `p` instances sending the same bogus payload total `0` in the field and `p` in ℤ, so no
sink is obliged to receive it and `eq:stateless_as_pred` fails. The manuscript needs a side
condition bounding the number of active stateless interactions below `p`. Invisible in prose that
reasons about integers; unavoidable once the sum is literally `∑` in `ZMod p`.

## `VmSat` gained a trace budget; `forcesAccepts` is now proved

Acting on the above.

**Audited surface (`VmSpec.lean`).** `Host` gained `maxInstances : ℕ`, and `VmSat` a fourth
conjunct `VmAssignment.withinBudget`: `(∑ t, (a.guestAssignments t).length) ≤ host.maxInstances`.

Two design points, both load-bearing:
- The bound *must* live in `VmSat`, not in a theorem hypothesis. `CanEffect` existentially
  quantifies the witness, so a theorem is handed an arbitrary one; a bound stated outside has
  nothing to attach to.
- It bounds **instances**, not instances × bus-interactions. The tempting single-line version
  (`∑ t, instances t * (G.get t).busInteractions.length < p` in `VmSat`) does not survive the
  soundness transfer: you would hold it for `G'` and need it for `G`, and nothing obliges the
  optimizer to *reduce* interaction counts. Keeping the budget on the shared `Host` makes it
  identical on both sides, and instance counts are preserved exactly by the soundness
  construction (the new lists are `map`s). The instances × interactions arithmetic moves to the
  connecting theorem, where both `G` and `G'` are in scope: `L * host.maxInstances < p` with
  `∀ t, (G.get t).busInteractions.length ≤ L`.

**Per-chip well-formedness (`VmSpecConnection.lean`).** `Circuit.legalGuest` bundles
`statelessSendOnly` (the manuscript's `eq:legal:stateless:mult`) and `statefulAccepts`. Both are
conditioned on the algebraic constraints alone. Required of `G'`, not just `G` — soundness starts
from the *optimized* VM's assignment, so that is where `forcesAccepts` gets applied; and `G'` is
what actually runs, so OpenVM would reject a multiplicity-2 lookup from it anyway.

`statefulAccepts` is assumed, standing in for the manuscript's `eq:legal:recv_byte`, which needs
its own balancing argument (only bytes are received because only bytes are sent). Not attempted.

**The counting chain.** `Circuit.multsAt` (the list `allEffects` sums) → `Circuit.countAt`
(`countP` of its nonzeros) → `guestCount` (the ℕ-valued analogue of `guestNet`). Then
`allEffects_eq_countAt` (a `0`/`1` list sums to its count of nonzeros — note the `cons` case
needs a split on `(1 : ZMod p) = 0`, true in `ZMod 1`), `guestCount_le`, and
`guestNet_ne_zero_of_active`: an active stateless message leaves a genuinely nonzero guest net.

**`Host.forcesAccepts` is derived, not assumed.** It was replaced as an *assumption* by the much
weaker `Host.sinksAreTables` ("any stateless message a host chip leaves nonzero is accepted" — no
mention of guests), and `forcesAccepts_of_sinksAreTables` supplies the balancing argument. This is
`bus_int.tex`'s stateless induction, formalized.

## Discharged for `openVmHost`

`ApcOptimizer/VmSpecOpenVmConnection.lean` (new) proves `openVmHost_sinksAreTables` and hence
`openVmHost_forcesAccepts`. The condition that was **false** two sections ago is now a theorem.

The proof is a `fin_cases` over the eight host chips: the four lookup chips restate their bus's
case of `OpenVM.accepts` (after `rcases`-ing the payload to the right arity, both sides are
literally the same proposition — `exact id` closes each), and the four memory-bus chips pin
`m.1 = memBusId`, which contradicts `isStateful m.1 = false`. For the output/input chips that
needs `exists_of_busStateOf_ne_zero` plus the fact that every interaction of an
`OutputRead`/`InputRead` sits on the memory bus.

**Still open: `Host.absorbsStateless` for `openVmHost`.** It looks true and the shape is clear —
append to each of the four lookup chips one instance carrying `δ` restricted to that chip's bus
(they are not `singleton`, so appending is free; their legality predicate constrains *which*
payloads may carry a nonzero net, not what it is). Two pieces of work: showing `δ`'s support lies
in `{2,3,6,7}` (from `isStateful m.1 = false` plus `∃ mult ≠ 0, accepts …`, since an unknown bus
id is stateless but `accepts` is `False` there — needs inverting `defaultBusMap`, i.e. an 8-deep
`rcases` on the bus id), and computing `hostNet` across the modified eight-chip assignment.

## The guest-chip list is a set

`VmSpec.lean` gained `vmEquivalent_of_mem`: two guest-chip lists whose elements form the same
set (`{c | c ∈ G} = {c | c ∈ G'}` as a `Set (Circuit p)` — no `List → Set` coercion or
`List.toSet` is in scope, and `List.toFinset` would need a `DecidableEq (Circuit p)` that
`Expression` does not derive) are `VmEquivalent`. Order and repetition are both unobservable, so the `List` is only ever used as a
set. `vmEquivalent_of_perm` is the permutation corollary.

Everything rests on one asymmetric lemma, `canProduce_of_subset`: if every chip of `G'` also
occurs in `G`, then `G` can produce every effect `G'` can. Since "same elements" is symmetric,
applying it both ways gives the iff — no separate dedup and reorder arguments.

The construction picks, for each chip type of `G'`, a home in `G` carrying the same circuit
(`choose φ hφ` off `List.mem_iff_get`), then pools the instances of everything mapped to one home
into that home's list, via `(List.ofFn fun t => if φ t = s then … else []).flatten`. Pooling is
invisible to `VmSat`: the balance sums regroup by fibre (`sum_fiber`, a `Finset.sum_comm` plus
`Finset.sum_ite_eq`), the algebraic constraints are per-instance and both homes carry the same
circuit, and `withinBudget` survives because pooling moves instances without creating any — which
is another payoff from bounding *instances* rather than instances × interactions.

Note this subsumes both directions of set-ness at once: `φ` is not required to be injective
(that's what lets two copies of a chip merge) nor surjective (that's what lets `G` carry extra
chip types, which simply get an empty instance list).

Needed `import Mathlib.Algebra.BigOperators.Fin` in `VmSpec.lean` for `List.sum_ofFn`.

## Auditing the soundness theorem's hypotheses — one was wrong

Review of `canProduce_of_isSoundReplacementOf`'s hypotheses, and what came of each.

**`hAccepts` was already discharged** for OpenVM. Kept, but the theorem now takes the more
primitive `Host.sinksAreTables` and derives `forcesAccepts` internally, so the signature shows the
condition that actually has to be checked.

**`hAbsorbs` is necessary, not eliminable.** Counterexample: a host with no lookup sinks. Let `G`
contain a chip with a range check and `G'` be the same chip without it — legal under
`isSoundReplacementOf`, since `sideEffects` is stateful-only. `G'` has satisfying assignments but
`G`'s range-check message has nothing to balance against, so `CanProduce ⟨host, G⟩` is empty and
the theorem is false without it.

**`hLegal'` split into a legitimate half and a wrong one.**

`statelessSendOnly` is fine — the manuscript's `eq:legal:stateless:mult`, of the acceptable
"algebraic constraints imply X" shape, and not transportable across `isSoundReplacementOf`.

`statefulAccepts` was **false for realistic chips**. OpenVM's memory `accepts` constrains
*receives* (a received byte-checked word must be byte-valued), and a chip that reads memory does
not constrain the value it finds there. Assuming it per-chip would have made the theorem vacuous
on real input. It is exactly why the manuscript *derives* `eq:legal:recv_byte` from balancing.

### What replaced it

Per chip, both of the accepted shape: `Circuit.statefulPolarity` (stateful multiplicities are
`0`/`±1`, `eq:legal:stateful:mult`) and `Circuit.statefulSendsMaintain` (what a chip *sends*
maintains the bus invariants, `eq:legal:stateful:send_byte`). The receive side is now **derived**
(`maintains_of_stateful_active`): if nothing carrying a payload maintained the invariants then no
guest sent it and no host chip touched it, leaving a pile of receives that cannot balance. Same
shape as the stateless induction, with `v = -1` instead of `v = 1` — so the counting machinery was
generalized from "sums of `0`/`1`" to "sums of `0`/`v`" (`sum_eq_countP_mul`,
`guestNet_ne_zero_of_uniform`), and the trace budget is what rules out `p` receives summing away.

Linking the two is `BusSemantics.statefulAcceptsOfMaintains` — acceptance on a stateful bus
depends only on the payload and follows from the invariants any carrier of it maintains. Proved
for `openVmBusSemantics`.

## Legality moved onto the `Host`

`Host` gained a `legalGuest : Circuit p → Prop` field and `VmSat` a `Vm.guestsLegal` conjunct.
The predicates themselves live in their own file, `ApcOptimizer/VmSpecLegal.lean`, because both
`VmSpecOpenVm.lean` (which instantiates the field) and `VmSpecConnection.lean` (which consumes
them) need them.

The payoff is not cosmetic: soundness now needs legality only of the chips the optimizer was
**given**. A run of the optimized chips already witnesses their own legality through `VmSat`, so
`hLegal' : ∀ t, (G'.get t).legalGuest bs` — an assumption about the optimizer's *output* — is
gone. An optimizer that emits an illegal chip makes `CanProduce` empty for its output, which
`VmCompleteReplacement` reports as a failure instead of assuming it away.

## `VmEquivalent` split

`VmSoundReplacement` (the optimized chips can produce nothing new) and `VmCompleteReplacement`
(they lose nothing), with `VmEquivalent` their conjunction and `vmEquivalent_iff` recovering the
old `↔` form.

## OpenVM-specific soundness

`openVm_canProduce_of_isSoundReplacementOf` states soundness for `openVmHost` with every host-side
condition discharged except two: `Host.statefulChipsMaintain` and `Host.absorbsStateless`. Also
proved along the way: `openVmBusSemantics_statefulAcceptsOfMaintains`, and
`openVmHost_legalGuest_unpack` (which is `id`, since the field is *defined* as
`Circuit.legalGuest`).

To make `statefulChipsMaintain` provable the host chips were strengthened: memory finalization and
the input chip's old-word reads now require byte-valued data, and `OutputRead`/`InputRead` carry
byte constraints. That is the manuscript's `eq:legal:recv_byte` asserted of the host's own fixed
furniture — inspectable once, and not an assumption about anything the optimizer produces.
`InputRead` additionally asks `ptr`/`count` to be bytes, which is *not* faithful: this draft
stores a whole word in one limb, where real OpenVM spreads a 32-bit register over four byte
limbs. Modelling that properly would remove the constraint.

## Simplification pass — algebraic satisfiability, and a named assignment vocabulary

Four duplications were collapsed; nothing about what is proved changed.

**`Circuit.satisfiesAlgebraic`** (`Spec.lean`) is the algebraic half of `Circuit.satisfies`, now
factored out of it. The predicate `∀ c ∈ algebraicConstraints, c.eval asg = 0` was written out
five times — once in `Circuit.satisfies`, once in `VmAssignment.satisfiesGuest`, and once in each
of the three legality clauses. Putting it in `Spec.lean` rather than `VmSpec.lean` is what makes
the two vocabularies literally the same predicate instead of two defeq ones. It cost exactly one
edit in the implementation tree: `OptimizerPasses/Bridge.lean`'s `decodeCS_satisfies` needed
`Circuit.satisfiesAlgebraic` added to a `simp only` list.

**`GuestAssignment` / `HostAssignment`** (`VmSpec.lean`) name the two halves of a `VmAssignment`,
with `.net`, `.satisfiesAlgebraic`/`.legal`, and `.instanceCount` on them. `VmSpecConnection.lean`
had been restating `HostLegal`/`hostNet`/`guestNet` locally, because the `Host` conditions must be
stated without a `Vm` in scope; now they use the real definitions, and the defeq bridges
(`hostLegal_of_satisfiesHost`) are gone. `VmAssignment.satisfiesGuest`/`satisfiesHost`/
`withinBudget` became one-line projections.

**`Circuit.algebraicallyForces`** (`VmSpecLegal.lean`) is the shape every legality clause shares:
"the chip's algebraic constraints force `P` on every message it writes to a bus of this
statefulness". The three clauses are now one-liners differing only in the statefulness bit and
`P`, which is exactly what an auditor wants to compare.

**`exists_instance_of_sum_ne_zero`** replaces the two identical `exists_instance_of_*Net_ne_zero`
proofs, which now derive from it in one line each.

**`Host.realizes bs`** (`VmSpecConnection.lean`) bundles the five host-side hypotheses —
`legalGuest` unpacking, `sinksAreTables`, `statefulChipsMaintain`, `statefulAcceptsOfMaintains`,
`absorbsStateless` — into one structure. They all say the same kind of thing: `Spec.lean` treats
`accepts`/`maintainsInvariants` as opaque per-message predicates, and these are what makes a
concrete VM's chips implement them. Since no field mentions a guest circuit, `Host.realizes` is
checkable once per VM and reusable across every optimizer run, which is what
`openVmHost_realizes` does: it discharges three of the five for `openVmHost` and takes the other
two as arguments, leaving `openVm_vmSoundReplacement_of_isSoundReplacementOf` a one-liner.

The internal lemmas (`maintains_of_stateful_active`, `forcesAccepts_of_hostSound`) deliberately
still take the individual fields rather than the bundle, so which condition carries which step of
the argument stays visible in their signatures.

## Both `openVmHost` conditions discharged — the OpenVM soundness theorem is VM-assumption-free

`openVmHost_statefulChipsMaintain` and `openVmHost_absorbsStateless` are proved, so
`openVmHost_realizes` now takes no arguments and
`openVm_vmSoundReplacement_of_isSoundReplacementOf` assumes **nothing about the VM** — only about
the optimization (`hlen`, `hLegal` on the input chips, `hSize'`/`hBudget`, `hSound`).

**`statefulChipsMaintain`** is the eight-way split that was predicted. The four lookup chips pin
their bus id to a stateless bus, so they cannot touch a stateful message at all — vacuous. The
four memory chips each supply a witness through `memory_maintains` (multiplicity `1` satisfies the
polarity clause; the byte clause is the hypothesis), and the byte facts come from the predicates
`VmSpecOpenVm.lean` states: all-zero words for initialization, the chip's own byte requirement for
finalization, and `OutputRead.interactions_data`/`InputRead.interactions_data` for the pinned
input/output witnesses. The one wrinkle: `InputRead`'s old-word payload is
`[2, ptr+i] ++ old.toList ++ [0]`, and `memoryPayload?` will not reduce until `old.toList` is a
syntactic cons chain, so the proof destructures the 4-vector by length first.

**`absorbsStateless`** goes as sketched. `defaultBusMap_stateless` inverts the bus map — a legal
`δ` is stateless *and* `accepts`-supported, and `accepts` is `False` on an unknown bus, so `δ`'s
support lands in `{2,3,6,7}`. Each lookup chip then absorbs its own slice,
`fun m => if m.1 = b then δ m else 0`, in one appended instance: legal because the chip's
predicate is exactly `OpenVM.accepts`'s case for that bus (the same equivalence
`openVmHost_sinksAreTables` uses, read in the other direction) and because no lookup chip is
`HostChip.singleton`. The net works out because the four bus ids are distinct, so at a message
with `δ m ≠ 0` exactly one indicator fires. Memory, input and output chips are untouched, which is
what makes the input/output preservation clauses `rfl`.

## Registers are four byte limbs now — the last unfaithful constraint is gone

`InputRead` used to store a whole register in one limb and ask `isByte` of it, which conflated a
32-bit register with a byte and silently capped an input chunk at 255 words. Fixed on the audited
surface (`VmSpecOpenVm.lean`):

* new `wordValue : Vector (ZMod p) 4 → ZMod p`, little-endian base-256 — how OpenVM spreads a
  32-bit value across `MemoryPayload.data`;
* `InputRead.ptr`/`count : ZMod p` became `ptrLimbs`/`countLimbs : Vector (ZMod p) 4`, with
  `InputRead.ptr`/`InputRead.count` now *derived* as `wordValue` of the limbs, so every use site
  reads the same;
* `ptrIsByte`/`countIsByte` (the unfaithful pair) became `ptrLimbsAreBytes`/`countLimbsAreBytes`,
  which is the ordinary memory-word discipline every other access already carries;
* `InputRead.interactions` peeks `[1, reg] ++ limbs.toList ++ [0]` instead of putting the whole
  value in the low limb.

`bytesLen`/`oldWordsLen` are now against `(wordValue countLimbs).val`, so a chunk may be up to
`2^32-1` words rather than 255.

On the connection side this made the register payloads the same shape as the overwritten-cell
payloads, so `memoryPayload?_word` (the data limbs of `[as, ptr] ++ w.toList ++ [ts]` are exactly
`w`'s entries) now covers all three, and `InputRead.interactions_data` shrank accordingly.

Still a modelling choice, not a distortion: a *datum* (an input byte, an output word) occupies one
word's low limb with the rest zeroed, rather than four data being packed per word. And
`OutputRead.wordsAreBytes` is unchanged — AS 3 is not byte-checked by `maintainsInvariants`, so
that field is a deliberate restriction of this draft's output model, not something OpenVM forces.

## Split into a folder; one substitution at a time

Two structural changes, both user-requested.

**Folder.** The five `VmSpec*.lean` files became the eight-file `ApcOptimizer/VmSpec/` above. Two
splits were more than filing: the spec-validation theorems came out of `VmSpec.lean` into
`Validation.lean`, leaving `Basic.lean` as definitions only; and the old `VmSpecConnection.lean`
(574 lines) split three ways along its actual seams — counting/anti-wraparound, what a host must
be, and the replacement argument itself.

**One substitution at a time.** The old `vmSoundReplacement_of_isSoundReplacementOf` replaced the
whole list in one go, with `Fin.cast`/`Fintype.sum_equiv` reindexing throughout. Now:

* `vmSoundReplacement_cons` — replace the *head* chip, leave the rest of the VM alone. Sums split
  by `Fin.sum_univ_succ` (`guestNet_cons`, `guestInstanceCount_cons`), and the tail terms are
  literally unchanged, so the reindexing is gone.
* `vmSoundReplacement_append` — the induction. `S` accumulates the chips already replaced, rotated
  to the *back* of the list, so the next chip to replace is always at the head:
  `VmSoundReplacement host (T ++ S) (S ++ T')`, peeling `T = c :: U`. One `vmSoundReplacement_cons`
  step, one rotation, recurse. This is where `Validation.lean`'s "the guest-chip list is a set"
  becomes load-bearing rather than decorative — the rotation is free precisely because of it, via
  `VmSoundReplacement.of_perm`, and `VmSoundReplacement.trans` chains the steps.
* `vmSoundReplacement_of_forall₂` — the headline, now stated with
  `List.Forall₂ (fun c c' => c'.isSoundReplacementOf c bs) G G'` instead of a length equation plus
  an index cast.

**One hypothesis got stronger, deliberately.** The old theorem needed the interaction-count bound
`L` only on `G'`, because `Host.forcesAccepts` was applied once, to the optimized list. The
intermediate lists of the induction mix chips from both, so the bound is now
`∀ c ∈ G ++ G', c.busInteractions.length ≤ L`. In practice this is *weaker* to check: the optimizer
only removes interactions, so bounding the input bounds the output. But it is a real change to the
statement.

`Host.forcesAccepts`, `maintains_of_stateful_active` and `guestCount_le`/`guestNet_ne_zero_of_uniform`
took the size bound as `∀ t : Fin G.length, (G.get t)…`; they now take `∀ c ∈ G, …` throughout.

**Not done: moving `Spec.lean` out of the audited surface.** The suggestion was that the chip-level
spec and the bus semantics no longer need auditing. Not yet, and the criterion is precise: there is
still no theorem connecting `openVmOptimizer` to `VmSoundReplacement`, so `refines` /
`isSoundReplacementOf` remain the statement an auditor actually reads. Once such a theorem exists,
`refines`, `isSoundReplacementOf`, `isCompleteReplacementOf`, `admissible` and `guaranteesInvariants`
do become internal — but `OpenVmSemantics.lean` does *not*, because `openVmBusSemantics` still
appears in the VM-level statement itself, inside `openVmHost`'s chip predicates and inside the
`legalGuest` hypothesis on the input. So the eventual split of `Spec.lean` is datatypes (audited)
vs. the chip-level relation (internal), not "all of it becomes internal".

## AUDIT: `Circuit.legalGuest` is too strong for OpenVM

Checked the three legality clauses against OpenVM and against a real powdr export
(`Benchmarks/OpenVM/openvm-eth/apc_001_pc0x4ecc54.json.gz`).

**Clauses 1 and 2 hold, and are genuinely algebraically forced.** In the export the lookup and
memory multiplicities are `is_valid`-style sums of opcode flags, and the export carries both
`opcode_add_flag*(opcode_add_flag-1)` and `(Σ flags)*((Σ flags)-1)` as algebraic constraints. So
`statelessSendOnly` (0/1 on lookups) and `statefulPolarity` (0/±1 on memory and the execution
bridge) are met by `Circuit.satisfiesAlgebraic` alone, as the definition demands.

**Clause 3, `statefulSendsMaintain`, is false.** Every OpenVM memory access is a *read-echo*:
receive `[as, ptr, d₀..d₃, prev_ts]` with multiplicity `-1`, then send `[as, ptr, d₀..d₃, ts]` with
multiplicity `+1` — the *same* data limbs. For a write the sent limbs are new and range-checked;
for a read they are whatever was in memory, and the chip constrains them not at all. But
`statefulSendsMaintain` demands `maintainsInvariants` — hence byte-valued limbs — of every memory
message with multiplicity `1`, from the algebraic constraints alone.

Measured on the export: of 11 memory sends, **2 carry data limbs that appear in no lookup anywhere
in the circuit** (`a__*_3`, `b__*_3` — a register read echoed straight back). Their byte-ness is
inherited from whoever wrote the register, and nothing in the circuit re-establishes it.

Consequence: `openVmHost` rejects realistic guest chips, `CanProduce` is empty for them, and
`openVm_vmSoundReplacement` is vacuously true where it matters.

**Why the obvious fix is not enough.** The natural repair is to let `algebraicallyForces` also
assume the chip's *stateless* interactions are accepted — non-circular, because
`forcesAccepts_of_hostSound`'s stateless branch uses only `sendOnly` + `sinksAreTables` + balance
and never touches the stateful clauses, so stateless acceptance can be derived first. That fixes
the *computed*-write case (an ALU output is byte-checked by `bitwise_lookup`). It does **not** fix
the read-echo, which has no stateless interaction at all.

Conditioning on the chip's own stateful *receives* would make the clause true, but that is exactly
what `maintains_of_stateful_active` is trying to derive — genuinely circular. And balancing alone
cannot break the cycle: two chips can each receive a non-byte word and send another one, balancing
perfectly. What rules that out in reality is the strictly increasing timestamp, which order-blind
`VmSat` does not see. So the byte invariant is not derivable here; it has to be assumed, in the
same shape the README already assumes it chip-level ("every memory writer in the deployed system is
byte-range-checked").

Recorded as machine-checked Lean in `ApcOptimizer/VmSpec/OpenVmLegalAudit.lean`: `readEchoChip`
(one memory access, no algebraic constraints, no lookups) satisfies clauses 1 and 2, fails clause 3
(`readEchoChip_not_statefulSendsMaintain`, for any `p > 256`), and hence makes the whole VM produce
nothing (`not_canProduce_of_readEcho`).

**Two smaller findings.**

* The real export's bus map is *not* `defaultBusMap`: `TupleRangeChecker` sits at bus **10** with
  sizes `[256, 8192]`, not bus 7 with `[256, 2048]`. `openVmHost` is hard-wired to `defaultBusMap`,
  and `openVmHost_absorbsStateless` depends on `defaultBusMap_stateless` pinning the stateless ids
  to `{2,3,6,7}`. The chip-level optimizer is parameterized by the parsed bus map, so only the
  VM-level draft is affected — but it should be parameterized too.
* `memoryPayload?` matches any payload of length **≥ 6** (`_timestamp` binds the tail). A memory
  access with a block size other than 4 either parses with the wrong limbs or, at length < 6,
  returns `none` and makes the byte clause vacuous. Fine for RV32 APCs (block size is always 4);
  a gap if a guest ever touches the native address space.

## New validation theorems

In `Validation.lean`: `VmEquivalent` is an equivalence relation (`refl`/`symm`/`trans`);
`vmCompleteReplacement_iff` (completeness is soundness the other way round); and the pair that
frames the audit finding —

* `not_canProduce_of_illegal`: a guest list containing an illegal chip produces *nothing*. This is
  what makes checking legality inside `VmSat` safe rather than assuming it.
* `canProduce_idle`: **the spec is not vacuous.** Any VM whose singleton host chips can sit idle
  has at least the empty run, so `VmSoundReplacement` is not holding for free. Without it, the
  audit finding above would be indistinguishable from a spec that is simply empty.

## Degree bounds at VM level

`Host` gained a `degreeBound : DegreeBound` field, sitting next to `maxInstances` — both are
capacity limits of the proving backend, not of any one chip. `VmSat` gained a matching conjunct,
`Vm.guestsWithinDegree` (`∀ c ∈ guestChips, c.withinDegree host.degreeBound`), placed alongside
`Vm.guestsLegal` and for the same reason: a chip the backend cannot prove has no runs, so it
belongs in the definition of a run rather than in a hypothesis.

That placement is the payoff. `Spec.lean` has to bolt `optimizerRespectsDegreeBound` onto
`Optimizer.isCorrect` as a separate conjunct, because a single `Circuit`'s `refines` has no notion
of the circuit being *runnable*. At VM level it is a consequence —
`guestsWithinDegree_of_vmCompleteReplacement`: if `G'` is a complete replacement for `G` and `G`
can produce anything at all, then `G'` is within the bound. `canProduce_idle` supplies the "can
produce anything at all". No extra conjunct on the optimizer.

Threading: one new hypothesis (`c.withinDegree host.degreeBound` for the chip being *restored*) on
`vmSoundReplacement_cons`, and its `∀ c ∈ G` form on `vmSoundReplacement_append`,
`vmSoundReplacement_of_forall₂`, `openVm_vmSoundReplacement`, `canProduce_of_subset` and
`canProduce_idle` — exactly parallel to the existing legality hypothesis, and required only of the
optimizer's *input*. `openVmHost` uses OpenVM's `defaultDegreeBound`. New in `Validation.lean`:
`guestsWithinDegree_of_canProduce` and `not_canProduce_of_overDegree`.

Note the `VmSat` conjunct chain got one longer: the last component is now
`guestsLegal ∧ guestsWithinDegree`, so `hsat.2.2.2.2` became `hsat.2.2.2.2.1`.

## The legalGuest fix, phase 1: a rank on stateful state

`Host` gained `statefulRank : BusMessage p → ℕ` (for OpenVM, `openVmRank` = the memory record's
timestamp, `0` off the memory bus), and `Circuit.statefulSendsMaintain` gained a hypothesis:

> a stateful **send** maintains the invariants, provided everything the same instance touches at a
> strictly lower rank already does (`Circuit.lowerRanksMaintain`).

`maintains_of_stateful_active` is now a strong induction on that rank, which is what makes the
whole thing work: balance alone provably cannot establish the byte invariant, since two chips can
each receive a bad word and send another one, cancelling exactly. The rank kills that — one of the
two would have to send below the rank it received at.

Rank is a **natural number**, deliberately. `<` on `ℕ` is well-founded, so the induction has
something to descend on, and all the wrap-sensitivity of "the timestamp went up" lands in the
per-chip check of the legality clause rather than in the spec.

`OpenVmLegalAudit.lean` flipped from a negative result to a mixed one:

* `readEchoChip_legalGuest` — the read-echo shape is legal **when `t₀.val < t₁.val`**.
* `readEchoChip_not_legalGuest_of_stale` — and illegal when it isn't. The timestamp condition is
  load-bearing, not decoration.
* `freshWriteChip_not_legalGuest` — a value justified by a bitwise-lookup range check is *still*
  rejected. This is the marker for phase 2.

## Phase 2: lookups, and legalGuest is now true of OpenVM

`Circuit.statefulSendsMaintain` gained its second hypothesis, `Circuit.statelessAccepted` — the
chip's own lookups hold. `statelessAccepted_of_sinks` (`Realizes.lean`) derives it for every guest
instance from `Circuit.statelessSendOnly`, `Host.sinksAreTables`, balance and the trace budget,
with no stateful clause taking part, so there is no circularity. It is the manuscript's stateless
`bus_int.tex` induction, now factored out of `forcesAccepts_of_hostSound` and reused in
`maintains_of_stateful_active` (which gained `hsinks`).

The two hypotheses match the two shapes an OpenVM memory send has, and the audit file checks both:

* `readEchoChip_legalGuest` — the echo, carried by the rank hypothesis, legal iff `t₀.val < t₁.val`
  (at this stage that inequality was a hypothesis; phase 3 derives it).
* `freshWriteChip_legalGuest` — the computed write, carried by the lookup hypothesis. It has no
  stateful traffic below its send's rank at all.

So the finding that opened this thread is discharged: `Circuit.legalGuest` now holds of the shapes
real OpenVM circuits have, and the memory byte invariant is *derived*, not assumed.

Phase 2 cost exactly what phase 1 predicted — one new lemma, one extra hypothesis on
`maintains_of_stateful_active`, one line at the `sendsMaintain` application site. Weakening a
definition that appears only *negatively* invalidated nothing.

## Phase 3: what OpenVM actually checks about timestamps

The read-echo's `t₀.val < t₁.val` was a hypothesis, and the question was whether a real chip can
discharge it. **It cannot, as stated.** Reading `openvm/crates/circuits/primitives/src/
assert_less_than/mod.rs` and `crates/vm/src/system/memory/offline_checker/bridge.rs`:

`MemoryOfflineChecker::eval_timestamps` attaches an `AssertLtSubAir` to every memory access, with
`max_bits = MemoryConfig::timestamp_max_bits` (default and hard cap `29`). That sub-AIR does *not*
constrain `prev_timestamp < timestamp`. It constrains

```
enabled * (timestamp - prev_timestamp - 1) = enabled * (lo + 2^17 * hi)
```

with `lo`, `hi` range-checked to 17 and 12 bits on the variable range checker. So all a chip
forces is that the *difference* is small. OpenVM's own comment states the missing premise:

> Soundness requirement: max_bits <= 29. max_bits > 29 doesn't work: the approach is to check that
> y-x-1 is non-negative. For a field with prime modular, this is equivalent to checking that
> y-x-1 is in the range [0, 2^max_bits - 1]. However, for max_bits > 29, if y is small enough and
> x is large enough, then y-x-1 is negative but can still be in the range due to the field size
> not being big enough.

i.e. bounded difference orders the two timestamps only while both are already below `2^max_bits`.
That premise is global — OpenVM documents it on `MemoryConfig` ("all timestamps must be in the
range `[0, 2^timestamp_max_bits)`") and enforces it with the connector chip, which range-checks a
segment's final timestamp. No single chip can establish it.

### What changed

* **`Host.rankBound : ℕ`**, alongside `maxInstances` and `degreeBound` — the VM's rank window.
  `openVmRankBound = 2 ^ openVmTimestampBits = 2 ^ 29`.
* **`VmAssignment.withinRankBound`**, a new `VmSat` conjunct: every guest instance's traffic
  satisfies `Circuit.ranksBounded`.
* **`Circuit.ranksBounded`** is stated on `Circuit.allEffects` under a `rank m ≠ 0` guard, *not*
  per bus interaction. That is what makes it survive an optimization: `isSoundReplacementOf`
  preserves `Circuit.sideEffects`, which agrees with `allEffects` on exactly the stateful buses,
  and `Host.realizes.rankStateless` (a new field) says a rank sees no other bus. A per-interaction
  version would not transfer — two interactions can cancel.
* **`Circuit.statefulSendsMaintain` gained `ranksBounded` as a third hypothesis**, so
  `Circuit.legalGuest` now takes a `rankBound` too.
* **`VmSat` is now a structure** (7 fields), since `.2.2.2.2.2`-style projections do not survive
  adding a conjunct. Field names match the definitions: `satisfiesGuest`, `satisfiesHost`,
  `balances`, `withinBudget`, `withinRankBound`, `guestsLegal`, `guestsWithinDegree`.

### What the audit file now proves

`readEchoChip` carries the real gadget — `assertLtLoLookup` (17 bits), `assertLtHiLookup`
(12 bits), and `assertLtConstraint` (`t₁ - t₀ - 1 = lo + 2^17 * hi`) — and
`readEchoChip_timestamps_increase` *derives* `t₀.val < t₁.val` from: the two range checks (via
`statelessAccepted`), the constraint (via `satisfiesAlgebraic`), and `t₀.val < 2^29` (via
`ranksBounded`). All three of `statefulSendsMaintain`'s hypotheses are consumed, each for a
different reason. `readEchoChip_legalGuest` is now unconditional, on `hp : 2 ^ 30 < p` — the
arithmetic needs `t₀.val + 1 + lo.val + 2^17 * hi.val < p`, and that sum is `< 2^30`, which is
exactly why 29 is OpenVM's cap for a 31-bit field.

The degenerate case is handled without the rank bound: if `t₀ = t₁` the receive and send cancel,
so `ranksBounded` says nothing — but then the constraint reads `-1 = lo + 2^17 * hi`, and
`(-1).val = p - 1 > 2^29` contradicts the limb bounds directly.

`staleEchoChip_not_legalGuest` replaces the old `readEchoChip_not_legalGuest_of_stale`: strip the
gadget out, echo the word back at the timestamp it was found at, and the chip is rejected. So the
gadget is load-bearing, not decorative.

### The remaining assumption, stated plainly

`VmAssignment.withinRankBound` is an assumption about the *run*, discharged in reality by OpenVM's
connector chip, which this spec does not model. It sits next to `VmAssignment.withinBudget`, which
has the same character (a "nothing wraps `ZMod p`" condition the VM's configuration guarantees).
Modelling the connector — and the execution-bridge chain that propagates its bound backwards —
would discharge it, and is the natural successor to this work.

## Phase 4: `VmSat` is now only about runs

**User's criterion:** `VmSat` should hold of exactly what would pass OpenVM's actual constraints.
`Vm.guestsLegal` failed it — `Circuit.legalGuest` quantifies over all assignments of a circuit,
which no AIR evaluates, so a real OpenVM run *can* violate it. Folding it into satisfaction
silently dropped those runs from `CanProduce`, which is a soundness hole in the modelling: the
theorem said nothing about the very runs an illegal optimizer output would produce.
`Vm.guestsWithinDegree` went with it — a degree bound is a setup-time property of a circuit, not
of a run.

`VmSat` is now five fields, all properties of the assignment: `satisfiesGuest`, `satisfiesHost`,
`balances`, `withinBudget`, `withinRankBound`.

### Where the two requirements went

Both became preservation obligations in `Basic.lean`, stated separately from the Sat semantics:

```lean
def PreservesLegality (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  (∀ c ∈ guestChips, host.legalGuest c) → ∀ c ∈ guestChips', host.legalGuest c

def PreservesDegree (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  (∀ c ∈ guestChips, c.withinDegree host.degreeBound) →
    ∀ c ∈ guestChips', c.withinDegree host.degreeBound
```

`PreservesDegree` is entirely decoupled — nothing in the equivalence proof consumes it.

`PreservesLegality` is *not* decoupled, and this is the one thing the change forces into the open:
`Host.forcesAccepts` runs its balancing argument over the list the VM is actually executing, which
for a sound replacement is the **optimized** one. So legality of `G'` is genuinely needed, and
`vmSoundReplacement_of_forall₂` now takes `hLegal` on `G` *plus* `hPreserve`. Previously that need
was met by `VmSat` — i.e. assumed away.

### Consequences

* `Host.forcesAccepts` gained a `∀ c ∈ G, host.legalGuest c` premise; `statelessAccepted_of_sinks`
  and `maintains_of_stateful_active` take it as `hGuests` instead of reading `hsat.guestsLegal`.
* `vmSoundReplacement_cons` no longer asks anything of `c` — not legality, not degree. `VmSat`
  carries no circuit-level property, so the restored run has nothing to re-establish.
* `vmSoundReplacement_append` threads legality exactly like `hSize`: on `T ++ T'` and on `S`.
* Deleted: `guestsLegal_of_canProduce`, `guestsWithinDegree_of_canProduce`,
  `not_canProduce_of_illegal`, `not_canProduce_of_overDegree`, and
  `guestsWithinDegree_of_vmCompleteReplacement`. The last was the nicest casualty — "completeness
  implies the degree bound for free" was only true because the bound was in `VmSat`.
* `canProduce_of_subset` and `canProduce_idle` lost their legality/degree hypotheses.

## Phase 5: `withinRankBound` out too — the criterion is *directly checked*

The criterion is sharper than "true of every real run": `VmSat` may hold only what an OpenVM AIR
checks **directly**. `withinRankBound` fails that, and reading `VmConnectorAir::eval` settles it —
the connector's trace is two rows, `begin` (asserted `= 1`) and `end`, and it range-checks
`local.timestamp` on its own rows only. So OpenVM directly constrains *two* timestamps per
segment, plus, per memory access, only the bounded difference. Nothing constrains an intermediate
or per-record timestamp. "Every timestamp is in range" is a multi-chip consequence — exactly the
kind of thing this spec exists to derive.

`VmSat` is now four fields: `satisfiesGuest`, `satisfiesHost`, `balances`, `withinBudget`.

### Where it went

```lean
def Host.pinsRanks (host : Host p) : Prop :=
  ∀ (G : List (Circuit p)) (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a →
    a.withinRankBound
```

A claim about the *host*, sibling to `Host.forcesAccepts` — but where `forcesAccepts` is derived
from `Host.realizes`, this one is **assumed**. `Host.forcesAccepts` gained an `a.withinRankBound`
premise; `vmSoundReplacement_cons` and its callers thread `hPins`, and
`openVm_vmSoundReplacement` now carries it as a visible, undischarged hypothesis.

**It is not provable for `openVmHost` as it stands**: the host models neither the connector nor
the bridge terminator, and none of its eight chips constrains a timestamp — `memoryInitHostChip`
and `memoryFinalizeHostChip` impose no bound. So the OpenVM soundness theorem is, as of this
phase, conditional on a hypothesis this development cannot supply. That is strictly better than
before, when the same gap was hidden inside `VmSat` and invisible in every statement — but it is a
real debt, and it makes modelling the connector the next thing worth doing rather than a nicety.

### What the change bought back

Taking it out of `VmSat` deleted the machinery that existed only to carry it across a replacement:

* `Circuit.ranksBounded` is now **per bus interaction**, not `allEffects`-with-a-guard. The guard
  existed so the predicate would survive `Circuit.isSoundReplacementOf`, which preserves only
  `sideEffects`; with `withinRankBound` out of `VmSat` there is nothing to transfer.
* `Host.realizes.rankStateless` — deleted, along with `openVmHost_rankStateless`. It existed only
  to make that transfer go through.
* The `hranks` block in `vmSoundReplacement_cons` — deleted.
* `readEchoChip_allEffects_recv` and the `t₀ = t₁` case split in
  `readEchoChip_timestamps_increase` — deleted. With a per-interaction bound the receive's
  timestamp is in range because the chip actively receives at it, full stop.

## Phase 6: `Host.pinsRanks` discharged — walking the execution bridge

`openVmHost_pinsRanks` (`Implementation/OpenVmChain.lean`) is proved. The one thing it needs beyond
what the VM already supplies is an arithmetic budget, which replaced `hPins` in
`openVm_vmSoundReplacement`:

```lean
(hWindow : (maxInstances + 1) * (window + 1) < p)
```

That is exactly the sanctioned kind of assumption: a bound on instance counts depending on the
window. It says a run of at most `maxInstances` instructions, each advancing the clock by less than
`window`, cannot wrap `ZMod p`.

### The argument

`Implementation/Chain.lean` states it with no mention of a circuit, a bus or a host. A
`VmChain.Chain` is a `Fintype` of *arcs*, each consuming a state (`src`) and producing one (`dst`),
such that

* `balanced` — every state is consumed exactly as often as it is produced (as **ℕ** counts),
* `advTime` — every arc but one advances a `ZMod p`-valued clock by a natural `adv e`,
* `advPos` — that advance is positive,
* `totalLt` — the advances total less than `p`.

The distinguished arc is `conn`. From those four fields:

1. `Chain.exists_succ` — balance makes the successor relation total, so `Chain.succ` exists by
   choice (it need not be canonical, or injective).
2. `Chain.no_cycle` — a stretch of the walk returning to its own start, avoiding `conn`, advances
   the clock by a natural in `[1, p)` while leaving it unchanged. Contradiction.
3. `Chain.walk_inj` — hence the walk is injective until it meets `conn`, and `Chain.exists_walk_conn`
   — hence it must meet it, or it would inject `ℕ` into finitely many arcs.
4. `Chain.time_conn` — balance again, now summed: `∑ time (src e) = ∑ time (dst e)`, which collapses
   to `time (src conn) = time (dst conn) + total`.
5. `Chain.arc_position` — combining 3 and 4: every arc's consumed reading is `time (dst conn) + T`
   for an honest natural `T`, with `T + adv e ≤ total`.

### The instantiation

`OpenVmChain.lean` builds the chain: `BridgeArc gA := Option ((s : Fin G.length) × Fin (gA s).length)`
— one arc per realized guest instance, plus `none` for the connector.

* `src`/`dst` of a guest arc are the `(pc, t)` it receives and the `(pc', t + d)` it sends, read off
  a `ClockStep` chosen once per instance from `Circuit.advancesClock`.
* `src`/`dst` of the connector are `(finalPc, finalTimestamp)` and `(initialPc, 1)`.
* `balanced` is `VmSat.balances` on bus `0`, upgraded from `ZMod p` to ℕ counts by the budget
  (`bridge_balanced`); `openVmHost_bridge_isolated` is what says no other host chip is on bus `0`,
  and `connector_busStateOf` computes the connector's contribution.
* `time` is `openVmBridgeTimestamp`.

Then `bridge_chain_bound` reads off: each instance's `base` is `((1 + T : ℕ) : ZMod p)` and
`1 + T + d ≤ finalTimestamp.val`. Since `ConnectorBoundary.finalTimestampBounded` range-checks
`finalTimestamp.val < 2 ^ 29`, and `Circuit.advancesClock` puts every memory access of the instance
at `base + δ` with `0 < δ < d`, every memory timestamp in the run is below the window.

### Two things worth remembering

* The `some x` case of `bridge_balanced` needs `p ≠ 2`: an arc that consumed and produced the same
  state would net both `-1` and `1` there. `bridge_p_large` derives `6 < p` from the presence of a
  single instance (which forces `1 ≤ maxInstances` and `2 ≤ window`), so no extra hypothesis.
* `Chain.succ` is *not* assumed injective, and the arcs are not assumed to form one cycle. Coverage
  comes from walking *forward* from each arc to the connector rather than from decomposing the arc
  set into cycles, which is why no flow-decomposition machinery is needed.

## Phase 7: audit-surface cleanup, a translation-validation checker, and the legality-preservation
   question

Independent-session work, requested as a batch: address `Basic.lean`'s inline TODOs, revisit the
organization of the `L`/`maxInstances`/`window` size-type constraints, build a basic static
checker for `legalGuest`'s `sendOnly`/`polarity` clauses, and investigate whether soundness implies
`PreservesLegality`.

**`Basic.lean` TODOs.** `VmAssignment.satisfiesGuest`/`satisfiesHost`/`balances`/`withinBudget`
were separate one-line defs whose only call sites dotted off a `VmSat` value (never a bare
`VmAssignment`) — inlined directly into `VmSat`'s field types, a pure removal of dead indirection.
`GuestAssignment.satisfiesAlgebraic` and `HostAssignment.legal` stayed: both are used directly
elsewhere. The dead `let vm := { host := vm.host, guestChips := vm.guestChips }` in `CanProduce`
(an eta-expansion of `vm` itself) is gone. The "tie in substitution theorem" TODO became an
accurate account of what blocks it (item 2 above) rather than a stale action item. Two purely
cosmetic-naming TODOs (shorten "assignment"; rename `net`/`netBus`) were resolved by deciding not
to act — not worth the churn for no semantic gain.

**Size-constraint reorganization.** Tried naming `(maxInstances + 1) * (window + 1) < p` once as
an `abbrev ClockBudget` (checked empirically first that `abbrev` stays transparent to `omega` and
to `rw`/`exact`-style unification — a scratch build confirmed it, Lean's tactics unfold
`@[reducible]` defs) and using it everywhere the formula recurred verbatim
(`openVm_vmSoundReplacement`'s `hWindow` plus seven lemmas in `OpenVmChain.lean`). Reverted at the
user's request — `L` was grouped with the other size variables in `openVm_vmSoundReplacement`'s
binders instead (`{maxInstances ptrReg countReg window L : ℕ}`), and the raw formula stayed spelled
out everywhere. Also investigated bundling the `L`/`hSize`/`hBudget` triple into a structure and
concluded it wasn't a net win: `hSize`'s list argument genuinely varies per call site (whole `G`,
`c' :: R`, `G ++ G'`, a `Finset`-sum sub-`List`, …), so bundling would trade the current direct
re-application of `hSize` for `.mono`-style projection lemmas at every call site — no shorter, and
further from the individual proofs that actually need `hSize` alone (e.g. `guestCount_le`).

**`VmSpec/Analysis/` (new folder).** Two files, neither spec nor `Implementation/`:

- `SendOnlyPolarity.lean` — `checkMultiplicities`, a decidable syntactic pass folding each bus
  interaction's multiplicity to a literal constant (`Expression.foldConst`) and checking it against
  the legal set for its bus's statefulness. `checkMultiplicities_sound` turns a `true` result into
  actual `Circuit.statelessSendOnly ∧ Circuit.statefulPolarity`, for any `GuestBusRules` sharing the
  `isStateful` function checked against. Sound but intentionally incomplete: a bare-variable
  multiplicity (e.g. a boolean flag range-checked elsewhere) never folds, so a legitimate
  conditionally-gated send is rejected — recognizing that pattern (matching against a booleanity
  constraint in `algebraicConstraints`) is a real next tier, not attempted.
- `LegalityPreservation.lean` — the answer to "does soundness imply `PreservesLegality`?": no,
  formally. `toyBusSemantics` models a stateless bus whose acceptance never inspects multiplicity
  (true of every real OpenVM lookup table). `illegalCircuit` replaces a legal chip's constant
  multiplicity `1` with a wholly free variable; `illegalCircuit_isSoundReplacementOf` shows this is
  a sound replacement (`sideEffects` never sees a stateless bus; `satisfies` is magnitude-blind
  too), and `illegalCircuit_not_statelessSendOnly` shows it directly violates `statelessSendOnly`.
  The mechanism generalizes to `statefulPolarity`/`statefulSendsMaintain` too (splitting one
  stateful send into two interactions whose multiplicities cancel to the same net) — argued in
  prose in `agent-docs/legality-preservation.md` rather than formalized a second time, since the
  construction is the same shape.

Both files needed `import`ing into `VmSpec.lean` to become part of the actual build/audit surface
and the unused-theorem check's reachable set — a file compiled by `lake build`'s default target
set but not imported anywhere is invisible to `Scripts/UnusedTheorems.lean`, which only walks from
`ApcOptimizer`/`Main`'s transitive imports. (Caught this the first time by noticing the check
still reported the pre-existing ignore count unchanged after adding a new file with new theorems.)

**Where this leaves `PreservesLegality`.** Not a small missing lemma — it needs a genuinely
separate legality-preservation argument per optimizer pass, parallel to (not derivable from) each
pass's existing soundness proof. `agent-docs/legality-preservation.md` has the full argument and
suggests the practical path: most passes either don't touch bus interactions or touch them in
syntactically multiplicity-preserving ways, so `PreservesLegality` for those should reduce to a
short corollary plus the `SendOnlyPolarity` checker run on the pass's output, rather than a new
semantic proof each time.

**Follow-up naming pass.** `ClockBudget` (this phase's abbrev for the window budget) was reverted
at the user's request — spelled out inline again everywhere. Then, on request, the two remaining
bare size-type identifiers were renamed for consistency with `maxInstances`: `window` →
`maxWindow` (`Circuit.advancesClock`, `openVmHost`, and everything downstream) and `L` →
`maxInteractions` (`Theorems.lean`, `Connection.lean`, `Counting.lean`, `Realizes.lean`). Care was
needed distinguishing this from the unrelated "rank window" phrase (`RankModel`'s bound, prose
only, never a bound identifier) scattered through the same files' docstrings — those stayed as
`window`. Older sections of this log below predate the rename and still say `window`/`L`; that is
accurate to what the code looked like at the time, not stale.

## Phase 8: `Audit/` folder — auditing the audit surface, in one place

`OpenVmLegalAudit.lean` sat directly under `VmSpec/`, doing the same job as the `Analysis/` folder
from Phase 7 — evidence that the audited hypotheses are non-vacuous — but under a different label
("evidence" vs. "a checker's claim, not its implementation") and in a different location, purely
for historical reasons (it predates `Analysis/`). Merged: `Analysis/` renamed to `Audit/`, and
`OpenVmLegalAudit.lean` moved in alongside `SendOnlyPolarity.lean` and `LegalityPreservation.lean`.
All three now share one `VmSpec.lean` doc section ("Audited — files that audit the audit surface")
and one local `README.md`. No Lean content changed — namespaces live in the files, not the
directory, so the move is a pure reorganization; `Scripts/unused-theorems.txt`'s fully-qualified
names are unaffected.

## Next step on resume

In rough priority order:

1. **Record the wraparound side condition in the manuscript**, on `eq:stateless_as_pred`. The
   Lean now has the honest version (`VmAssignment.withinBudget` plus `L * maxInstances < p`); the
   prose does not.
2. **Wire the VM-level statement to the optimizer.** `openVm_vmSoundReplacement` takes a
   `List.Forall₂` of per-chip `isSoundReplacementOf`, and `openVmOptimizer_maintainsCorrectness`
   produces exactly that per chip. What still blocks assembling the two is `PreservesLegality` —
   confirmed in "Phase 7" *not* derivable from soundness, so this needs each pass to carry its own
   legality-preservation proof (`agent-docs/legality-preservation.md`), which is real work, not a
   short step. It is also what would let the VM-level statement seed
   `Scripts/unused-theorems.txt` (still true — see Phase 7's own ignore-list entries, which had to
   be added by hand because the folder is not reachable from the correctness roots), and what
   makes the `Spec.lean` audit-surface question above answerable.
3. ~~**Model the connector chip and the execution-bridge terminator**, to discharge
   `Host.pinsRanks`.~~ Done — see "Phase 6".
4. **Check `Circuit.legalGuest` against a whole exported APC**, not just the isolated shapes in
   `OpenVmLegalAudit.lean` — an APC has many memory accesses sharing one `from_timestamp`, and
   `readEchoChip` only exercises one.
5. **Parameterize `openVmHost` by the bus map** rather than hard-wiring `defaultBusMap`.
6. **The completeness half** (`CanProduce ⟨host, G⟩ e → CanProduce ⟨host, G'⟩ e`). Its blocker is
   unchanged: `Circuit.isCompleteReplacementOf` is gated on `Circuit.admissible`, a list-order
   property (`admissibleMemoryBus`) that order-blind `VmSat` cannot supply. Either it becomes an
   explicit "real trace" hypothesis, or `MemoryBus.lean` changes.

## Full current content of `ApcOptimizer/VmSpec/Basic.lean`

```lean
import ApcOptimizer.Spec
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-! VM-level correctness: what it means to replace a *list* of guest chips, run against a fixed
    host, by another list.

    `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` — per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates — and conditioned on VM-level invariants it cannot itself justify. This file makes
    the VM explicit instead: host chips are named, buses balance globally, and the observable is
    the VM's input/output, so no per-message assumption is needed.

    The definition is equi-effectfulness: for every effect one chipset can produce
    (`CanProduce`), the other can produce it too. Soundness is one direction
    (`VmSoundReplacement`), completeness the other.

    The rest of the folder:

    * `Validation.lean` — that the definitions here behave: `VmSat` doesn't see instance order,
      and the guest-chip list is used as a *set*.
    * `Legal.lean` — `Circuit.legalGuest`, what a VM requires of a chip before running it.
    * `Counting.lean` — the honest natural-number counts that keep a balance argument from
      wrapping around `ZMod p`.
    * `Realizes.lean` — `Host.realizes`, the single condition tying a host's chips to a
      `BusSemantics`, and what it buys (`Host.forcesAccepts`).
    * `Connection.lean` — the soundness half: per-chip `Circuit.isSoundReplacementOf` implies
      `VmSoundReplacement`.
    * `OpenVm.lean`, `OpenVmConnection.lean` — a concrete OpenVM host, and the discharge of every
      host-side condition for it. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip (memory init/final, a lookup table, the input chip, the output
    chip, ...). It is defined only by the effects it can have and by how many
    instances it can have. There is no explicit circuit. -/
structure HostChip (p : ℕ) where
  /-- Whether this `BusState` can be produced by this host-chip type. -/
  canProduce : BusState p → Prop
  /-- Must a satisfying assignment instantiate this chip just once? E.g. mem-init. -/
  singleton : Prop := False

/-- A VM's input: a stream of values. -/
abbrev VmInput (p : ℕ) := List (ZMod p)

/-- A VM's output: an array of values. -/
abbrev VmOutput (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM: inputs and outputs. -/
structure VmEffect (p : ℕ) where
  input : VmInput p
  output : VmOutput p

/-- A Host, comprising its:
    * chips,
    * input chip,
    * input computation function,
    * output chip,
    * output computation function, and
    * a proof that the output is a singleton.

    This abstracts the Host's details from the correctness definition.
    -/
structure Host (p : ℕ) where
  chips : List (HostChip p)
  /-- The VM's trace budget: the most guest-chip instances a satisfying assignment may realize,
      in total across all types (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- The proving backend's degree bound: the most a guest circuit's expressions may be nested
      before this backend can no longer prove it. Unlike `maxInstances` this is checked of a
      circuit, not of a run, so it stays out of `VmSat`; see `PreservesDegree`. -/
  degreeBound : DegreeBound
  /-- How the VM orders its stateful state — for OpenVM, a memory record's timestamp. A natural
      number, so `<` is well-founded: this is what `maintains_of_stateful_active` inducts on, and
      what makes the memory byte invariant derivable rather than assumed. See
      `Circuit.statefulSendsMaintain`. -/
  statefulRank : BusMessage p → ℕ
  /-- How far `statefulRank` may reach in a run this VM will accept — for OpenVM,
      `2 ^ timestamp_max_bits` (see `openVmRankBound`).

      A rank reads a field element as a natural number, so "the rank went up" is the order it
      looks like only while ranks stay inside a window too narrow to wrap. A chip cannot check
      that for itself, and OpenVM's does not try: its `AssertLtSubAir` range-checks the limbs of
      `timestamp - prev_timestamp - 1`, which coincides with `prev_timestamp < timestamp` exactly
      when both sit below this bound. OpenVM pins them there, but only indirectly — its connector
      chip range-checks a segment's two boundary timestamps, and the execution-bridge chain plus
      the trace budget carry that to every timestamp in between. So the bound belongs to the VM,
      like `maxInstances`, while the claim that a run respects it is `Host.pinsRanks`. -/
  rankBound : ℕ
  /-- Which guest circuits this host is prepared to run — the VM's well-formedness requirements
      on a guest chip (for OpenVM: binary multiplicities on lookup buses, `±1` on stateful ones,
      byte-valued memory sends).

      These live on the `Host` because they are the VM's requirements, not any chip's. They are
      *not* a conjunct of `VmSat`, and that placement matters: a real OpenVM AIR cannot check any
      of them — each quantifies over all assignments of the circuit, which no constraint system
      evaluates — so a run that breaks one still exists, and folding legality into satisfaction
      would quietly drop those runs from `CanProduce`. They are hypotheses of the equivalence
      theorems instead (`PreservesLegality`). -/
  legalGuest : Circuit p → Prop
  /-- The `chips` index that is the input chip type. -/
  inputChip : Fin chips.length
  /-- Map from an input chip instance's effects to its contribution to the input stream. -/
  getInputChunk : BusState p → VmInput p
  /-- The `chips` index that is the output chip type/instance (it's a singleton). -/
  outputChip : Fin chips.length
  /-- Map from an output chip instance's effects to the output array. -/
  getOutput : BusState p → VmOutput p
  /-- The output must be a singleton. -/
  outputSingleton : (chips.get outputChip).singleton

/-- A VM: a host and guest chips. -/
structure Vm (p : ℕ) where
  host : Host p
  guestChips : List (Circuit p)


/-- An assignment to a single chip instance: for each variable, what value it takes. -/
abbrev ChipAssignment (p : ℕ) := Variable → ZMod p

/-- The net multiplicity a circuit's bus interactions contribute to every message, under a
    given assignment. Unlike `Circuit.sideEffects`, this includes all buses, not
    just stateful ones. -/
def Circuit.allEffects (circuit : Circuit p) (assignment : ChipAssignment p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- Every message this instance actively touches has rank below `bound` — for OpenVM, every
    memory record it reads or writes carries a timestamp inside the VM's window. -/
def Circuit.ranksBounded (c : Circuit p) (rank : BusMessage p → ℕ) (bound : ℕ)
    (asg : ChipAssignment p) : Prop :=
  ∀ bi ∈ c.busInteractions, (bi.eval asg).multiplicity ≠ 0 →
    rank ((bi.eval asg).busId, (bi.eval asg).payload) < bound

/-- The guest half of a VM assignment: for each guest-chip *type*, however many algebraic
    assignments the witness chooses to realize (the trip count is not fixed by `guestChips`
    itself — see the module docstring). -/
abbrev GuestAssignment (p : ℕ) (guestChips : List (Circuit p)) :=
  Fin guestChips.length → List (ChipAssignment p)

/-- The host half of a VM assignment: for each host-chip type, however many bus contributions it
    realizes, one per instance (constrained to at most one wherever `HostChip.singleton` opts
    in — see `HostAssignment.legal`). -/
abbrev HostAssignment (p : ℕ) (host : Host p) := Fin host.chips.length → List (BusState p)

/-- An assignment to a VM. -/
structure VmAssignment (p : ℕ) (vm : Vm p) where
  guestAssignments : GuestAssignment p vm.guestChips
  hostAssignment : HostAssignment p vm.host

/-- The net multiplicity the guest instances contribute to every message. -/
def GuestAssignment.net {G : List (Circuit p)} (gA : GuestAssignment p G) : BusState p :=
  fun message => ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg message)).sum

/-- The net multiplicity the host instances contribute to every message. -/
def HostAssignment.net {host : Host p} (hA : HostAssignment p host) : BusState p :=
  fun message => ∑ t : Fin host.chips.length, ((hA t).map (fun effect => effect message)).sum

/-- How many guest instances the assignment realizes, across all types. -/
def GuestAssignment.instanceCount {G : List (Circuit p)} (gA : GuestAssignment p G) : ℕ :=
  ∑ t : Fin G.length, (gA t).length

/-- Every realized guest instance satisfies its own chip's algebraic constraints. -/
def GuestAssignment.satisfiesAlgebraic {G : List (Circuit p)} (gA : GuestAssignment p G) : Prop :=
  ∀ t : Fin G.length, ∀ asg ∈ gA t, (G.get t).satisfiesAlgebraic asg

/-- Every realized host-chip instance's contribution is one its type may legally make, and
    every host-chip type that opts into `HostChip.singleton` has at most one realized
    instance. -/
def HostAssignment.legal {host : Host p} (hA : HostAssignment p host) : Prop :=
  (∀ t : Fin host.chips.length, ∀ effect ∈ hA t, (host.chips.get t).canProduce effect) ∧
  (∀ t : Fin host.chips.length, (host.chips.get t).singleton → (hA t).length = 1)

/-- The net multiplicity contributed to every bus message, summed over host and guest. -/
def VmAssignment.netBus {vm : Vm p} (a : VmAssignment p vm) : BusState p :=
  fun message => a.guestAssignments.net message + a.hostAssignment.net message

omit [Fact p.Prime] in
theorem netBus_apply {vm : Vm p} (a : VmAssignment p vm) (message : BusMessage p) :
    a.netBus message = a.guestAssignments.net message + a.hostAssignment.net message := rfl

/-- Every realized guest-chip instance's algebraic constraints hold under its own assignment. -/
def VmAssignment.satisfiesGuest {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  a.guestAssignments.satisfiesAlgebraic

/-- The host side of the assignment is legal (`HostAssignment.legal`). -/
def VmAssignment.satisfiesHost {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  a.hostAssignment.legal

/-- Every bus balances: the net contribution to every message is zero. -/
def VmAssignment.balances {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  ∀ message : BusMessage p, a.netBus message = 0

/-- The assignment fits the VM's trace budget.

    This is needed to prevent overflow, e.g., in multiplicities. -/
def VmAssignment.withinBudget {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  a.guestAssignments.instanceCount ≤ vm.host.maxInstances

/-- Every guest instance's traffic stays inside the VM's rank window (`Host.rankBound`).

    Needed to prevent overflow, but of a different kind than `withinBudget`: not in a multiplicity
    but in the rank itself, which is a field element read as a natural number and ordered only
    while it stays in the window.

    Not a conjunct of `VmSat`, because no OpenVM AIR checks it: the connector constrains the two
    timestamps on its own two rows, and a memory access constrains only the *difference* across
    it. That every timestamp in between is in range is a multi-chip consequence, and deriving it
    is this spec's job rather than its premise — see `Host.pinsRanks`. -/
def VmAssignment.withinRankBound {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  ∀ t : Fin vm.guestChips.length, ∀ asg ∈ a.guestAssignments t,
    (vm.guestChips.get t).ranksBounded vm.host.statefulRank vm.host.rankBound asg

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (its own algebraic
    constraints, or, for a host-chip instance, its type's legality), every host-chip type that
    opts into `singleton` stays a singleton, every bus balances, and the whole thing fits the VM's
    trace budget and rank window.

    Every conjunct is something a real OpenVM run is checked on *directly*, and nothing else goes
    in. Two kinds of thing are therefore absent:

    * Requirements on a guest *circuit* — `Host.legalGuest`, `Host.degreeBound`. These quantify
      over all assignments, which no constraint system evaluates, so a run violating one still
      exists. They are obligations on the optimizer instead (`PreservesLegality`,
      `PreservesDegree`).
    * Invariants that hold of every real run but only as a *consequence* of several chips —
      `VmAssignment.withinRankBound`. Assuming one here would shrink `CanProduce` below the set of
      runs OpenVM admits, and would assume away the very thing this spec exists to derive
      (`Host.pinsRanks`). -/
structure VmSat (vm : Vm p) (a : VmAssignment p vm) : Prop where
  satisfiesGuest : a.satisfiesGuest
  satisfiesHost : a.satisfiesHost
  balances : a.balances
  withinBudget : a.withinBudget
-- ANCHOR_END: vmSat

/-- The effects of a satisfying VM assignment: the input stream its input-chip instances pulled,
    concatenated in list order, and the array its output-chip instance left behind. -/
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) (h : VmSat vm a) : VmEffect p :=
  { input := (a.hostAssignment vm.host.inputChip).map vm.host.getInputChunk |>.flatten,
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).head (by
      have hlen := h.satisfiesHost.2 vm.host.outputChip vm.host.outputSingleton
      intro hnil
      simp [hnil] at hlen)) }

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `host`, can produce effect `e`. -/
def CanProduce (vm : Vm p) (e : VmEffect p) : Prop :=
  let vm : Vm p := { host := vm.host, guestChips := vm.guestChips }
  ∃ (a : VmAssignment p vm) (h : VmSat vm a), a.effects h = e
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a *sound* VM-level replacement for `guestChips`: it can produce no effect
    the original could not. Nothing new becomes possible.

    The multi-chip analogue of `Circuit.isSoundReplacementOf`. -/
def VmSoundReplacement (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips'⟩ e → CanProduce ⟨host, guestChips⟩ e

/-- `guestChips'` is a *complete* VM-level replacement for `guestChips`: every effect the
    original could produce, it can produce too. Nothing is lost.

    The multi-chip analogue of `Circuit.isCompleteReplacementOf`. -/
def VmCompleteReplacement (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips⟩ e → CanProduce ⟨host, guestChips'⟩ e

/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed
    `host`: they are equi-effectful. -/
def VmEquivalent (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  VmSoundReplacement host guestChips guestChips' ∧
    VmCompleteReplacement host guestChips guestChips'
-- ANCHOR_END: vmEquivalent

/-- The replacement chips are ones the host will run, given that the originals were. The VM-level
    counterpart of the `Host.legalGuest` field, kept out of `VmSat` — see there.

    Soundness needs this, not just legality of the originals: `Host.forcesAccepts` runs its
    balancing argument over the list the VM is actually executing, which for a sound replacement
    is the *optimized* one. -/
def PreservesLegality (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  (∀ c ∈ guestChips, host.legalGuest c) → ∀ c ∈ guestChips', host.legalGuest c

/-- The replacement chips fit the backend's degree bound, given that the originals did. The
    VM-level counterpart of `Spec.lean`'s `optimizerRespectsDegreeBound`, and independent of
    everything else here: nothing in the equivalence proof consumes it. -/
def PreservesDegree (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  (∀ c ∈ guestChips, c.withinDegree host.degreeBound) →
    ∀ c ∈ guestChips', c.withinDegree host.degreeBound
```
