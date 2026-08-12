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

File: `ApcOptimizer/VmSpec.lean` (new, **uncommitted** — see `git status`; also uncommitted:
one import line added to `ApcOptimizer.lean`). Builds clean (`lake build` passes end to end,
zero warnings). Definitions only, no theorems — explicit scope decision, to get the shape
reviewed before investing in proofs. Full current file content is reproduced verbatim at the
bottom of this doc in case the working-tree copy doesn't make it across machines.

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
`HostLegal`/`hostNet`/`guestNet` restate pieces of `VmSpec.lean` over the host assignment alone
so the conditions can be stated without a `Vm` in scope — each is defeq to its `VmSpec.lean`
counterpart (`hostLegal_of_satisfiesHost` and `netBus_apply` are both proved by `id`/`rfl`).
All nine theorems went into `Scripts/unused-theorems.txt`'s `[ignore]`, same rationale as the
`VmSpec.lean` entries.

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

## Next step on resume

In rough priority order:

1. **`Host.absorbsStateless` for `openVmHost`** — the last hypothesis of
   `canEffect_of_isSoundReplacementOf` not discharged for a concrete host. Shape and remaining
   work described in the section above.
2. **Record the wraparound side condition in the manuscript**, on `eq:stateless_as_pred`. The
   Lean now has the honest version (`VmAssignment.withinBudget` plus `L * maxInstances < p`); the
   prose does not.
3. **Derive `Circuit.statefulAccepts`** rather than assuming it — the manuscript's
   `eq:legal:recv_byte` from `eq:legal:stateful:send_byte` plus balancing.
4. **The completeness half** (`CanEffect host G e → CanEffect host G' e`). Its blocker is
   unchanged: `Circuit.isCompleteReplacementOf` is gated on `Circuit.admissible`, a list-order
   property (`admissibleMemoryBus`) that order-blind `VmSat` cannot supply. Either it becomes an
   explicit "real trace" hypothesis, or `MemoryBus.lean` changes.

## Full current content of `ApcOptimizer/VmSpec.lean`

```lean
import ApcOptimizer.Spec

set_option autoImplicit false

/-! `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` (per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates).

    It's equivalence definition is conditioned on certain VM-level invariants
    and assumptions.  It is not clear whether those hold.

    This file defines equivalence for a *list* of guest chips together in the
    context of a host.  It's definition omits complex assumptions and
    invariants.

    Our next task is to ensure that if each chip (`Circuit`) in the list is
    replaced by an equivalent chip, according to the other definition, then this
    equivalence definition holds.

    The basic structure of the definition is equi-effectfulness: for every
    effect one chipset can produce, the other can produce it too, and vice
    versa.

    So, we need to define chips, effects, whether a chipset can produce an
    effect (i.e., whether some assignment to it has that effect).
    -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip (memory init/final, a lookup table, the input chip, the output
    chip, ...). It is defined only by the effects it can have and by how many
    instances it can have. There is no explicit circuit. -/
structure HostChip (p : ℕ) where
  /-- Whether this `BusState` is a valid effect for an instance of this host-chip type. -/
  canEffect : BusState p → Prop
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

abbrev HostAssignment (p : ℕ) (host : Host p) := (t : Fin host.chips.length) → List (BusState p)

/-- An assignment to a VM: for each guest-chip *type*, however many algebraic assignments the
    witness chooses to realize (the trip count is not fixed by `guestChips` itself — see the
    module docstring); likewise, for each host-chip type, however many bus contributions it
    realizes, one per instance (constrained to at most one wherever `HostChip.singleton`
    opts in — see `VmSat`). -/
structure VmAssignment (p : ℕ) (vm : Vm p) where
  guestAssignments : Fin (vm.guestChips.length) → List (ChipAssignment p)
  hostAssignment : HostAssignment p vm.host

/-- The net multiplicity contributed to every bus message, summed over host and guest. -/
def VmAssignment.netBus {vm : Vm p} (a : VmAssignment p vm) : BusState p :=
  fun message =>
    (∑ t : Fin vm.guestChips.length,
      ((a.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
    (∑ t : Fin vm.host.chips.length,
      ((a.hostAssignment t).map (fun effect => effect message)).sum)

/-- Every realized guest-chip instance's algebraic constraints hold under its own assignment. -/
def VmAssignment.satisfiesGuest {vm : Vm p}
    (a : VmAssignment p vm) : Prop :=
  ∀ t : Fin vm.guestChips.length, ∀ asg ∈ a.guestAssignments t,
    ∀ c ∈ (vm.guestChips.get t).algebraicConstraints, c.eval asg = 0

/-- Every realized host-chip instance's contribution is one its type may legally make, and
    every host-chip type that opts into `HostChip.singleton` has at most one realized
    instance. -/
def VmAssignment.satisfiesHost {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  (∀ t : Fin vm.host.chips.length, ∀ effect ∈ a.hostAssignment t,
    (vm.host.chips.get t).canEffect effect) ∧
  (∀ t : Fin vm.host.chips.length,
    (vm.host.chips.get t).singleton → (a.hostAssignment t).length = 1)

/-- Every bus balances: the net contribution to every message is zero. -/
def VmAssignment.balances {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  ∀ message : BusMessage p, a.netBus message = 0

/-- The assignment fits the VM's trace budget.

    Balance alone is weaker than it looks, because multiplicities live in `ZMod p`: `p` instances
    that each send the *same* message net to zero, so no host chip has to receive it and a lookup
    table never gets to object. Bounding how many instances a witness may realize is what closes
    that off — see `Host.forcesAccepts` in `VmSpecConnection.lean`, which is unprovable without
    it. The bound is on instance counts alone, not on instances × bus interactions, so that it is
    fixed by the `Host` and therefore identical for the two guest-chip lists an equivalence
    compares; converting it into a bound on *messages* is the connecting theorem's job. -/
def VmAssignment.withinBudget {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  (∑ t : Fin vm.guestChips.length, (a.guestAssignments t).length) ≤ vm.host.maxInstances

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (its own algebraic
    constraints, or, for a host-chip instance, its type's legality), every host-chip type that
    opts into `singleton` stays a singleton, every bus balances, and the whole thing fits the
    VM's trace budget. -/
def VmSat (vm: Vm p) (a : VmAssignment p vm) : Prop :=
  a.satisfiesGuest ∧ a.satisfiesHost ∧ a.balances ∧ a.withinBudget
-- ANCHOR_END: vmSat

/-- The effects of a satisfying VM assignment: the input stream its input-chip instances pulled,
    concatenated in list order, and the array its output-chip instance left behind. -/
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) (h : VmSat vm a) : VmEffect p :=
  { input := (a.hostAssignment vm.host.inputChip).map vm.host.getInputChunk |>.flatten,
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).head (by
      obtain ⟨-, ⟨-, hsingle⟩, -⟩ := h
      have hlen := hsingle vm.host.outputChip vm.host.outputSingleton
      intro hnil
      simp [hnil] at hlen)) }

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (unidirectional). -/
theorem VmSat.of_perm {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t))
    (hsat : VmSat vm a) : VmSat vm a' := by
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := hsat
  have hnet : a'.netBus = a.netBus := by
    funext message
    show (∑ t : Fin vm.guestChips.length,
        ((a'.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin vm.host.chips.length,
        ((a'.hostAssignment t).map (fun effect => effect message)).sum) =
      (∑ t : Fin vm.guestChips.length,
        ((a.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin vm.host.chips.length,
        ((a.hostAssignment t).map (fun effect => effect message)).sum)
    rw [Finset.sum_congr rfl (fun t _ => ((hguest t).map _).sum_eq),
      Finset.sum_congr rfl (fun t _ => ((hhost t).map _).sum_eq)]
  exact ⟨fun t asg hasg => h1 t asg ((hguest t).mem_iff.mp hasg),
    ⟨fun t effect hcontrib => h2 t effect ((hhost t).mem_iff.mp hcontrib),
      fun t hsingle => (hhost t).length_eq ▸ h3 t hsingle⟩,
    ⟨fun message => (congrFun hnet message).trans (h4 message),
      (Finset.sum_congr rfl (fun t _ => (hguest t).length_eq)).trans_le h5⟩⟩

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (bidirectional). -/
theorem VmSat.perm_iff {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t)) :
    VmSat vm a' ↔ VmSat vm a :=
  ⟨fun h => VmSat.of_perm (fun t => (hguest t).symm) (fun t => (hhost t).symm) h,
    fun h => VmSat.of_perm hguest hhost h⟩

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `host`, can produce effect `e`. -/
def CanEffect (host : Host p) (guestChips : List (Circuit p)) (e : VmEffect p) : Prop :=
  let vm : Vm p := { host := host, guestChips := guestChips }
  ∃ (a : VmAssignment p vm) (h : VmSat vm a), a.effects h = e
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed
    `host`: they are equi-effectful.

    This is the multi-chip analogue of `Circuit.isSoundReplacementOf` /
    `Circuit.isCompleteReplacementOf`. -/
def VmEquivalent (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : VmEffect p, CanEffect host guestChips e ↔ CanEffect host guestChips' e
-- ANCHOR_END: vmEquivalent
```
