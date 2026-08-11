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
word once, `singleton := True`), `memoryFinalizeHostChip` (receives any final word,
`singleton := True`), `outputHostChip` (receives any final word at address space `3`,
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

`openVm (initialWord) (ptrReg countReg) (memBusId := 1) : Vm p` assembles all eight `HostChip`s
into one list and wires `inputChipType`/`outputChipType`/`inputChunk`/`outputArray` together
(indices `⟨7, by simp⟩`/`⟨6, by simp⟩` — `by decide` failed here since the list's *elements*
contain free variables (`ptrReg` etc.), even though only the list's *length* — which doesn't
depend on element values — matters; `simp` reduces the length symbolically instead). `openVm`
and both extractors are `noncomputable` (unavoidable — `Classical.choice` isn't computable).
Builds clean end to end, no new theorems (so nothing for the unused-theorem checker to flag).

## Next step on resume

No known open design gaps in the current shape. Candidates for what's next: (a) instantiate a
concrete `Vm` for OpenVM (payload-layout decoding for `inputChunk`/`outputArray`, concrete
`HostChip`s for the OpenVM bus map), or (b) the connecting theorem sketched in `vmEquivalent`'s
docstring — per-chip `refines` (matched up between `guestChips` and `guestChips'`) implies
`vmEquivalent`.

## Full current content of `ApcOptimizer/VmSpec.lean`

```lean
import ApcOptimizer.Spec

set_option autoImplicit false

/-! `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` (per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates). This file instead defines equivalence for a *list* of guest chips together,
    following the "VM equivalence" definition at the end of the `manuscript-powdr-ver` writeup:
    a VM is some guest-chip types (what the optimizer touches, each a full `Circuit`) plus some
    host-chip types (memory init/final, lookup tables, the input chip, the output chip —
    everything else), and two guest-chip lists are equivalent when they can each produce exactly
    the same externally observable effects.

    Every chip is a *type*: a real VM assignment realizes however many *instances* of each type
    it needs (a basic block's trip count, or how many times the input chip is invoked, are
    data-dependent and unknowable to the optimizer), so instance counts are part of the witness
    (`VmAssignment`), never fixed by `guestChips`/`hostChips` themselves. A few chip types (per
    vm.tex: memory init, memory final, output, each lookup table) can only ever have at most one
    instance; that's `HostChip.singleton`, opt-in and `False` by default.

    Host chips are represented directly by the interactions they may legally make (`HostChip`
    below), never by algebraic constraints of their own — mirroring how `BusSemantics` already
    stood in for "an opaque chip, specified only by what it accepts." Unlike `Spec.lean`, this
    file has no notion of *stateful* vs *stateless* buses, and no ordering discipline on bus
    interactions (contrast `MemoryBus.lean`'s `admissibleMemoryBus`, which reasons about
    consecutive-in-list-order pairs for one circuit). At VM level, every bus — lookup or memory
    alike — is subject to exactly one requirement: the net multiplicity of every message, summed
    over every realized instance's contribution, is zero. That single requirement is what
    `VmSat` checks.

    Effects are the VM's two externally observable interfaces: `Input`, the flat stream of
    values fed to the input chip across all of its realized instances, and `Output`, the flat
    array read back from the output chip's single realized instance. Both are plain arrays, not
    the raw per-message `BusState` — `BusState` is order-blind (it nets *by message*), which
    fits a final memory snapshot but not a stream, where position is the whole point. `VmSat`
    never constrains the order of a chip type's realized instances (its `legal` check is by
    membership, its balance check sums — both order-blind), so *that* order is already a free
    choice of the witness `a`, and `CanEffect` reads the input stream straight off
    `a.hostContribution vm.inputChipType` in list order: no separate notion of chip execution
    order is needed anywhere in the model. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip type, standing in for one of the VM's non-guest chips (memory init/final, a
    lookup table, the input chip, the output chip, ...). It has no algebraic constraints of its
    own — only the set of bus contributions each of its instances may legally make. -/
structure HostChip (p : ℕ) where
  /-- Whether a candidate contribution (a net multiplicity per bus message) is one an instance
      of this host-chip type may legally make. For a lookup table, e.g., this restricts
      contributions to nonpositive multiplicities whose payload is an actual table entry. -/
  legal : BusState p → Prop
  /-- Whether this type may only ever have at most one realized instance in a satisfying VM
      assignment (e.g. memory initialization/finalization, the output chip, each lookup table —
      per vm.tex's manuscript). Opt-in: defaults to `False`, i.e. unbounded instances — most
      chip types, the input chip included, may run any number of times. -/
  singleton : Prop := False

/-- The net multiplicity a circuit's bus interactions contribute to every message, under a
    given assignment. Unlike `Circuit.sideEffects`, this covers *every* bus interaction, not
    just stateful ones: at VM level, lookups balance the very same way memory does (see
    `VmSat`), so there is no separate stateless/`accepts` case to carve out. -/
def Circuit.netContribution (circuit : Circuit p) (assignment : Variable → ZMod p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- An assignment to a VM: for each guest-chip *type*, however many algebraic assignments the
    witness chooses to realize (the trip count is not fixed by `guestChips` itself — see the
    module docstring); likewise, for each host-chip type, however many bus contributions it
    realizes, one per instance (constrained to at most one wherever `HostChip.singleton`
    opts in — see `VmSat`). -/
structure VmAssignment (p : ℕ) (guestChips : List (Circuit p)) (hostChips : List (HostChip p)) where
  guestAssignment : (t : Fin guestChips.length) → List (Variable → ZMod p)
  hostContribution : (t : Fin hostChips.length) → List (BusState p)

/-- Every realized guest-chip instance's algebraic constraints hold under its own assignment. -/
def VmAssignment.guestSatisfies {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin guestChips.length, ∀ asg ∈ a.guestAssignment t,
    ∀ c ∈ (guestChips.get t).algebraicConstraints, c.eval asg = 0

/-- Every realized host-chip instance's contribution is one its type may legally make. -/
def VmAssignment.hostLegal {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin hostChips.length, ∀ contribution ∈ a.hostContribution t,
    (hostChips.get t).legal contribution

/-- Every host-chip type that opts into `HostChip.singleton` has at most one realized
    instance. -/
def VmAssignment.singletonsRespected {guestChips : List (Circuit p)}
    {hostChips : List (HostChip p)} (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin hostChips.length, (hostChips.get t).singleton → (a.hostContribution t).length ≤ 1

/-- The net multiplicity contributed to every bus message, summed over every realized guest- and
    host-chip instance's contribution. -/
def VmAssignment.netContribution {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : BusState p :=
  fun message =>
    (∑ t : Fin guestChips.length,
      ((a.guestAssignment t).map (fun asg => (guestChips.get t).netContribution asg message)).sum) +
    (∑ t : Fin hostChips.length,
      ((a.hostContribution t).map (fun contribution => contribution message)).sum)

/-- Every bus balances: the net contribution to every message is zero. -/
def VmAssignment.balances {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ message : BusMessage p, a.netContribution message = 0

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (its own algebraic
    constraints, or, for a host-chip instance, its type's legality), every host-chip type that
    opts into `singleton` stays a singleton, and every bus balances. -/
def VmSat (guestChips : List (Circuit p)) (hostChips : List (HostChip p))
    (a : VmAssignment p guestChips hostChips) : Prop :=
  a.guestSatisfies ∧ a.hostLegal ∧ a.singletonsRespected ∧ a.balances
-- ANCHOR_END: vmSat

omit [Fact p.Prime] in
theorem VmSat.of_perm {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    {a a' : VmAssignment p guestChips hostChips}
    (hguest : ∀ t, (a'.guestAssignment t).Perm (a.guestAssignment t))
    (hhost : ∀ t, (a'.hostContribution t).Perm (a.hostContribution t))
    (hsat : VmSat guestChips hostChips a) : VmSat guestChips hostChips a' := by
  obtain ⟨h1, h2, h3, h4⟩ := hsat
  have hnet : a'.netContribution = a.netContribution := by
    funext message
    show (∑ t : Fin guestChips.length,
        ((a'.guestAssignment t).map (fun asg => (guestChips.get t).netContribution asg message)).sum) +
      (∑ t : Fin hostChips.length,
        ((a'.hostContribution t).map (fun contribution => contribution message)).sum) =
      (∑ t : Fin guestChips.length,
        ((a.guestAssignment t).map (fun asg => (guestChips.get t).netContribution asg message)).sum) +
      (∑ t : Fin hostChips.length,
        ((a.hostContribution t).map (fun contribution => contribution message)).sum)
    rw [Finset.sum_congr rfl (fun t _ => ((hguest t).map _).sum_eq),
      Finset.sum_congr rfl (fun t _ => ((hhost t).map _).sum_eq)]
  exact ⟨fun t asg hasg => h1 t asg ((hguest t).mem_iff.mp hasg),
    fun t contribution hcontrib => h2 t contribution ((hhost t).mem_iff.mp hcontrib),
    fun t hsingle => (hhost t).length_eq ▸ h3 t hsingle,
    fun message => (congrFun hnet message).trans (h4 message)⟩

omit [Fact p.Prime] in
/-- `VmSat` only depends on each chip type's realized instances as a *multiset*: permuting any
    type's instance list, guest or host, preserves satisfiability. This is why `CanEffect` can
    read the input stream straight off `a.hostContribution vm.inputChipType` in list order with
    no separate existential permutation — reordering that list (or any other type's) never
    changes whether an assignment is `VmSat`, so the freedom to choose an order was already
    available through the witness `a` itself. -/
theorem VmSat.perm_iff {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    {a a' : VmAssignment p guestChips hostChips}
    (hguest : ∀ t, (a'.guestAssignment t).Perm (a.guestAssignment t))
    (hhost : ∀ t, (a'.hostContribution t).Perm (a.hostContribution t)) :
    VmSat guestChips hostChips a' ↔ VmSat guestChips hostChips a :=
  ⟨fun h => VmSat.of_perm (fun t => (hguest t).symm) (fun t => (hhost t).symm) h,
    fun h => VmSat.of_perm hguest hhost h⟩

/-- The VM's input interface: the flat stream of values fed, in order, to the input chip
    across all of its realized instances. Where one instance's chunk ends and the next begins is
    not part of the type — only the concatenation is externally observable (see `CanEffect`). -/
abbrev Input (p : ℕ) := List (ZMod p)

/-- The VM's output interface: the flat array read back from the output chip's single realized
    instance. -/
abbrev Output (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM run: what it consumed and what it produced. -/
structure Effect (p : ℕ) where
  input : Input p
  output : Output p

/-- A VM: its host-chip types, which one is the input chip's type (it may have any number of
    realized instances) and which is the output chip's type (expected — by convention, opt into
    `HostChip.singleton` on it — to have exactly one, so `e.output` is well-defined), and how to
    read one instance's own bus contribution as its stream chunk / output array. That extraction
    is left abstract here — it depends on the payload layout of whichever bus the input/output
    chips use, which is VM-specific in the same way `OpenVmSemantics.lean`'s payload decoding
    is. -/
structure Vm (p : ℕ) where
  hostChips : List (HostChip p)
  /-- The `hostChips` index that is the input chip's type. -/
  inputChipType : Fin hostChips.length
  /-- An input-chip instance's stream chunk, read off its own bus contribution. -/
  inputChunk : BusState p → Input p
  /-- The `hostChips` index that is the output chip's type. -/
  outputChipType : Fin hostChips.length
  /-- The output chip's output array, read off its (single realized) instance's contribution. -/
  outputArray : BusState p → Output p

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `vm`, can produce effect `e`: whether some satisfying VM
    assignment realizes exactly that input stream and output array. The input stream is the
    concatenation, in list order, of `a.hostContribution vm.inputChipType`'s chunks; since
    `VmSat` never constrains that order, this already ranges over every possible way the
    realized input-chip instances could line up (see the module docstring) — no separate
    permutation is needed on top of the witness `a`. The output is read off the single realized
    output-chip instance (there is none, or more than one, unless the `Vm`'s `outputChipType`
    opts into `HostChip.singleton`; see `VmSat`). -/
def CanEffect (vm : Vm p) (guestChips : List (Circuit p)) (e : Effect p) : Prop :=
  ∃ a : VmAssignment p guestChips vm.hostChips, VmSat guestChips vm.hostChips a ∧
    ((a.hostContribution vm.inputChipType).map vm.inputChunk).flatten = e.input ∧
    ∃ c, a.hostContribution vm.outputChipType = [c] ∧ vm.outputArray c = e.output
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed `vm`:
    every effect one can produce, the other can produce too, and vice versa. This is the
    multi-chip analogue of `Circuit.isSoundReplacementOf` / `Circuit.isCompleteReplacementOf`
    from `Spec.lean` — a future connecting theorem should show that per-chip `refines` (matched
    up between `guestChips` and `guestChips'`) implies this. -/
def vmEquivalent (vm : Vm p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : Effect p, CanEffect vm guestChips e ↔ CanEffect vm guestChips' e
-- ANCHOR_END: vmEquivalent
```
