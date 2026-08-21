# `VmSpec` audit findings

A running list of problems found while auditing `ApcOptimizer/VmSpec/`. Each entry records the
**mechanism** (why it is true of the definitions as written), the **impact** (what it does to the
meaning of `openVm_vmSoundReplacement`), and a **status**. Findings are about the *audited* surface
— `Basic.lean`, `Legal.lean`, `OpenVm.lean`, `Theorems.lean` — since a mistake under
`Implementation/` can only fail to compile.

Ordered by how much they cost the theorem, not by how hard they are to fix.

## A. The observable: `VmAssignment.effects` and the I/O host chips

### A1. The output is not determined by the computation

*Status: fixed (2026-08-20).*

**Mechanism, as found.** `OutputRead.interactions` built each received word as
`payload := [3, i, w, 0, 0, 0, 0]`; payload field `6` is the memory timestamp (`memoryPayload?`), so
every address-space-3 record the output chip received sat at timestamp `0`. Bus balance means some
chip *sent* that exact message, and only `memoryInitHostChip` could — it is the one chip whose
`canProduce` demands `message.2[6]? = some 0`. A guest could not: `advancesClock` puts its memory
records at `base + δ`, and `openVmHost_pinsRanks` forces `base = 1 + T`, hence `val ≥ 2 ≠ 0`. So
`VmEffect.output` was a function of the memory-init witness alone — arbitrary byte data chosen by
the prover, independent of the guest chips.

**Fix, step 1 — unpin the timestamp.** `OutputRead` gained `times : List (ZMod p)`, one free
timestamp per word, exactly as `memoryFinalizeHostChip` leaves the timestamps of the records it
receives; `interactions` puts each word's own timestamp in field `6` instead of `0`. A guest write
at `base + δ` can now be received by the output chip, so the output became causally reachable from
the computation. `outputArrayOf` gained no new ambiguity from this: every message the witness
describes is a distinct `-1`, so nothing cancels and the witness stays recoverable (unlike the input
side — see A3).

That step alone was not enough: `memoryInitHostChip` restricted no address space, so it could still
send `[3, i, w, 0, 0, 0, 0]` and the output chip could still receive it — the output was reachable
from the computation but not determined by it, and the option of dropping the output *entirely* onto
memory init (rather than sourcing it from a guest write) was still on the table.

**Fix, step 2 — pin memory init's address-space-3 words to `0`, not just to leave that bus alone.**
The tempting-looking alternative — restrict `memoryInitHostChip` to address spaces `1`/`2`, so
address space `3` has no sender but a guest write — turns out to be unsound at the model's own
memory discipline: `MemoryBus.lean`'s `receiveThenSend` requires a write to *receive* the cell's
previous record before it *sends* the new one, so a guest's first write to an address-space-`3` cell
still needs some earlier record to receive, and only memory init runs before any guest instance.
Leaving address space `3` out of memory init entirely would make that first write, and hence the
output chip, unsatisfiable — trading a spec bug for a soundness-preserving but overly narrow model
(no legal guest could ever produce output).

So `memoryInitHostChip.canProduce` keeps every address space, but its `f.addressSpace.val = 3` case
now forces `∀ d ∈ f.data, d = 0` — the initial state a guest's first write receives is fixed at
zero, matching volatile mode. A forged output is now always the all-zero array; any other output has
to come from a guest write. `HostAssignment.satisfies` and `openVmHost_sinksAreTables`'s proof needed
one extra field unpacked (`obtain` grew a `-`) and nothing else moved.

**What remains.** None of A1's own scope. The related, larger question — that the *rest* of initial
memory (address spaces `1`/`2`) is still an unconstrained VM input, so a segment's public inputs are
not modelled at all — is now the lower tier's `memoryInitHostChip` entry, option 3 (a `Host`-level
initial-memory field) if that ever needs closing.

### A2. The input stream is only meaningfully ordered when timestamps are distinct

*Status: fixed (2026-08-20).*

**Mechanism, as found.** `VmAssignment.effects` read `input` off the *list order* of the input
chip's instance list, but `VmSat.perm_iff` (`Implementation/Validation.lean`) proves `VmSat` is
invariant under permuting each host chip's instance list. So `CanProduce` was closed under
permuting input chunks: reading `[a, b]` and `[b, a]` were the same effect, for *any* two instances,
regardless of when either ran.

**Fix, step 1 — sort by time.** `Host` gained `getInputTime : BusState p → ZMod p`, alongside
`getInputChunk`. `VmAssignment.orderedInputInstances` sorts the input chip's realized instances by
`.val` of `getInputTime` before `effects` maps and flattens them (`Basic.lean`); `openVmHost`
supplies `inputTimeOf`, which recovers a witnessing `InputRead`'s `base` — by the same
`Classical.choose` call `inputChunkOf` uses to recover `bytes` (choice depends only on the
existential's proposition, not which proof is in hand, so the two agree on one witness). Left a
residual: nothing yet forced two different instances to distinct `base`s, so a same-timestamp tie
could still make the sort's output depend on list position — permuting such instances was still
invisible to `CanProduce`.

**Fix, step 2 — put the input chip on the execution bridge, and prove ties impossible.** Two
pieces, mutually dependent, both landed this session.

1. `Chain.arc_position` only ever gave distance-from-connector, bounded but not necessarily
   unique. `VmChain.Chain.time_injOn` (`Implementation/Chain.lean`) is the missing injectivity —
   no two non-connector arcs ever share a *clock reading* — proved from the same `balanced`/
   `no_cycle` axioms the file already had: any state with two producers (or consumers) forces a
   branch, and a branch has to reconnect somewhere, closing a cycle that avoids the connector,
   which `no_cycle` already forbids. Formalized via a genuinely more general fact,
   `no_selfBalanced_of_not_mem_conn` (any nonempty self-balanced arc-set avoiding the connector is
   impossible — not just ones shaped like `Chain.walk`'s own trajectory), applied to the complement
   of the connector's own lap (`Chain.cycleSet`, shown self-balanced by a cyclic index-shift
   bijection) to force that lap to cover every arc, hence every arc a unique lap position, hence
   (`walkSum` strictly increasing along the lap) a unique clock reading. `Chain.src_injOn` (full
   *state* distinctness) is now a one-line corollary via `congrArg C.time`.
2. `InputRead` gained `pcFrom`/`pcTo`/`d`/`dPos`, and `.interactions` opens with the same
   receive/send pair on the execution bridge a guest `ClockStep` produces — whitepaper §4.5:
   `Rv32HintStoreAir` is an instruction executor like any other, not traffic outside the
   instruction stream. `inputHostChip` gained a `maxWindow` parameter bounding `r.d`, mirroring
   `ClockStep.dLt`. `OpenVmChain.lean`'s `BridgeArc` became `Option (guest-sigma ⊕ Fin n)`, one arc
   per realized input-chip instance alongside every guest instance and the connector;
   `openVmHost_bridge_isolated` now recovers each instance's `InputRead` witness (and, via
   `Classical.choose` determinism again, the fact `Host.getInputTime` reads off the same witness's
   `base`) and states bus-`0` balance including the input net; `bridge_balanced`/`bridge_total_le`/
   `bridge_totalLt`/`bridgeChain`/`bridge_chain_bound` all generalized to cover both instance
   kinds, and `OpenVmParams.windowOk` now bounds `maxInstances + maxInputInstances` together
   (deriving the old guest-only `Host.noTimeOverflow` from it, since that field's type is audited
   in `Basic.lean` and unchanged).

`openVmHost_inputTime_injOn` (`OpenVmChain.lean`) puts the two together: two different realized
input-chip instances are two different non-connector arcs of the very same bridge chain, so
`Chain.time_injOn` gives them distinct `getInputTime` values, unconditionally — the tie
`VmAssignment.orderedInputInstances`' sort could previously not rule out is now impossible.
`sorry`-free, `lake build` and `Scripts/check-proof-integrity.sh` both clean.

### A3. `inputChunkOf` is not a function of what the VM did

*Status: open.*

**Mechanism.** Every access in `InputRead.interactions` is a receive/send pair on the same payload
shape, so a witness with `ptrTime = base`, `countTime = base + 1`,
`oldWords[i] = #v[bytes[i],0,0,0]` and `wordTimes[i] = base + 2 + i` cancels to the identically-zero
`BusState`. A `count = 0` witness cancels to zero too. Both satisfy `inputHostChip.canProduce` with
different `bytes`, so `Classical.choose` picks an unspecified chunk and `inputChunkOf 0 = []` is not
provable. Real OpenVM excludes this with `prev_timestamp < timestamp` on every access; `InputRead`
carries no such field.

**Impact.** The model admits arbitrarily many input-chip instances that consume phantom input at
zero bus cost, and the recovered chunk need not be what was written.

**Fix.** Put the AssertLt discipline on the witness, or make the witness part of the assignment
instead of recovering it by choice.

## B. `VmSat` budgets the guest and not the host

*Status: fixed — see `HostChip.instanceBound` (2026-08-20). The quantitative half is still open:
`Host.noMultOverflow` counts guest interactions only, so host contributions are still not part of the
anti-wraparound arithmetic.*

**Mechanism.** `VmSat.withinBudget` bounded `guestAssignments.instanceCount` only, and
`HostAssignment.satisfies` asked for producibility and singleton-ness, nothing else. `inputHostChip`
has `singleton := False`, so a run could realize unboundedly many input instances, each touching the
memory bus with `±1`.

**Impact.** `VmSat` accepted runs where a stateful bus balances only modulo `p` — `p` copies of one
message sum to `0` in the field. The anti-wraparound story (`Counting.lean`, `noMultOverflow`'s
"+1 for the exempt host chip") covers the guests plus one singleton receive-only chip; the input chip
was outside it.

**Fix applied.** Two changes.

*The tables became singletons.* `lookupTableHostChip` had left `singleton` at its `False` default,
so the four lookup tables were unbounded alongside the input chip. A VM has one table chip per bus —
its rows are its table entries — and pinning the count costs nothing, because the chip's predicate
is closed under sums and holds of `0`, so one instance reaches exactly the nets any number of them
could. `Host.absorbsStateless` used to *append* an instance per lookup chip; it now pools each
chip's instances into the one the singleton allows, plus that bus's slice of `δ`
(`openVmHost_absorbsStateless`).

*Every chip got a cap, and `singleton` went away.* `HostChip.singleton : Prop` is replaced by
`instanceBound : ℕ` — required, no default and no `Option`, so an unbounded host chip cannot be
written down; the property no longer needs checking because the type enforces it.
`HostAssignment.satisfies` is a structure with `.producible` and `.withinBound`. `openVmHost` gives
every chip bound `1` except the input chip, which takes `OpenVmParams.maxInputInstances` — the
input stream really is pulled one chunk at a time.

The cost is that `instanceBound` bounds above only, so "this chip must be present" is no longer
expressible. That is free here: every `openVmHost` chip's `canProduce` holds of `0`, so omitting a
chip is the same run as instantiating it idle. It also removed `Host.outputSingleton` and the
`VmSat` argument to `VmAssignment.effects` (which now reads the output contribution with `headD 0`),
leaving `CanProduce vm e = ∃ a, VmSat vm a ∧ a.effects = e`.

## C. The host-abstraction TODO is backwards

*Status: acknowledged (2026-08-20); the `TODO(AO)` in `OpenVm.lean` that hoped otherwise is removed.*

**Mechanism.** The hope was that a host chip which "produces more things" still yields
a true theorem for the real host. It does not: the host appears on both sides of
`CanProduce_H(G') ⊆ CanProduce_H(G)`. Over-approximating gives
`real(G') ⊆ model(G') ⊆ model(G) ⊇ real(G)` — no conclusion; under-approximating fails symmetrically.

**Impact.** Host fidelity has to be exact, or the transfer needs a per-run simulation lemma. Several
chips are currently loose in one direction (memory init, the input chip) and tight in the other (the
output chip; address spaces `0` and `4`, which `memoryFinalizeHostChip` excludes, making any run that
touches them unsatisfiable).

## D. The configuration conditions are never instantiated, and they bind

*Status: open.*

**Mechanism.** `windowOk`/`budgetOk` are discharged "once when `P` is built", but no `OpenVmParams`
value exists in the repo. At BabyBear they are tight:

| `maxInstances` | `maxWindow` ≤ | `maxInteractions` ≤ |
| --- | --- | --- |
| 2²⁰ | 1918 | 1919 |
| 2²² | 478 | 479 |
| 2²³ | 238 | 239 |

**Impact.** A fused APC over a large basic block can plausibly exceed ~479 bus interactions, so
whether the hypotheses are satisfiable at real segment sizes is an open question, not bookkeeping.
The unexplained `+ 1`s (`TODO(AO): why the +1's?` on `Host.noTimeOverflow`) eat headroom nobody has
justified.

**Probe.** One concrete `example : OpenVmParams babyBear := …` at the sizes actually targeted.

## E. *Dropped (2026-08-20)*

Inheriting `OpenVmSemantics.lean`'s `accepts`/`maintainsInvariants`/`defaultBusMap` — including the
unmodelled program behind the PC lookup, and the host chips' hand-copied table predicates — is a
deliberate choice, not a defect. Recorded so it is not rediscovered as one.

## F. Three audited definitions with no consumer

*Status: open.*

`VmCompleteReplacement`, `VmEquivalent` and `PreservesDegree` are audited but reachable only from
`Validation.lean`'s sanity lemmas. No theorem constrains them, so a mistake there stays invisible
until the completeness half is attempted.

## Lower tier

* `Circuit.advancesClock` is the strongest clause of legality: it demands execution-bridge traffic on
  *every* algebraically-satisfying assignment and pins every memory access into `(base, base + d)`.
  The rank hypothesis of `Circuit.statefulSendsMaintain` is fine — extra hypotheses only weaken
  legality, and `Host.pinsRanks` supplies the fact globally.
* `Audit/OpenVmLegalAudit.lean`'s chips carry *constant* `t₀`/`t₁`/`pc`/`ptr`, whereas an exported APC
  has them as columns sharing one `from_timestamp`. Legality against a whole APC is untested.
* `inputHostChip` now sits on the execution bridge like a guest instruction
  (`InputRead.pcFrom`/`pcTo`/`d`, closing A2), but unlike `Circuit.advancesClock`, nothing pins its
  own memory accesses (`ptrTime`/`countTime`/`wordTimes`) inside `(base, base + d)` — the AssertLt
  discipline a real guest step's own algebra would have to supply. Harmless for anything currently
  proved (`Host.pinsRanks` only bounds guest ranks), but the input chip's own memory-timestamp
  story is still more permissive than a real `Rv32HintStoreAir`.
* `memoryInitHostChip` still allows arbitrary initial memory in address spaces `1`/`2`, with
  unbounded (even infinite) support: a segment's public inputs are an unobserved VM input (address
  space `3` is now pinned to `0` — see A1). Restricting address space `3` to memory init's own senders
  isn't available as a fix here: `MemoryBus.lean`'s `receiveThenSend` discipline means a guest's
  *first* write to a cell still needs an earlier record to receive, and only memory init runs before
  any guest instance, so a cell with no possible sender has no possible guest write either — the same
  mechanism A1's fix ran into. The principled fix, if this needs closing, is the same as A1's: make
  the initial memory image a `Host` field (or part of `VmEffect`), so `CanProduce` is relative to a
  fixed initial state rather than an existentially-quantified one.
