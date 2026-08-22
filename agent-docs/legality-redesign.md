# Making `Circuit.legalGuest` true of a real APC

*Supersedes `advances-clock-fix.md` (deleted). Background: finding G in
[`vm-spec-audit.md`](vm-spec-audit.md); the circuits in
`ApcOptimizer/VmSpec/Audit/RealApcLegality.lean`.*

`Circuit.advancesClock` is false of every real APC (finding G). The fix is not local to that
clause: it asserts two things a fused APC does not satisfy — that an instance is *one* instruction
step, and that its memory traffic lives inside that step's window — and the memory conjunct is
additionally doing an unadvertised second job. Separating the jobs lets the whole rank apparatus
leave the audited surface.

This file is the design, the evidence it holds against both APC stages, and the implementation
order.

## The idea: steps and offsets

A guest instance is a **sequence of instruction steps**. Each step is a bridge **arc** `(pcFrom,
base) → (pcTo, base + d)`. A fused APC has one arc per fused instruction; after powdr substitutes
the intermediate timestamps away, the arcs cancel into one. Both are the same clause with different
witnesses.

Each memory interaction sits at an integer offset `k` from *its own arc's* `base`:

```
      base - L                     base                  base + d
         |------------ lookback ------|------ step ------|
         k = -L                     k = 0               k = d
```

`L` is the furthest back an access may reach — `2 ^ openVmTimestampBits`, because `AssertLtSubAir`
range-checks `t - t_prev - 1` to that many bits. That is the same constant as the timestamp ceiling
`B`, and not by accident: the gadget is sized so any legitimate difference fits, which is why
merging accesses can never push a distance out of its range (both endpoints stay in `[0, B)`).

Offsets are integers, so comparing them is wraparound-free. Everything below is stated against
them, and that is what makes the clauses per-chip checkable at all: the timestamps themselves are
`ZMod p` elements whose `.val` order is not what the AIR constrains.

## The clause

The arcs are shared between the bridge condition, the memory placement and the send obligation, so
they live in one existential. `Circuit.legalGuest` becomes `{ sendOnly, polarity, stepLayout,
size }`.

```lean
structure StepLayout (p) (c : Circuit p) (asg : ChipAssignment p) where
  arcs  : List (Arc p)                                   -- pcFrom, pcTo, base, d
  arcOf : Fin c.busInteractions.length → Fin arcs.length -- for active stateful interactions
  off   : Fin c.busInteractions.length → ℤ               -- for active memory interactions

def Circuit.hasStepLayout (c) (r) (maxWindow maxLookback) : Prop :=
  ∀ asg, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    ∃ S : StepLayout p c asg, …the five conditions below…
```

Gated on `satisfiesStateless`, which is forced: in `apc2105000Opt` the lt-constraint survives
*only* as a range-check payload (`15360 * (prev_ts + decomp₀ + 1 - (base + δ))`, and
`15360 = -1/2^17 mod p`), so nothing about a receive's offset is derivable from the algebraic
constraints alone.

### (1) The bridge decomposes into arcs

```lean
(∀ α ∈ S.arcs, 0 < α.d) ∧ (S.arcs.map (·.d)).sum < maxWindow ∧
  ∀ m, m.1 = r.execBusId → c.allEffects asg m = (S.arcs.map (·.effect)).sum m
```

Stated on the **sum**, not on the exact net. That is what makes one witness serve every
assignment: where the intermediate arcs happen to chain, they cancel *inside the sum*
automatically, and where they don't, they stand as separate arcs. `Σ d_α < maxWindow` keeps the
per-instance clock budget exactly as `Host.noTimeOverflow` assumes, so no configuration condition
moves.

### (2) Every memory interaction sits in its arc's window

```lean
∀ i, memoryActive i →
  -maxLookback ≤ S.off i ∧ S.off i < (S.arcs.get (S.arcOf i)).d ∧
  r.getTimestamp (msg i) = (S.arcs.get (S.arcOf i)).base + (S.off i : ZMod p)
```

The anti-wraparound fact. It replaces the old memory conjunct and covers receives, which the old
one got wrong (it demanded they sit *inside* the step; they sit before it).

### (3) A send dominates what precedes it in its own step

```lean
∀ i j, j < i → sameBus j i → S.arcOf j = S.arcOf i → active j →
  (msg i).multiplicity = 1 → S.off j < S.off i
```

Only *sends* are constrained: a receive may sit at a larger offset than an earlier send, and in
`apc2105000Opt` one does. Same-arc scoping is what makes this true of an unoptimized APC, whose
arcs are not ordered relative to each other by anything algebraic. Same-bus scoping is also
load-bearing: the bridge send is the last stateful interaction in the list, after every memory
send.

### (4) The net memory traffic decomposes into ordered accesses

```lean
∃ accs : List (MemAccess p),
  (∀ a ∈ accs, a.sameAddress ∧ a.arc-local ∧ a.kRecv < a.kSend) ∧
  ∀ m, m.1 = r.memBusId → c.allEffects asg m = (accs.map (·.effect)).sum m
```

An access is `-1` at `(a, v_before, base_α + k_r)` and `+1` at `(a, v_after, base_α + k_s)` — same
address, same arc, `k_r < k_s`. This is memory consistency's local half; with bus balance it is the
standard offline-memory-checking chain, one per address.

Again stated on the sum, and again that is the point: the *natural* per-instruction decomposition
works on every assignment. A record that a later access cancels contributes `+1` and `-1` to the
same message inside the sum, so cross-arc pairings never have to be constructed — which matters,
because comparing offsets across arcs is exactly what a chip cannot do.

### (5) Sends maintain, positionally

```lean
∀ i, r.isStateful (bi i).busId = true → (msg i).multiplicity = 1 →
  (∀ j < i, sameBus j i → S.arcOf j = S.arcOf i → active j → r.payloadOk (msg j)) →
    r.payloadOk (msg i)
```

No rank, no rank bound, no `ranksBounded` hypothesis. A chip justifies a send from what it already
touched *earlier in its own list, on the same bus, in the same step* — which is how real chips
work: a memory send echoes a receive that precedes it.

Cross-instruction data flow inside a fused APC does not need more: it goes through *memory*, and a
receive's `payloadOk` comes from the global induction — which may perfectly well find the sender to
be this same chip at a lower rank — not from the chip's own hypothesis.

### Unchanged

`statelessSendOnly`, `statefulPolarity`, `size`. Both multiplicity clauses are already proved of
both APC stages by `Audit/SendOnlyPolarity.lean`'s checker.

## What leaves the audited surface

`Circuit.legalGuest` loses its `rank` and `rankBound` parameters. `Circuit.ranksBounded` and
`Circuit.lowerRanksMaintain` leave `Legal.lean` — the first moves to `Implementation/`, the second
disappears. `RankModel` becomes something no audited definition mentions, which is what its own
docstring already wishes were true. The `TODO(AO)` on `statefulSendsMaintain` — the clause whose
*location* was the worry — goes with it.

Chips stop comparing timestamps. `readEcho_timestamps_increase` and its wraparound case analysis
vanish from chip-level obligations; the wraparound reasoning happens once, in condition (2), not
once per send.

## What `Implementation/` must do instead

The rank survives, as the induction's well-founded order and nothing else:

```
rank m = ((getTimestamp m) + S).val,   S = L,   bound = B + S = 2 ^ 30
```

The shift is what makes rank monotone in offset. With an arc's `base = 1 + T` (the bridge walk) and
`k ∈ [-L, d)`:

```
rank = 1 + T + k + S ∈ [1, B + S)      no wraparound, since B + S = 2^30 < p
```

`1 + T + k ≥ 1 - L` needs `S ≥ L`; `1 + T + k < B` follows from `k < d` and
`1 + T + d ≤ finalTimestamp.val < B`. `2^30 < p` is exactly the headroom OpenVM already reserves for
`AssertLtSubAir`, so no new arithmetic condition on `p` is needed.

Consequences:

- **`Chain.lean`'s arc index generalizes.** `BridgeArc` is already the right notion; today it is
  1:1 with instances, and it becomes a list per instance. The chain argument itself is unchanged in
  shape — it already handles "one chip's send is another chip's receive, cancelling in the net",
  and an instance's internal arcs are the same phenomenon with a different index.
- **Cycles are still excluded.** Stating (1) on the sum does let a zero-net chip claim two arcs
  forming a cycle, which today's "exactly one receive, exactly one send" rules out outright. But
  `0 < d_α` plus the budget is precisely what `Chain.lean` already uses against cycles: a cycle's
  total advance is positive yet must sum to zero, and the budget keeps the total strictly between
  `0` and `p`.
- **`Host.pinsRanks` / `VmAssignment.withinRankBound` are no longer needed as bounds.** Their only
  consumer was the `ranksBounded` hypothesis of `sendsMaintain` (`Realizes.lean:269`, `:315`). The
  bridge walk still runs; its conclusion becomes *offset order implies rank order, within an arc*.
- **`maintains_of_stateful_active` supplies (5)'s hypothesis** from its own induction hypothesis:
  for `j < i` on the same bus in the same arc, `off j < off i` by (3), hence
  `rank (msg j) < rank (msg i)` by monotonicity, hence the IH applies.

*Lean-shape detail to settle at implementation:* `arcOf` is meaningful only for active stateful
interactions and `off` only for active memory ones; whether that is `Option`-valued, a partial
function on a subtype, or junk-valued with the conditions guarding it is a presentation choice with
no content.

## Evidence

### `apc2105000Opt` (stage `039_trivial_simp`) — one arc

Exactly two bus-`0` interactions: `mult -1, [2105000, from_state__timestamp_0]` and
`mult 1, [2105016 - 192·cmp_result_3, from_state__timestamp_0 + 11]`. One arc, `d = 11`,
`Σ d = 11 < maxWindow`. The two messages are distinct (`11 ≠ 0` in `ZMod p`), and no other
interaction carries bus `0`, so the sum matches the net.

Ten memory interactions, offsets read off each receive's own gadget (`n = decomp₀ + 2^17·decomp₁ ≥
0`, and `n < 2^29 = L` from the two range checks):

| idx | kind | addr | offset |
| --- | --- | --- | --- |
| 0 | recv | 40 | `-1 - n` |
| 1 | **send** | 40 | `0` |
| 2 | recv | 52 | `1 - n` |
| 4 | recv | 44 | `2 - n` |
| 5 | recv | 56 | `4 - n` |
| 6 | **send** | 56 | `5` |
| 8 | **send** | 52 | `6` |
| 9 | **send** | 44 | `9` |
| 10 | recv | (1,0) | `9 - n` |
| 11 | **send** | (1,0) | `10` |

- **(2)** every offset is in `[-L, 11)`.
- **(3)** each send dominates every earlier row: `0 > -1-n`; `5 > 0, 1-n, 2-n, 4-n`; `6 > 5`;
  `9 > 6`; `10 > 9, 9-n`. The receive at idx 2 sits *after* the send at idx 1 with a possibly
  larger offset — which is why (3) constrains sends only.
- **(4)** the five same-address pairs, `k_r < k_s` in each: `(-1-n, 0)`, `(1-n, 6)`, `(2-n, 9)`,
  `(4-n, 5)`, `(9-n, 10)`. The last two are tight — those are the addresses powdr did *not* merge,
  where `k_s - k_r` is exactly the original gadget's distance.

  The decomposition is well defined: all ten messages are pairwise distinct. Cross-address is
  immediate (literal pointers 40/44/52/56/0); within an address the receive and send differ in
  timestamp, and the gadget rules out coincidence — at address 40 they carry the *same* data
  `a__*_0`, so they would collapse if `prev_ts = base`, but `prev_ts = base - 1 - n` and
  `1 + n ≠ 0` since `n < 2^29`.

### `apc2105000Unopt` (stage `000_unopt`) — four arcs

Eight bus-`0` interactions: `(pc_i, ts_i) → (pc_i + 4, ts_i + 3)` for `i = 0,1,2` and
`(pc_3, ts_3) → (pc_3 + cmp·imm + (1-cmp)·4, ts_3 + 2)`. The **pcs are pinned to literals** —
2105000/4/8/12, consecutive by 4 — so on the pc side the arcs already chain. The **timestamps are
not**: each `from_state__timestamp_i` appears in exactly three constraints, and all three are its
own instruction's lt gadgets.

Four arcs with `d = 3, 3, 3, 2`, so `Σ d = 11` — the same total the optimized APC reaches in one
arc, and the same `maxWindow > 11` serves both. Where an assignment happens to chain the
timestamps, arcs 0…3 cancel inside the sum and the net is the single 11-tick arc; where it does
not, the four stand separately. The witness is the same either way.

Its 22 memory interactions place three per arc (two reads and a write, offsets `0, 1, 2`; arc 3 has
two reads at `0, 1`), each receive at `δ - 1 - n` for its own gadget's `δ`. (3) and (4) hold
within each arc by the same reading as above.

### Not yet checked: (5) for `apc2105000Opt`

Four of the five sends are easy — three echo a receive that precedes them (`a__*_0` from idx 0,
`a__*_1` from idx 4), and idx 11 sends literal zeros. The fifth (idx 9,
`[1, 44, a__0_2, 0, 0, 0, base+9]`) needs `a__0_2` to be a byte, which is reachable only through
the bitwise lookup at idx 7 — `[a__0_0, 3, a__0_0 + 3 - 2·a__0_2, 1]`, op `1`, i.e. `z = x XOR y`,
giving `a__0_2 = a__0_0 AND 3`. That is a real proof against `ApcOptimizer.OpenVM.accepts`'s
bitwise arm, and it is the open question this design does not settle.

## Legality preservation

Condition (4) is stated on the *net* memory effect, and `Circuit.isSoundReplacementOf` compares
exactly that (`Circuit.sideEffects`). So a predicate on `(sideEffects, arcs)` transports through
soundness verbatim: pull the assignment back, apply the original's legality, and the decomposition
is of the same net. That immunises (4) against the mechanism behind every counterexample in
[`legality-preservation.md`](legality-preservation.md), all of which split one interaction into
several with the same net. Condition (1) is on the bridge net and transports for the same reason.

Conditions (2), (3) and (5) are per-interaction and do not; that is no worse than today. (3)
additionally depends on list *order*, so a pass that appends a send whose offset is not maximal
breaks it. Restoring it is a sort, and a decidable checker in the style of
`Audit/SendOnlyPolarity.lean` can verify it on a pass's output.

The deeper win is that both APC stages now satisfy the *same* clause with the *same* shape of
witness, so powdr's substitution pass — the one that chains the timestamps and collapses four arcs
into one — becomes legality-**preserving** rather than legality-**creating**. That is the
relationship `PreservesLegality` needs, and `openVm_vmSoundReplacement` needs it in both
directions: its `hLegal` quantifies over `G ++ G'`, the optimizer's input *and* its output.

## Status per circuit after this change

| | `Unopt` (000) | `Opt` (039) | `Gated` (040) |
| --- | --- | --- | --- |
| `statelessSendOnly` / `statefulPolarity` | proved | proved | true, out of checker reach |
| `hasStepLayout` (1)–(4) | **true**, four arcs | **true**, one arc | **false** (G1) |
| `hasStepLayout` (5) | ? | open (the `a__0_2` question) | ? |

### The G2 correction

Finding G files G2 — "nothing algebraic chains the fused instructions" — alongside G1 as a case of
`algebraicallyForces` quantifying over assignments the bus semantics would reject, with the implied
fix of stating legality on `Circuit.satisfies`. **That is the wrong mechanism.** `accepts` for the
execution bridge is `True` (`OpenVmSemantics.lean`), so no per-chip acceptance test distinguishes a
chained assignment from an unchained one. What rules the unchained one out is *global bus balance*,
which a per-chip clause may not assume.

G2 is not a defect of the circuit at all. It is the clause asserting that an instance is one
instruction step, when a fused APC is four. Arcs are the fix, and G2 closes with them.

**G1 is untouched and does stem from that mechanism**: stage 040's `is_valid` padding row makes the
all-zero assignment algebraically satisfying, so no bridge witness exists at all. Whether legality
is stated on `satisfiesAlgebraic`, on `Circuit.satisfies`, or gated on an activity flag is a
separate decision, and the natural next piece of work.

## Deliberately out of scope

- **Deriving** global memory consistency from (4). The clause is the local half; the chain argument
  per address is a further, larger piece of work, structurally the same as `Chain.lean`'s bridge
  walk. Nothing in the current theorem needs it — `VmEquivalent` is a relative statement, and the
  only global invariant this development establishes is `payloadOk`.
- The G1 decision above.

## Implementation status

Landed (`7e8e37c`, `585de62`, `4911a26`, `b1bcef6`); `lake build` clean and
`Scripts/check-proof-integrity.sh` passing at each.

1. ✅ **Arcs in the chain.** `ClockStep` carries a list of arcs; `BridgeArc` indexes
   (instance, step). `Chain.lean` needed **no** change — it was already abstract in the arc index.
   The step count needs no new configuration field: each arc advances by at least one tick and
   they total less than `maxWindow`, so `windowOk` still covers the arc count.
2. ✅ **Arcs in the clause**, stated on the sum of arc effects.
3. ✅ **`StepLayout`.** `Circuit.legalGuest` is `{ sendOnly, polarity, stepLayout, size }`; `rank`,
   `rankBound`, `Circuit.ranksBounded` and `Circuit.lowerRanksMaintain` are off the audited
   surface. `Host.pinsRanks` became `Host.ordersRanks`, `openVmRank` gained the shift, and the
   audit chips were reworked (`stepChip` full layout, `earlyEchoChip` negative, `freshWriteStepChip`
   for the lookup-justified send).

Not started:

4. **The real-APC theorems.** `apc2105000Opt` (one arc, `d = 11`) and `apc2105000Unopt` (four arcs,
   `d = 3,3,3,2`) satisfying the bridge condition, then the full placement — the five gadget
   derivations, driven off `satisfiesStateless`. Evidence and constants are tabulated above. Replace
   the prose in `Audit/RealApcLegality.lean`'s header table as they land.
5. **Finding G in `vm-spec-audit.md`**: record the G2 correction (see below), that G1's padding-row
   half is closed, and that the memory half (G3) is what the placement closes. It also mis-names
   `apc2105000Gated_not_advancesClock` as `apc2105000Opt_not_advancesClock`; that theorem is now
   `apc2105000Gated_padding_bridge`.

### Three decisions taken while implementing, not in the design above

- **`openVmTimestamp` reads the execution bridge too** (payload index `1`, against memory's `6`).
  Without it, `ordered` would have to be scoped by step *and bus*, and then a bridge send could not
  be ordered against anything. With it, a step's bridge receive sits at offset `0`, its memory
  accesses in between, and its bridge send at offset `d`, all on one scale — so `ordered` is scoped
  by step alone.
- **`ordered` requires the *send* to be stateful.** Otherwise a stateless lookup at multiplicity `1`
  would demand an ordering against the step's memory interactions, which is false of every real
  chip (`checkedStepChip` fails it immediately).
- **`OpenVmParams.rankWindowOk : openVmRankBound < p`** is a new configuration field. The shift
  needs it and nothing else implies it; it is OpenVM's own `2 ^ (timestamp_max_bits + 1) < p`, the
  condition that caps `timestamp_max_bits` at `29` for BabyBear.

### Proof idioms that carried the audit chips

Worth reusing for the real-APC theorems:

- `ClockArc.net_singleton` (in `Legal.lean`) reduces a one-step chip's bridge condition to the
  familiar receive / send / nothing-else triple.
- `place := fun i => (0, (i.val : ℤ))` — offsets *are* list positions — discharges `ordered` by
  `simpa using Fin.lt_def.mp hji`, and works whenever a chip's stateful interactions are listed in
  time order at consecutive offsets. A real APC needs a real table instead (its offsets are
  `0, 5, 6, 9, 10` and its receives are `δ - 1 - n`), but `ordered` stays a numeric check.
- `fin_cases i` on the interaction index, then one bullet per interaction, is how `placed`,
  `ordered` and `sendsOk` are discharged chip by chip.

## Done when

1. `lake build` clean, no warnings.
2. `bash Scripts/check-proof-integrity.sh` passes (new lemma names go in the `[ignore]` section of
   `Scripts/unused-theorems.txt` — the `VmSpec/` tree is unreachable from the correctness roots).
3. Both `apc2105000Opt` and `apc2105000Unopt` satisfy `hasStepLayout` (1)–(4), proved, with the
   header table in `Audit/RealApcLegality.lean` updated to match.
