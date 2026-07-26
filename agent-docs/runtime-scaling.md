# Why the optimizer is superlinear in circuit size

Session note (2026-07-26), triggered by powdr's Rust-vs-Lean timing comparison
(`apc-timing/apc_optimizer_timing.json` on powdr's `apc-optimizer-timing-comparison` branch:
20 115 APCs across 9 guest programs, both optimizers timed on the same machine). Every number below
was measured on a 4-core container against **`ff15446`** (post PRs #205–#210), which is also the
commit the reference JSON was generated from. #211 (reencode's per-candidate whole-system scans,
184 → 97 s on sha256) landed while this was being measured; §7 re-measures on top of it. Absolute
times on this container run ~2× the 48-core box used for the `ideas.md` numbers, and run-to-run
variance is ±15 % — read exponents and shares, not seconds.

**Headline: the Lean optimizer's wall time grows as ~N^1.5–1.8 in circuit size; powdr's Rust
optimizer is ~N^1.0.** On small APCs Lean is *faster* than Rust; at ~170k columns it is ~6× slower.
The growth is **not** the fixpoint needing more rounds — it is per-pass cost, and it comes from one
recurring shape: **Θ(system) work per optimization candidate**, with Θ(N) candidates.

This file records the cross-implementation measurement, a controlled scaling experiment that
isolates the effect, and the per-pass attribution. It complements the runtime section of
[`ideas.md`](ideas.md), which holds the ranked fix list; findings here are cross-referenced to its
`R*` entries, and the three previously-unlisted quadratic sites in §4 were added there as R13–R15.

## 1. The cross-implementation gap

Median wall time **per input variable**, bucketed by circuit size, from the reference JSON:

| input variables | APCs | Rust µs/var | Lean µs/var | Lean / Rust |
| --- | --- | --- | --- | --- |
| < 500 | 15056 | 1248 | 923 | 0.74 |
| 500–1k | 3064 | 1833 | 992 | 0.54 |
| 1k–2k | 1400 | 1668 | 1120 | 0.67 |
| 2k–4k | 402 | 1907 | 1215 | 0.64 |
| 4k–8k | 159 | 4170 | 1573 | 0.38 |
| 8k–16k | 13 | 2049 | 2116 | 1.03 |
| 16k–32k | 12 | 1579 | 3631 | 2.30 |
| 32k–64k | 7 | 1160 | 3065 | 2.64 |
| 64k–300k | 2 | 679 | 4083 | **6.01** |

Rust's per-variable cost is flat-to-declining across four orders of magnitude; Lean's grows 4.4×.
A log-log fit over the APCs with ≥ 5000 variables gives exponent **1.26 for Lean** against **0.42
for Rust** (Rust's sub-linear fit is an artifact of noise in the mid range — the honest reading is
"flat" — while Lean's is a real upward trend). The crossover is around 8k–10k variables.

The two data points in the top bucket are this repo's own stress benchmarks: `sha256`
(168 915 vars) and the largest `openvm-eth` block (170 361 vars).

## 2. The controlled experiment: k disjoint copies

Real APCs differ in shape, so the scaling was re-measured on a synthetic family: `k` copies of
`openvm-eth/apc_005` (5406 vars, 4652 constraints, 2253 interactions), copy `c` renaming every
variable `<name>@<id>` to `<name>@<id + c·stride>` so the copies share nothing. A linear optimizer
must take exactly `k ×` the single-copy time on this input.

| k | vars | total | vs. linear |
| --- | --- | --- | --- |
| 1 | 5 406 | 8.0 s | 1.0× |
| 2 | 10 812 | 23.3 s | 1.5× |
| 3 | 16 218 | 49.2 s | 2.1× |
| 4 | 21 624 | 91.5 s | 2.9× |
| 6 | 32 436 | 164.8 s | 3.5× |
| 8 | 43 248 | 315.8 s | **5.0×** |

Exponent **1.77**. Cleanup iterations: 5 at k=1, 6 at k=8 — so on this input the growth is
*entirely* per-pass cost, not extra fixpoint rounds. Per-pass exponents (entries ≥ 150 ms at k=8):

| pass | k=1 (ms) | k=8 (ms) | exponent | vs. linear |
| --- | --- | --- | --- | --- |
| `reencode` | 2418 | 256950 | **2.24** | 13.3× |
| `subsumedRange` | 28 | 2977 | **2.24** | 13.3× |
| `tupleRange` | 5 | 391 | **2.10** | 9.8× |
| `busPairCancel` | 196 | 6340 | **1.67** | 4.0× |
| `flagUnify` | 110 | 2732 | 1.54 | 3.1× |
| `flagFold` | 420 | 9577 | 1.50 | 2.9× |
| `busUnify` | 267 | 3656 | 1.26 | 1.7× |
| `gauss` | 549 | 5962 | 1.15 | 1.4× |
| everything else | — | — | 1.08–1.28 | 1.2–1.8× |

`domainFold` is omitted because it is not monotone here: 1.7 s → 26.0 s over k=1…4 (exponent ≈ 2.0
between k=2 and k=3, both on the *indexed* path), then collapsing to 1.4 s / 2.1 s at k=6 / k=8
once `reencode` has grown large enough to consume the same candidate groups first. See the ablation
below.

The 1.08–1.28 band covers passes that are linear by construction (`encode`, `constFold`, `dedup`,
`tautoBus`): allocation and locality cost from a larger working set, consistent with the
"budget is memory traffic, not arithmetic" finding in `ideas.md`. It is the floor to beat, not a
bug.

Real-circuit ladders agree on the shape: a 12-circuit ladder from 852 to 27 521 variables
(`openvm-eth`, `wasm-eth`, `keccak`) fits exponent **1.48**; `keccak` → `sha256` (6.14× the
variables) costs 26.0× the time, exponent **1.79**.

## 3. Where the time goes, and the ablation

`sha256` (168 915 vars; 1046.7 s on this 4-core container — slower than the 48-core box used for
the #205–#210 numbers in `ideas.md`, but the same ranking):

| pass | ms | share |
| --- | --- | --- |
| `reencode` | 399 276 | 38.1 % |
| `busPairCancel` | 186 121 | 17.8 % |
| `busUnify` | 117 529 | 11.2 % |
| `gauss` | 48 903 | 4.7 % |
| `domainBatch` | 47 700 | 4.6 % |
| `bytePack` | 33 643 | 3.2 % |
| `flagFold` | 31 717 | 3.0 % |
| rest (30 passes) | 181 855 | 17.4 % |

`keccak` (27 521 vars, 40.3 s): `busUnify` 21 %, `domainFold` 13 %, `reencode` 10 %, `gauss` 9.5 %,
`busPairCancel` 9 %, `domainBatch` 6.4 %. Cycle 0 alone is 36 % of the sha256 run and cycles 0–2
are 68 %, matching the earlier per-cycle finding.

gdb stack sampling of the live sha256 process (260 stacks, `thread apply all bt` — the work runs on
a Lean worker thread) puts the innermost frames exactly where §4 predicts:
`denseDegPreReject → List.any → DenseExpr.sharesVarIn` under `denseReencodeStep`/`denseReencodeLoop`,
and `denseCheckPair → denseAddrTwoRootNeq → densePtrReductions` under `denseCollectForBus`
(`busUnify`) and `denseFindCancelGoIdx` (`busPairCancel`).

### Ablation: the cost is shared, not owned by one pass

Dropping `reencode` from `cleanupPasses` and re-running the replica ladder speeds up **nothing**
(k=4: 90.1 s without vs 91.5 s with; k=1 and k=2 are slightly *slower* without it). The 44 s
`reencode` spent at k=4 reappears as `domainFold` growing 26.0 s → 57.1 s, and the output is worse
(7546 vs 5498 variables).

The reason is that both passes enumerate the *same* candidate shape — 2-to-8-variable groups whose
variables are pinned by single-variable constraints (`denseTargetsV` in `DomainFoldRuntime.lean`
vs. `reencode`'s `targets` in `Reencode.lean`, identical predicates) — and each spends Θ(system)
per group. With `reencode` gone the groups survive and `domainFold` re-processes them every cycle.

**So the target is the pattern, not one pass.** Whoever consumes the candidate groups pays
Θ(groups × system) unless the per-group work is served from an index. Indexing `reencode` alone
should therefore move part of the cost rather than remove it — #211 did exactly that indexing, so
§7 is the test of this prediction.

## 4. The pattern, and three sites not yet in `ideas.md`

Three recurring shapes produce all of the measured superlinearity:

1. **Per-candidate whole-system scan** — a gate or certificate walks every constraint and every
   interaction, once per candidate (`reencode`, `domainFold`, and the three sites below).
2. **Per-candidate whole-interval scan** — for stateful buses, a matched send/receive pair's
   certificate quantifies over every interaction *between* them, and for `busPairCancel` over the
   entire *prefix* before the send. Cost is Σ over pairs of the gap length: Θ(N²) when matched
   pairs are far apart, which is precisely what a long basic block like sha256/keccak looks like.
   Already tracked as R8 (`busPairCancel`) and R10 (`busUnify`).
3. **Find-first-then-restart drains** — "find the first rewritable pair from the head, rewrite,
   repeat" re-scans the prefix and rebuilds `revPre.reverse` for every rewrite: Θ(rewrites × N).

Sites not currently listed in `ideas.md`:

### 4a. `subsumedRange` / `subsumedCheck` — exponent 2.24

`SubsumedCheck.lean:53` `denseSubsumedDropKeep` calls `denseFindVarBound`
(`RootPairUnify.lean:92`) — a linear scan of the whole `base` interaction list — once per
recognized check, so the pass is Θ(checks × interactions). Only 9.0 s of the sha256 run today
(coda passes run once, on the shrunk system), but it is the cleanest quadratic in the tree and
`RootPairUnify.lean` already has the indexed twin to reuse: `denseAnyVarBoundIdx`, served from the
per-variable `witsOf` map built by #209. Cheap, and the drop is untrusted-then-rechecked, so no new
soundness proof.

### 4b. `bytePack` / `tupleRange` — find-first-then-restart drains

`ByteCheckPack.lean:102` `denseFindGo` (with `denseFindSecond` at :88) is driven by
`DenseNativeStep.drain` (`Proofs/ByteCheckPack.lean:598`) with fuel = interaction count: each
packed pair restarts the scan at the head of the list and materializes `revPre.reverse`.
`TupleRange.lean:98`/`:104` has the identical shape. Measured 33.6 s (`bytePack`) + 11.7 s
(`bytePackLate`) + 5.7 s (`tupleRange`) = 5 % of the sha256 run, exponent 2.10 for `tupleRange` on
the replica ladder. A resume cursor (`denseCancelLoop`'s `resumeIdx`/`resumePos` pattern) is exactly
sound here: the step's output is `pre ++ pairCheck :: mid ++ post`, `pre` is unchanged and by
construction holds no recognized single-value check, and the emitted `.pair` check is not one
either (`denseSvCheck?` only fires for single-operand shapes) — so resuming at `|pre| + 1` visits
the same candidates in the same order and keeps the output byte-identical.

### 4c. `flagUnify` — exponent 1.54

`FlagUnify.lean:34` `denseFuPairData?` resolves each joint variable's domain with
`denseFindDomainAlg domCs v` (`DomainFold.lean:43`), a full constraint-list scan per variable per
matched pair. `RootPairUnify.lean` already tabulates exactly this once per invocation
(`denseFindDomainMap`, #209) — share it. Its `seen` buckets are also never pruned, so a match key
shared by many interactions is re-certified against every later candidate.

### Already-tracked sites, with this session's numbers attached

- `reencode` (R3, R13): `denseDegPreReject` was `d.algebraicConstraints.any … ||
  d.busInteractions.any …` per candidate group, ahead of the cheap gates — the single hottest loop
  in the optimizer at sha scale in every measurement above, and the frame gdb landed in. It had been
  *added* (entry 113) to avoid the far worse freshness-scan-plus-`reencodeOut` on the 1276-of-1276
  degree-rejected groups: it cut the constant but kept the Θ(targets × system) shape. **#211 / entry
  142 indexed it** (a thunked whole-system posting index, rebuilt on accept) with no soundness proof
  needed, since the gate is untrusted (both branches sound) and only items sharing a variable with
  `xs` can make the `any` true. Still open: `denseCheckReencode` (`Reencode.lean:135`) — its
  `denseCoveredCsOf` filter and its explicitly-`O(bits × system)` freshness scan are the same shape.
- `domainFold` (R3): the direct path (`denseFoldLoopDirectV`, `DomainFoldRuntime.lean:170`) runs
  `denseSystemHasFoldableWV` over the whole system per target, and is taken below
  `domainFoldIndexThreshold = 8192` constraints — which includes big circuits *mid-fixpoint*
  (keccak 28 627 → 4 529 constraints by cycle 2; sha256 199 740 → 3 194 by cycle 6), so both spend
  their tail cycles there. Note entry 107's warning: the analogous gate in `reencode` was measured
  1.19× *worse* when retired on dense openvm-eth blocks, so any change here needs a same-runner
  A/B, not just a keccak/sha number. Separately, the indexed path measured exponent ≈ 2.0 between
  k=2 and k=3 on the replica ladder — the per-target cost is the union of the `xs` variables' index
  buckets and group variables are typically flags with very long buckets. Worth re-measuring
  directly before acting on.
- `busPairCancel` (R8): `BusPairCancel.lean:207` `denseShieldScanSeg … arr alive 0 i` is a full
  live-prefix scan per candidate send, and `:205` `denseLiveAllSeg … (i+1) (j-i-1)` the
  between-region scan. 17.8 % of sha256 here (89.5 s / ~16 % on the 48-core box post-#210) — the
  R8 design (b) sweep remains the fix.
- `busUnify` (R10): `denseCheckPair` (`BusUnify.lean:82`) re-verifies `mid.all` for each candidate
  the sweep proposed, and `denseEmitCand` (`:159`) materializes `w.revPre.reverse` — a fresh copy
  of the whole prefix — per emitted candidate, even though `denseCollectForBus` (`:248`) never
  reads `pre`/`post` (they exist only so the positional split can be stated). Making those two
  fields lazy or position-only removes Θ(N) per candidate without touching the sweep's decisions,
  which R10 correctly insists must stay bit-identical.

## 5. Why Rust does not have this

`powdr_autoprecompiles::memory_optimizer::redundant_memory_interactions_indices` is a **single
left-to-right sweep** over the bus interactions holding a `HashMap<Address, MemoryContent>` of live
sends: a receive consumes the entry for its address and emits the data/timestamp equalities; a send
evicts only entries it cannot prove disjoint. Nothing is re-verified against the interval between a
send and its receive, and one sweep's drops are applied in one batch. The surrounding
`optimize_rust` loop wraps everything in an `IndexedConstraintSystem`, so per-variable lookups are
O(1) by construction.

The Lean code *has* that sweep — `denseSweepGo` mirrors it closely — but then re-verifies each
candidate it proposed, because that is the form the machine-checked certificate takes. The extra
cost is not sloppiness in the port: it is the shape of the proof obligation. Making it linear means
proving that the sweep's invariant *implies* the per-pair conditions, rather than re-deriving each
pair's conditions from the raw list. That is the standing R8/R10 design, and it is the structural
difference to close if the goal is Rust-comparable scaling rather than a better constant.

The candidate-group family (§3 ablation) has an easier answer: those gates are untrusted, so
indexing them needs no proof — only the discipline of keeping the index complete across accepts.

## 6. Reproducing

```bash
# per-pass attribution for one circuit
lake exe apc-optimizer profile Benchmarks/OpenVM/keccak/apc_001_pckeccak.json.gz

# runtime across a benchmark set, serial, with per-pass totals and A/B against a baseline
Benchmarks/runtime_bench.py --n 20 --repeat 3 --json out.json
```

Disjoint-replica scaling input: emit `k` copies of one APC's `machine.constraints` and
`machine.bus_interactions`, renaming every `<name>@<id>` in copy `c` to `<name>@<id + c·stride>`
(`stride` = max id + 1), keeping `bus_map` and setting `next_free_id = k·stride`. The parser reads
only those keys. A linear optimizer takes `k ×` the single-copy time; anything above that is the
per-pass superlinearity, with the fixpoint's round count held fixed.

Stack sampling a long run (no `perf` in this container; the optimizer runs on a Lean worker
thread, so `thread apply all` is required, and `bt -N` gives the outermost frames that identify the
pass):

```bash
gdb -p <pid> -batch -ex "thread apply all bt 40" -ex "thread apply all bt -8"
```

Sampling inflates the sampled run (~30 %); use it for attribution, not for timings.
