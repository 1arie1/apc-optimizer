# Fixing `Circuit.advancesClock`

Two changes, very different sizes. Do the first on its own; the second is a design change worth
reviewing before it lands. Background and evidence: finding G in
[`vm-spec-audit.md`](vm-spec-audit.md), and the imported circuits in
`ApcOptimizer/VmSpec/Audit/RealApcLegality.lean`.

## Why

`Circuit.advancesClock` ([`ApcOptimizer/VmSpec/Legal.lean`](../ApcOptimizer/VmSpec/Legal.lean), the
last of `Circuit.legalGuest`'s clauses) requires of every guest chip:

> When this chip runs, it performs one instruction step. It takes the CPU from `(pc, t)` to
> `(pc', t + d)`, and every memory access it makes happens at some time strictly between `t` and
> `t + d`.

A memory access here is **two** bus messages, not one:

* a **receive** — "at time 900, address 40 held X"
* a **send** — "at time 1005, address 40 now holds Y"

The send is this instruction writing. The receive names the record it is replacing, and its
timestamp — 900 — is whenever some *earlier* instruction last touched that address. It is not in
this instruction's window; it is before it.

So the clause is false of real chips twice over. In the imported APC (window `t … t+11`) the sends
land at `t+0, t+5, t+6, t+9, t+10` — the first one fails "strictly after `t`" — and the receives
land at `..._prev_timestamp_...` columns that are outside the window entirely.

## Change 1 — allow a memory access at exactly `base`

*Small, free, no design content.*

The clause's `∃ δ : ℕ, 0 < δ ∧ δ < d ∧ …` becomes `∃ δ : ℕ, δ < d ∧ …`. This weakens a hypothesis
of `legalGuest`, so it can only make the VM theorem apply to more chips.

Sites, in dependency order:

1. `ApcOptimizer/VmSpec/Legal.lean` — `Circuit.advancesClock`, the memory conjunct. Drop `0 < δ ∧`.
   Update the surrounding doc comment: the whitepaper's `t_from < t_{i,j} < t_to` is the
   idealization; real executors take their first access at `t_from` itself.
2. `ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean` — the `mem` field of `ClockStep`
   (~line 58). Same edit. `clockStep_nonempty` just below passes the conjunct through unchanged and
   needs no edit.
3. `ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean`, in `openVmHost_pinsRanks` (~line 594):
   `obtain ⟨δ, hδpos, hδlt, hδeq⟩ := (S ⟨t, j⟩).mem …` loses `hδpos`. **Checked: the closing
   `omega` does not use it** — it runs on `hδlt` plus `1 + T + d ≤ finalTimestamp.val`.
4. `ApcOptimizer/VmSpec/Audit/OpenVmLegalAudit.lean` — `stepChip_advancesClock`'s last bullet
   (~line 336) builds two witnesses `⟨1, by omega, by omega, by simp …⟩` and
   `⟨2, by omega, by omega, by simp …⟩`. Each loses one `by omega`.
5. `ApcOptimizer/VmSpec/Audit/SoundnessGivesLegality.lean` — `checkedStepChip`'s legality proof
   (~line 449, `refine ⟨0, 0, 0, 1, by omega, hw, ?_, ?_, ?_, ?_⟩` and the memory bullet that
   follows). Same shortening.

Verify: `lake build` clean with no warnings, then `bash Scripts/check-proof-integrity.sh`.

## Change 2 — say the right thing about memory receives

*Real work. Changes the audited surface. Review before landing.*

Two candidate shapes, in preference order: tie each receive to its own send by a bounded distance
(the requirement OpenVM already enforces — see below), or, failing that, drop receives from the
clause and rebuild their timestamp bound at VM level.

### The problem this has to solve

The clause is currently doing a second, unadvertised job. Several proofs need
*"no timestamp in this run is astronomically large"* — arithmetic is modulo `p`, and an unbounded
value may have wrapped, which breaks the induction in `maintains_of_stateful_active`. Today that
fact arrives for **every** memory message, receives included, straight from this clause, via:

```
Circuit.advancesClock (memory conjunct)
  → openVmHost_pinsRanks            (Implementation/OpenVmChain.lean)
  → VmAssignment.withinRankBound    (Implementation/Rank.lean)
  → Circuit.ranksBounded            (Legal.lean) — quantifies over every nonzero-multiplicity
                                     interaction, receives included
  → the rank induction in maintains_of_stateful_active (Implementation/Realizes.lean)
```

Drop receives from the clause and that bound is gone for them.

**It cannot be recovered per-chip.** The natural idea — the APC range-checks the old timestamp, so
take the bound from `Circuit.satisfiesStateless` — does not work: the APC range-checks the
*difference* `t − prev_t − 1`, decomposed into a 17-bit and a 12-bit limb, and never `prev_t`
itself. `readEcho_limbs` in `Audit/OpenVmLegalAudit.lean` runs the other direction — it derives
`t₀.val < t₁.val` **from** a window bound on `t₀`, precisely because without one `t₁ = t₀ + 1 + ε`
may have wrapped. Knowing the send is bounded says nothing about the receive.

The bound is genuinely a multi-chip fact: the record "at time 900, address 40 held X" had to be
*sent* by someone — memory init, which runs at timestamp `0`, or an earlier instruction whose
window the bridge walk already bounds. `VmAssignment.withinRankBound`'s own doc comment says as
much: every intermediate timestamp being in range "is a multi-chip consequence, and deriving it is
this argument's job rather than its premise". The current clause shortcuts that by assuming it
per-chip, and that assumption is what is false.

### The requirement that probably belongs here instead

Rather than dropping receives from the clause and rebuilding everything globally, tie each receive
to its own send. OpenVM already enforces exactly this, per access, with `AssertLtSubAir` (the
`timestamp_lt` gadget): every memory access range-checks `t_send − t_prev − 1`, decomposed into a
17-bit and a 12-bit limb at the default `timestamp_max_bits = 29`. So **the two halves of one
memory access are a bounded distance apart**, and that is a property of the chip alone.

In the imported APC this is visible as the variable-range-checker traffic:

```
[reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0, 17]
[15360*prev_ts + 15360*decomp0 + 15360 - 15360*ts, 12]
```

So the memory conjunct would read, roughly:

* every memory **send** sits at `base + δ` with `δ < d` (Change 1's form); and
* every memory **receive** is matched by a send of the same address, at a timestamp a bounded
  distance later — `∃ Δ : ℕ, Δ < timestampBound ∧ t_send = t_recv + Δ`.

This is strictly better than the "receives leave the clause" plan below: it is checkable per chip,
it is what the AIR actually constrains, and it keeps the rank bound derivable locally rather than
needing a new VM-level balancing argument.

**The one step to check before committing to it.** Bounded distance plus a bounded send gives a
bounded receive only if the subtraction does not underflow. From `t_send = t_recv + Δ` in `ZMod p`
we get `t_recv.val = t_send.val − Δ` **when `Δ ≤ t_send.val`**; otherwise `t_recv.val` is
`p − (Δ − t_send.val)`, which is enormous. That is the same wraparound `readEcho_limbs`
(`Audit/OpenVmLegalAudit.lean`) has to rule out, and there it is ruled out by an a-priori window
bound on `t₀`. Work out where that comes from here before writing the clause — the likely answer
is that it follows from the send being inside the window and the run starting at timestamp `1`
(`ConnectorBoundary`), which would make the whole thing local after all. If it does not, fall back
to the VM-level plan below.

### The change (fallback: receives leave the clause entirely)

**Audited surface — one edit.** In `Legal.lean`, restrict the memory conjunct to sends: replace
`(bi.eval asg).multiplicity ≠ 0 →` with `(bi.eval asg).multiplicity = 1 →`. `= 1` is the right way
to say "send": `Circuit.statefulPolarity` already pins stateful multiplicities to `{0, 1, -1}`, and
OpenVM memory sends carry `+1`, receives `-1`. Mirror the edit in `ClockStep.mem`
(`Implementation/OpenVmChain.lean`, not audited).

Deliberately leave `Host.pinsRanks`, `VmAssignment.withinRankBound` and `Circuit.ranksBounded`
**unchanged** — they still claim the bound for all traffic. Only the *proof* for `openVmHost` has
to work harder. That keeps the audit-surface churn to the single conjunct above.

**The work — `openVmHost_pinsRanks` splits into two cases.**
`ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean`, ~line 560. After `rcases` on the
interaction's multiplicity (`statefulPolarity` gives `0`/`1`/`-1`; `0` is excluded by the
`ranksBounded` hypothesis):

* **`multiplicity = 1` (send)** — the existing argument, unchanged.
* **`multiplicity = -1` (receive)** — new. Needs a lemma of roughly this shape:

  > In a satisfying VM assignment over `openVmHost`, if any chip contributes a negative
  > multiplicity to a memory message `m`, then `openVmRank openVmMemBusId m < openVmRankBound`.

  Argument: bus balance makes the net at `m` zero, so some chip contributes positively there.
  Enumerate the possible positive contributors and bound each one's timestamp:
  - another guest instance's send — bounded by the send case above;
  - `memoryInitHostChip` — its `canProduce` pins the timestamp to `0`;
  - `inputHostChip` — its writes land at `base + 1` / `base + 2`, and `base` is bounded because
    input instances sit on the same execution bridge (`openVmHost_inputTime_injOn`,
    `bridgeChain`);
  - `memoryFinalizeHostChip` and `outputHostChip` only receive, so they cannot be the positive
    contributor;
  - the four lookup chips are pinned to lookup buses and cannot touch memory at all
    (`openVmHost_sinksAreTables`).

  The "somebody must have sent it" step is the same move `maintains_of_stateful_active`
  (`Implementation/Realizes.lean`) already makes for payload invariants, built on
  `guestNet_ne_zero_of_uniform` in `Implementation/Counting.lean`. Reuse that pattern rather than
  reinventing it.

**Knock-on sites.** The witness constructions in `Audit/OpenVmLegalAudit.lean`
(`stepChip_advancesClock`) and `Audit/SoundnessGivesLegality.lean` (`checkedStepChip`) get *easier*
— their memory-receive bullets can be discharged by the multiplicity hypothesis being `-1 ≠ 1`
rather than by exhibiting a `δ`. Simplify rather than patch.

### Risks

* The host-chip enumeration above is the part most likely to reveal a gap. If some `openVmHost`
  chip can send a memory record at an unbounded timestamp, this argument fails and the finding is
  larger than stated — check `memoryInitHostChip`'s address-space cases in particular.
* `Circuit.ranksBounded` is also a hypothesis of `Circuit.statefulSendsMaintain`. It is stated over
  all interactions there too; if the receive case proves awkward, consider whether that clause
  needs it for receives at all before weakening anything.

## Done when

1. `lake build` is clean with **no warnings**.
2. `bash Scripts/check-proof-integrity.sh` passes (add any new lemma names to the `[ignore]`
   section of `Scripts/unused-theorems.txt` — the `VmSpec/` tree is unreachable from the
   correctness roots, so everything in it is listed by hand).
3. In `ApcOptimizer/VmSpec/Audit/RealApcLegality.lean`, `apc2105000Opt` — the keccak APC at stage
   `039_trivial_simp` — should now satisfy `Circuit.advancesClock` at any `maxWindow > 11`. Prove
   it, and replace the prose in that file's header table that currently records the failure. That
   theorem is the point of the whole exercise: a real APC satisfying the clause.
4. Update finding G in `vm-spec-audit.md` and the entry in `vm-spec-todo.md`.
