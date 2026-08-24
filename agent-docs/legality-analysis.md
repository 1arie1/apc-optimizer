# A static analysis for `Circuit.hasStepLayout`

*Supersedes the implementation half of [`legality-redesign.md`](legality-redesign.md), whose
multi-arc `StepLayout` was replaced by the single-step one in `12a85af`. Background: finding G in
[`vm-spec-audit.md`](vm-spec-audit.md); the circuits in
`ApcOptimizer/VmSpec/Audit/RealApcLegality.lean`.*

## The clause, as it now stands

`StepLayout` is one instruction step — the shape `Circuit.advancesClock` had — plus an integer
offset per stateful interaction:

```
pcFrom pcTo base d   place : Fin n → ℤ
dPos    0 < d                     dLt     d < maxWindow
recv    allEffects (b, [pcFrom, base]) = -1
send    allEffects (b, [pcTo, base + d]) = 1
other   nothing else on bus b
placed  every active stateful interaction at an offset in [-maxLookback, d]
ordered a send dominates everything before it
sendsOk a send's payload is Ok given that what precedes it is
```

Two support lemmas in `Legal.lean`: `StepLayout.endpoints_ne` (the endpoints differ, since equal
ones would net both `-1` and `1`) and `StepLayout.net` (the triple as the single equation
`Chain.lean` consumes). Only two theorems consume the clause: `openVmHost_ordersRanks` (via the
bridge fields and `placed`) and `maintains_of_stateful_active` (via `ordered` and `sendsOk`).

## Status against the three APC stages

| | `Unopt` (000) | `Opt` (039) | `Gated` (040) |
| --- | --- | --- | --- |
| `statelessSendOnly` / `statefulPolarity` | proved | proved | true, out of checker reach |
| `hasStepLayout` | **false** — four unchained steps | **proved** | **false** — padding row |

Both falsities are properties of the *circuits*, not the clause, and both are recorded in Lean:
`apc2105000Gated_not_hasStepLayout`, and `apc2105000Unopt`'s four bridge arcs (its
`from_state__timestamp_0..3` occur only in their own lt gadgets, so nothing chains them).

**What would fix them.** `Gated`: pin `is_valid`. `Unopt`: three constraints
`from_state__timestamp_{i+1} = from_state__timestamp_i + d_i`, or equivalently run powdr's
substitution pass, after which the six intermediate bridge messages cancel — their PCs already
chain via literals (`2105000/4/8/12`) and all four opcode-flag sums are pinned to `1`.

## The analysis

Layered, each layer a decidable check plus a soundness theorem, in the style of
`Audit/SendOnlyPolarity.lean`'s `checkMultiplicitiesWith`.

### Landed

- **`Audit/LinForm.lean`** — `Expression.toLin` normalizes an expression to a constant plus a
  coefficient **vector** over a fixed variable list, folding pinned subexpressions on the way.
  A vector rather than an association list is what keeps it cheap: addition is `zipWith`, equality
  is list equality, "is this constant?" is `all (· = 0)`, and no `Nodup` invariant is needed.
  Sound by `Expression.toLin_eval`.

  On top: `allEffects_eq_entrySum` re-reads `Circuit.allEffects` as a sum over normalized entries,
  turning a chip's traffic on one bus into a list a checker can walk.

- **`Audit/BridgeCheck.lean`** — `bridgeCheck` walks that list: first entry the receive, last the
  send, everything between cancelling in consecutive pairs (the shape a fused APC has once its
  seams are chained, one pair per seam). `d` is read off the two timestamp forms; the endpoints are
  separated at a payload position where they carry the same coefficients and differ by a nonzero
  constant — which is how `t` and `t + d` differ, and neither is a literal in a real APC.

  The caller names the three endpoint expressions and the checker verifies them against the
  traffic, so `bridgeCheck_sound` returns facts about messages the caller wrote.

  `apc2105000Opt`'s `recv`/`send`/`other` are now `optBridgeCheck`, a `decide`.

### Next, in cost order

1. **Constant-offset placement.** For an interaction whose timestamp form is `baseForm + k`,
   `linShiftedBy` already decides it. Covers every *send* and the bridge receive — 7 of the 12
   stateful interactions of `apc2105000Opt`. Needs a `tsPos : Nat → Option ℕ` parameter (payload
   index of the timestamp, per bus) and a hypothesis tying it to `GuestBusRules.getTimestamp`.

2. **`ordered`.** Interval arithmetic over slots: a constant offset is its own upper bound, a
   lookback offset `k - n` is bounded above by `k`. `optOffsetUb_dominates` is that check by hand
   already, and it is a `decide`.

3. **The lt-gadget recognizer** — the interesting one, and the first place the analysis stops
   being generic. A memory *receive*'s timestamp is a free `*_prev_timestamp_*` variable, so its
   offset is `k - n` with `n` bounded only by the gadget. The recognizer must find the two
   range-check interactions (`[lo, 17]`, `[hi, 12]`) and check that `hi` normalizes to
   `15360 * (prev + lo - base - k)` — a *linear identity between forms*, so `LinForm` decides it —
   then apply `lt_gadget_offset`, which is already proved.

   Note the offset is then **assignment-dependent**: `place` cannot be a closed term, because `n`
   comes from the gadget. So the checker's output is a *slot* (`at k` or `lookback k`), and the
   layout is built by instantiating slots per assignment. `optOffsets` is that instantiation
   written by hand.

4. **`sendsOk`** — the byte invariant, and the largest piece. Three shapes appear in
   `apc2105000Opt`: a send echoing a preceding receive's data limbs (syntactic payload equality), a
   send directly range-checked (bus-fact lookup), and a send needing real reasoning (`a__0_2`, via
   `isByte_of_xorThree`). Most of the machinery exists in
   `Implementation/OptimizerPasses/BusPairCancelJustify.lean` — `denseByteJustifiedW` has literal /
   direct-bus-bound / deep-constraint / domain / affine / basis tiers, and its deep tier already
   enumerates one-hot flags, which is the ALU shape. Missing: the assumption set (conditional
   byte-ness: "given these receives are bytes, prove this send is"), output reshaping, and an
   `Expression`↔`DenseExpr` bridge.

### What the analysis cannot become

A checker, not a decision procedure. It fails loudly rather than unsoundly, so the search may be
heuristic; what needs real proofs is the small set of lemmas the recognizers cash out to
(`lt_gadget_offset` for the window, `isByte_of_xorThree` and friends for the bytes). The `15360`
pattern is what powdr's optimizer leaves *today* — a future pass reshapes it and the recognizer
stops matching. That is a maintenance cost, not a soundness risk, and it argues for keeping a
recognizer for the pre-optimization form too, where the lt constraint is still algebraic.
