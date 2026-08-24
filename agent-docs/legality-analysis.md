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

Two support lemmas, `StepLayout.endpoints_ne` (the endpoints differ, since equal ones would net
both `-1` and `1`) and `StepLayout.net` (the triple as the single equation the bridge argument
consumes), live in `Implementation/OpenVmChain.lean` rather than `Legal.lean`: neither appears in
`StepLayout`'s own fields or in `Circuit.legalGuest`, so they don't change what the audited clause
means, only what `OpenVmChain.lean` — their one consumer — finds convenient. Only two theorems
consume the clause itself: `openVmHost_ordersRanks` (via the bridge fields and `placed`) and
`maintains_of_stateful_active` (via `ordered` and `sendsOk`).

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

- **`Audit/PlaceCheck.lean`** — `StepLayout.place` depends on the assignment (a receive's offset is
  `k - n` for whatever distance its lt gadget range-checks), so a checker cannot name it. It names
  a **`Recipe`** per interaction instead: how to *compute* the offset, and — read off the same
  constructor, so the two cannot disagree — the interval that computation stays inside.
  `Recipe.fits`/`Recipe.below` decide `placed` and `ordered` (`recipe_placed`, `recipe_ordered`);
  `placeCheckAll` verifies a `fixed` offset against the timestamp's normal form.

  `gadgetIdentity` is the lt gadget's arithmetic as a linear identity between normal forms, so
  `LinForm` decides it — and it checks the expression powdr *emitted* (`payloadOf` names the limbs
  by position in the circuit) rather than a shape restated by hand. `lookback_of_gadget` composes
  it with the two range-check lookups and `lt_gadget_offset`.

  `apc2105000Opt`'s five gadgets go through it: five `decide`s in place of five hand-written
  `linear_combination`s and five transcribed high-limb payloads. `lt_gadget_offset` additionally
  names its witness (`n = lo.val + 131072 * hi.val`), which is what makes the offset computable
  rather than merely existential.

- **`Audit/ByteCheck.lean`** — `sendsOk`, OpenVM's byte invariant. Four justifications are
  decided: the interaction is not a stateful send; it is not on the memory bus, where
  `openVmPayloadOk` asks nothing; its data limbs are literal bytes; or its data limbs are an
  *earlier* interaction's, so `sendsOk`'s own hypothesis supplies them — a memory send echoing the
  read it just did. A fifth (`external`) is left to the caller, and is decidably vacuous at every
  other index, so the caller's case analysis collapses to one `try`.

  `apc2105000Opt`'s sixty-line `sendsOk` bullet is now eight: a `decide` over `optWitnesses`, and
  the masked write at position `9`.

### What is checked, and what is still by hand

For `apc2105000Opt`:

| clause | how |
| --- | --- |
| `recv` / `send` / `other` | `optBridgeCheck`, a `decide` |
| the five lt gadgets | `gadgetIdentity` (a `decide`) + `lookback_of_gadget` |
| `placed` | by hand — thirteen one-line bullets; the recipe machinery is proved but not wired |
| `ordered` | by hand — `optOffsetUb_dominates`, a `decide`; likewise not wired |
| `sendsOk` | `optByteCheck`, a `decide`, plus one case |

### Next, in cost order
1. **Wiring `placed`/`ordered` through the recipes on `apc2105000Opt`.** The machinery is proved;
   what is left is `optRecipes` plus replacing the thirteen `placed` bullets and the `ordered` one.
   Deliberately *not* done: for this circuit it is a wash. Each bullet is already one line, and the
   per-index case analysis that `placeCheck_placed`'s `hlook`/`hbk` obligations need is the same
   size as the one it would replace. The recipes pay off on a circuit that has *no* hand proof yet
   — which is where the machinery should first be pointed.

2. **Finding the gadget rather than being told where it is.** `lookback_of_gadget` takes the two
   range-check indices from the caller. Searching for them — a bus-3 pair with payloads
   `[·, 17]`/`[·, 12]` whose high limb satisfies `gadgetIdentity` — would make the recipe list
   itself derivable instead of written out.

3. **A tier for the `external` byte case** — the one shape `ByteCheck` does not decide: a limb
   that is a byte because a lookup table says so (`a__0_2`, via `isByte_of_xorThree`). Most of the
   machinery exists in `Implementation/OptimizerPasses/BusPairCancelJustify.lean` —
   `denseByteJustifiedW` has literal / direct-bus-bound / deep-constraint / domain / affine / basis
   tiers, and its deep tier already enumerates one-hot flags, which is the ALU shape. Missing: the
   assumption set (conditional byte-ness), output reshaping, and an `Expression`↔`DenseExpr`
   bridge.

### What the analysis cannot become

A checker, not a decision procedure. It fails loudly rather than unsoundly, so the search may be
heuristic; what needs real proofs is the small set of lemmas the recognizers cash out to
(`lt_gadget_offset` for the window, `isByte_of_xorThree` and friends for the bytes). The `15360`
pattern is what powdr's optimizer leaves *today* — a future pass reshapes it and the recognizer
stops matching. That is a maintenance cost, not a soundness risk, and it argues for keeping a
recognizer for the pre-optimization form too, where the lt constraint is still algebraic.

## Toward a fully automatic analysis

Everything landed so far is a **checker**: given a circuit and a *human-supplied* certificate — the
bridge endpoints, a `Recipe` per stateful interaction, a `ByteWitness` per interaction, the two
range-check indices for each lt gadget — it decides whether the certificate is valid and, if so,
returns the `StepLayout`. Every certificate in this repo today is `apc2105000Opt`'s, written out by
hand once and checked by `decide` from then on.

The end state is a single function `Circuit p → GuestBusRules p → Option (StepLayout certificate)`
that *finds* the certificate, so a new circuit costs nothing to add — no `optWitnesses`, no
`optVars`, no `lookback_of_gadget` call sites. What that needs, on top of what exists:

- **A search over the bus-0 interaction list** for the receive/pairs/send shape `bridgeCheck`
  currently takes on faith (which interaction is the receive, which is the send). Small: bus 0 has
  few interactions and the shape is rigid.
- **A search for each stateful interaction's `Recipe`** — try `fixed` first (does its timestamp form
  match `base + k` for some literal `k`?), then search bus 3 for an `AssertLtSubAir` pair whose high
  limb satisfies `gadgetIdentity` against this interaction's timestamp. Item 2 in "Next, in cost
  order" above.
- **A search for each interaction's `ByteWitness`** — `notSend`/`notMemory` fall out of the
  multiplicity and bus-id checks already in place; `limbs` and `echo` are both cheap syntactic scans
  over the normalized payload against every earlier interaction. `external` is what is left once the
  first four fail, and is where the search should stop and defer to the assumption-set search that
  `sendsOk`'s open tier (item 3 above) still needs.
- **Ordering `ordered`'s obligation out of the search entirely** — once every interaction has a
  `Recipe`, `recipe_ordered` needs no search: it is a pairwise check over the derived intervals.

None of this changes what has to be *proved* — `lt_gadget_offset`, `isByte_of_xorThree`,
`Expression.toLin_eval`, `allEffects_eq_entrySum`, and the four checkers' soundness statements are
already the complete list of things an auditor has to trust, and a search built on top of them
inherits their soundness for free (a `Bool` a search computes and gets wrong just fails to find a
certificate, the same non-failure-mode a hand-written wrong index would have today). What changes is
that `Audit/RealApcLegality.lean` (and any future real-APC file) stops carrying `optVars`,
`optWitnesses`, or explicit gadget indices at all — those become the search's *output*, not its
input.

