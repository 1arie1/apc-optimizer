import ApcOptimizer.VmSpec.Audit.Apc2105000
import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.OpenVmLegalAudit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **`Circuit.legalGuest` measured against real APCs.**

    `Audit/OpenVmLegalAudit.lean` checks the legality clauses against hand-written chips in the
    shape a real OpenVM AIR has. This file does the same against circuits nobody wrote by hand:
    the keccak basic block at pc `2105000`, at three points in powdr's own optimizer pipeline
    (`Apc2105000.lean`, emitted from the stage dumps by `Scripts/emit-apc-lean.py`). Same block,
    same semantics, three forms — so a difference between two results is a statement about the
    optimizer, not about the block.

    | | `apc2105000Unopt` (`000_unopt`) | `apc2105000Opt` (`039_trivial_simp`) | `apc2105000Gated` (`040`) |
    | --- | --- | --- | --- |
    | `statelessSendOnly` | **true** | **true** | true, out of checker reach |
    | `statefulPolarity` | **true** | **true** | true, out of checker reach |
    | `hasStepLayout` | four arcs, not proved | **true**, one arc | not proved (needs primality) |

    Every "true" above is discharged by `Audit/SendOnlyPolarity.lean`'s decidable checker and its
    soundness theorem — a `Bool` and a `rfl`, with no case analysis over the circuit written by
    hand. The optimized APC needs only the constant-folding tier; the unoptimized one needs the
    constant-propagation tier, since its multiplicities are opcode-flag sums that are legal only
    because a constraint pins them.

    **Why `039` and not the pipeline's final output.** The last pass introduces a fresh `is_valid`
    column and multiplies every multiplicity by it, which puts the circuit out of the multiplicity
    checker's reach (`apc2105000Gated_checkMultiplicities_fails`): `Expression.foldConst` returns
    `none` on a bare variable, and the booleanity constraint `is_valid * (is_valid - 1) = 0` is not
    linear, so no pin rule comes off it either. Stage `039` is that same circuit one pass earlier —
    identical bus interactions and constraints, multiplicities the literal `±1`.

    It also puts `hasStepLayout` behind a case split on `is_valid`, which needs `ZMod babyBear`
    to be a domain. The padding row that gate introduces is *not* a reason to prefer `039` any
    more: `StepLayout` decomposes the bridge net into a list of steps, and the all-zero row is the
    empty list (`apc2105000Gated_padding_bridge`).

    **What a real APC's memory traffic looks like, and why the clause admits it.** Every memory
    *receive* sits at a free `*_prev_timestamp_*` column — the record an earlier instruction left,
    which the AssertLt gadget constrains only to be *less than* the access — and the first memory
    *send* sits at `from_state__timestamp_0 + 0`, i.e. exactly at the step's base. Neither fits
    the old `Circuit.advancesClock`, which demanded that memory sit strictly inside
    `(base, base + d)`; both fit `StepLayout`, which places an interaction at any integer offset
    in `[-maxLookback, d]` and orders only the sends. That is what
    `apc2105000Opt_hasStepLayout` exhibits, and it closes the memory half of finding G.

    See `agent-docs/vm-spec-audit.md`, finding G, and `agent-docs/legality-redesign.md`. -/

namespace ApcOptimizer.OpenVM

/-! `Spec.lean` assumes primality of the characteristic for every `p` it quantifies over. These
    circuits sit at the literal `babyBear`, so the one theorem that needs `ZMod babyBear` to be a
    field takes the same assumption as an instance hypothesis rather than re-proving it (Mathlib's
    `norm_num` primality extension is not built in this checkout). -/

/-- The rules all three circuits are checked against: OpenVM's own bus map, memory on bus `1`. -/
abbrev apcRules : GuestBusRules babyBear :=
  openVmGuestRules defaultBusMap openVmMemBusId

/-- powdr emits `-1` as the literal `p - 1`; the two are the same field element. -/
theorem babyBear_negOne : (2013265920 : ZMod babyBear) = -1 := by decide

/-- A circuit whose every multiplicity vanishes puts nothing on any bus. -/
theorem allEffects_eq_zero_of_mults_zero {p : ℕ} {c : Circuit p} {asg : ChipAssignment p}
    (h : ∀ bi ∈ c.busInteractions, (bi.eval asg).multiplicity = 0) (m : BusMessage p) :
    c.allEffects asg m = 0 := by
  refine List.sum_eq_zero (fun x hx => ?_)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, -⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  exact h bi hbi

--------- The gadgets a placement is read off ---------

/-- `-1` is neither `0` nor `1`: what rules a memory *receive* out of `StepLayout.ordered`'s and
    `StepLayout.sendsOk`'s send obligations. -/
theorem babyBear_negOne_ne_one : (2013265920 : ZMod babyBear) ≠ 1 := by decide

theorem babyBear_negOne_ne_zero : (2013265920 : ZMod babyBear) ≠ 0 := by decide

/-- **OpenVM's `AssertLtSubAir`, as it survives powdr's optimizer.** The gadget's own constraint
    `prev + 1 + lo + 2 ^ 17 * hi = t` is substituted away; what is left is its *range checks* — the
    low limb to 17 bits and, as the high limb's payload, `15360 * (prev + lo - base - δ)` to 12.
    That is the same equation, because `15360 = -1/2 ^ 17` in BabyBear (`15360 * 131072 = p - 1`),
    so the payload *is* `hi`.

    Reading it back: the access sits at `base + δ` and the record it receives sits `n` ticks
    earlier, `n = lo + 2 ^ 17 * hi < 2 ^ 29 = openVmTimestampBound`. That bound is the whole content
    of `StepLayout.placed`'s `-maxLookback ≤ offset`, and this is why `Circuit.hasStepLayout` is
    gated on `Circuit.satisfiesStateless`: after the substitution nothing about a receive's offset
    is derivable from the algebraic constraints alone. -/
theorem lt_gadget_offset (δ : ℤ) (prev base : ZMod babyBear) {lo hi : ZMod babyBear}
    (hlo : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [lo, 17] })
    (hhi : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [hi, 12] })
    (heq : hi = 15360 * prev + 15360 * lo - 15360 * base - 15360 * ((δ : ℤ) : ZMod babyBear)) :
    ∃ n : ℕ, n < 2 ^ 29 ∧ prev = base + (((δ - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hlo' : lo.val < 2 ^ 17 := by
    have := (show (17 : ZMod babyBear).val ≤ 17 ∧ lo.val < 2 ^ (17 : ZMod babyBear).val from hlo).2
    rwa [show (17 : ZMod babyBear).val = 17 from by decide] at this
  have hhi' : hi.val < 2 ^ 12 := by
    have := (show (12 : ZMod babyBear).val ≤ 17 ∧ hi.val < 2 ^ (12 : ZMod babyBear).val from hhi).2
    rwa [show (12 : ZMod babyBear).val = 12 from by decide] at this
  refine ⟨lo.val + 131072 * hi.val, by omega, ?_⟩
  have hlo'' : ((lo.val : ℕ) : ZMod babyBear) = lo := by simp
  have hhi'' : ((hi.val : ℕ) : ZMod babyBear) = hi := by simp
  push_cast [hlo'', hhi'']
  have h15 : (15360 : ZMod babyBear) * 131072 = -1 := by decide
  linear_combination (131072 : ZMod babyBear) * heq
    + (prev + lo - base - ((δ : ℤ) : ZMod babyBear)) * h15

/-- `x + 3 = (x ^^^ 3) + 2 * (x &&& 3)` for a byte, by cases: the low two bits are the only ones
    the two operations disagree on. -/
theorem xor_three : ∀ x < 256, x + 3 = Nat.xor x 3 + 2 * (x % 4) := by decide

/-- **`x AND 3` is a byte, from the bitwise table alone.** OpenVM masks by lookup up rather than by
    constraint: `z = x XOR 3` (the table's `op = 1` arm) with `z = x + 3 - 2 * a` pins
    `a = x AND 3`, hence `a < 4`. This is `apc2105000Opt`'s only fresh memory send — a value the
    APC computes rather than echoes — and the one place its byte-ness is not inherited from a
    receive. -/
theorem isByte_of_xorThree {x z a : ZMod babyBear}
    (hx : isByte x) (hz : z.val = Nat.xor x.val 3) (heq : z = x + 3 - 2 * a) : isByte a := by
  have hx' : ((x.val : ℕ) : ZMod babyBear) = x := by simp
  have hz' : ((z.val : ℕ) : ZMod babyBear) = z := by simp
  have key : (2 : ZMod babyBear) * a = 2 * ((x.val % 4 : ℕ) : ZMod babyBear) := by
    have hc : ((x.val + 3 : ℕ) : ZMod babyBear)
        = ((Nat.xor x.val 3 + 2 * (x.val % 4) : ℕ) : ZMod babyBear) := by rw [xor_three x.val hx]
    push_cast at hc
    rw [hx', ← hz, hz'] at hc
    linear_combination hc + heq
  -- `2` is a unit, so `key` determines `a`; no primality needed.
  have h2inv : (1006632961 : ZMod babyBear) * 2 = 1 := by decide
  have ha : a = ((x.val % 4 : ℕ) : ZMod babyBear) := by
    linear_combination (1006632961 : ZMod babyBear) * key
      - (a - ((x.val % 4 : ℕ) : ZMod babyBear)) * h2inv
  have hmod : x.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
  show a.val < 256
  rw [ha, ZMod.val_natCast_of_lt (lt_trans hmod (by norm_num [babyBear]))]
  omega

--------- The optimized APC: both multiplicity clauses, by static analysis ---------

/-- **The static check passes on a real optimized APC.** Every multiplicity stage `039` carries is
    a field literal, so `Expression.foldConst` — `Audit/SendOnlyPolarity.lean`'s first and only
    tier — resolves all 23 of them, and `decide` closes the check in the kernel. No case analysis
    over the circuit is written by hand. -/
theorem apc2105000Opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful apc2105000Opt = true := by decide

/-- **Both multiplicity clauses of `Circuit.legalGuest`, for a real optimized APC**, discharged by
    `checkMultiplicities_sound` from the `Bool` above rather than by a proof about this particular
    circuit. -/
theorem apc2105000Opt_legalMultiplicities :
    apc2105000Opt.statelessSendOnly apcRules ∧ apc2105000Opt.statefulPolarity apcRules :=
  checkMultiplicities_sound apc2105000Opt_checkMultiplicities rfl

/-- **The checker does not reach the pipeline's final output.** `apc2105000Gated`'s multiplicities
    are `±is_valid`, and `Expression.foldConst` returns `none` on a bare variable, so the check
    fails on a circuit whose clauses are in fact true — reachable only through the booleanity
    constraint `is_valid * (is_valid - 1) = 0`. That is precisely the second tier
    `Audit/SendOnlyPolarity.lean`'s docstring names and does not attempt, and powdr's last pass is
    what moves the circuit out of the first tier's reach. -/
theorem apc2105000Gated_checkMultiplicities_fails :
    checkMultiplicities apcRules.isStateful apc2105000Gated = false := by decide

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `apc2105000Gated_padding_bridge`'s row, no
    assignment makes this circuit silent. -/
theorem apc2105000Opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ apc2105000Opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (apc2105000Opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [apc2105000Opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- One interaction of `apc2105000Opt`, unpacked from `Circuit.satisfiesStateless`. The message is
    given explicitly and matched against the list entry by `rfl`, which leaves the side conditions
    as `decide`s on concrete field elements. -/
theorem optAccepts {asg : ChipAssignment babyBear}
    (hacc : apc2105000Opt.satisfiesStateless apcRules asg)
    (k : ℕ) (hk : k < apc2105000Opt.busInteractions.length)
    (m : BusInteraction (ZMod babyBear)) (hm : (apc2105000Opt.busInteractions[k]).eval asg = m)
    (hst : apcRules.isStateful m.busId = false) (hmult : m.multiplicity ≠ 0) :
    accepts defaultBusMap m := by
  subst hm; exact hacc _ (List.getElem_mem hk) hst hmult

/-- Where each of `apc2105000Opt`'s twelve stateful interactions sits, as an offset from the step's
    `from_state__timestamp_0`. Positions `7` and `13`–`22` are the stateless lookups and never read.
    The five receives look back by their own gadget's `n`; the six sends and the bridge receive sit
    at literal offsets. -/
def optOffsets (n0 nw0 nr1 nw1 nr3 : ℕ) : List ℤ :=
  [-1 - (n0 : ℤ), 0, 1 - nw0, 0, 2 - nr1, 4 - nw1, 5, 0, 6, 9, 9 - nr3, 10, 11]

/-- The largest offset each position can hold: a receive's is `δ - n` for a lookback `n ≥ 0`, so
    `δ` bounds it; the six sends attain their entry exactly. -/
def optOffsetUb : List ℤ := [-1, 0, 1, 0, 2, 4, 5, 0, 6, 9, 9, 10, 11]

/-- Each of the six sends dominates every position before it. With `optOffsetUb` this is the whole
    of `StepLayout.ordered` for this circuit — a `decide` over positions, which is what stating the
    layout in integer offsets rather than field timestamps buys. -/
theorem optOffsetUb_dominates :
    ∀ b ∈ [1, 6, 8, 9, 11, 12], ∀ k < b, optOffsetUb.getD k 0 < optOffsetUb.getD b 0 := by decide

/-- **A real optimized APC has a step layout.** One arc — `(2105000, t) → (2105016 - 192·cmp,
    t + 11)` — and the twelve stateful interactions placed at `optOffsets`, read off the five
    surviving lt gadgets (`lt_gadget_offset`). Its five memory sends are byte-valued: four echo a
    receive earlier in the same step, and the fifth is the masked value the bitwise table checks
    (`isByte_of_xorThree`).

    This is finding G's memory half, closed. The clause the old `Circuit.advancesClock` failed on
    every APC — memory strictly inside `(base, base + d)` — is gone; what replaces it, an integer
    offset in `[-2 ^ 29, 11]` with the sends ordered, this circuit satisfies. -/
theorem apc2105000Opt_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    apc2105000Opt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg _ hacc
  obtain ⟨n0, hn0, ht0⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩)
    (optAccepts hacc 13 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩, 17] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (optAccepts hacc 14 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [15360 * asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
          + 15360 * asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩
          + 15360 + 2013265920 * (15360 * asg ⟨"from_state__timestamp_0", some 1⟩), 12] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (by push_cast
        linear_combination (15360 * asg ⟨"from_state__timestamp_0", some 1⟩) * babyBear_negOne)
  obtain ⟨nw0, hnw0, htw0⟩ := lt_gadget_offset 1
    (asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩)
    (optAccepts hacc 15 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩, 17] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (optAccepts hacc 16 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [15360 * asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
          + 15360 * asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩
          + 2013265920 * (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 15360), 12] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (by push_cast
        linear_combination (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 15360)
          * babyBear_negOne)
  obtain ⟨nr1, hnr1, htr1⟩ := lt_gadget_offset 2
    (asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩)
    (optAccepts hacc 17 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩, 17] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (optAccepts hacc 18 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [15360 * asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
          + 15360 * asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩
          + 2013265920 * (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 30720), 12] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (by push_cast
        linear_combination (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 30720)
          * babyBear_negOne)
  obtain ⟨nw1, hnw1, htw1⟩ := lt_gadget_offset 4
    (asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩)
    (optAccepts hacc 19 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩, 17] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (optAccepts hacc 20 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [15360 * asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
          + 15360 * asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩
          + 2013265920 * (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 61440), 12] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (by push_cast
        linear_combination (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 61440)
          * babyBear_negOne)
  obtain ⟨nr3, hnr3, htr3⟩ := lt_gadget_offset 9
    (asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩)
    (optAccepts hacc 21 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩, 17] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (optAccepts hacc 22 (by decide)
      { busId := 3, multiplicity := 1,
        payload := [15360 * asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
          + 15360 * asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩
          + 2013265920 * (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 138240), 12] }
      rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    (by push_cast
        linear_combination (15360 * asg ⟨"from_state__timestamp_0", some 1⟩ + 138240)
          * babyBear_negOne)
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    optAccepts hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  have hub : ∀ i : Fin apc2105000Opt.busInteractions.length,
      apcRules.isStateful (apc2105000Opt.busInteractions.get i).busId = true →
      ((apc2105000Opt.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 ≤ optOffsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [optOffsets, optOffsetUb, apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin apc2105000Opt.busInteractions.length,
      apcRules.isStateful (apc2105000Opt.busInteractions.get i).busId = true →
      ((apc2105000Opt.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [1, 6, 8, 9, 11, 12] ∧
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 = optOffsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [optOffsets, optOffsetUb, apc2105000Opt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful, BusInteraction.eval,
        Expression.eval, babyBear_negOne_ne_one]
  refine ⟨⟨[⟨2105000, 2105016 + 2013265920 * (192 * asg ⟨"cmp_result_3", some 126⟩),
      asg ⟨"from_state__timestamp_0", some 1⟩, 11⟩],
    fun i => (0, (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0),
    by simp, by simpa using hw, ?_, ?_, ?_, ?_⟩⟩
  · -- The bridge: one receive at `base`, one send eleven ticks later, nothing else on bus `0`.
    have h11 : ((11 : ℕ) : ZMod babyBear) = 11 := by push_cast; ring
    have h11' : (11 : ZMod babyBear) ≠ 0 := by decide
    refine ClockArc.net_singleton _ ?_ ?_ ?_ ?_
    · intro hcon
      rw [Prod.ext_iff] at hcon
      have hb := hcon.2
      simp only [List.cons.injEq, and_true, h11] at hb
      exact h11' (by linear_combination -hb.2)
    · simp [Circuit.allEffects, apc2105000Opt, BusInteraction.eval, Expression.eval,
        openVmGuestRules, h11', babyBear_negOne]
    · simp [Circuit.allEffects, apc2105000Opt, BusInteraction.eval, Expression.eval,
        openVmGuestRules, h11', babyBear_negOne]
    · rintro ⟨mb, ml⟩ hbus hr hs
      simp only [openVmGuestRules] at hbus
      subst hbus
      simp only [ne_eq, Prod.mk.injEq, true_and, h11, openVmGuestRules] at hr hs
      simp [Circuit.allEffects, apc2105000Opt, BusInteraction.eval, Expression.eval,
        Ne.symm hr, Ne.symm hs]
  · -- The placement, offset by offset.
    intro i hst hm
    fin_cases i
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp] using ht0⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp]⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp] using htw0⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp] using htr1⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp] using htw1⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp]⟩
    · simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp]⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp]⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp] using htr3⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp]⟩
    · exact ⟨_, rfl, by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The ordering: numeric, via `optOffsetUb`.
    intro i j hji hsi hsj hmj hmi _
    obtain ⟨hmem, heq⟩ := hsendIdx i hsi hmi
    show (optOffsets n0 nw0 nr1 nw1 nr3).getD j.val 0
      < (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0
    rw [heq]
    exact lt_of_le_of_lt (hub j hsj hmj)
      (optOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
  · -- The five memory sends: four echoes and one masked value.
    intro i hst hmult hlow
    fin_cases i
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · have h0 := hlow ⟨0, by decide⟩ (by simp [Fin.lt_def]) rfl
        (by simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
          babyBear_negOne_ne_zero]) rfl
      replace h0 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
        asg ⟨"a__3_0", some 22⟩, asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩]) := h0
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
        asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩])
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h0)
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · -- the word read at address 44 is written on to address 56
      have h4 := hlow ⟨4, by decide⟩ (by simp [Fin.lt_def]) rfl
        (by simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
          babyBear_negOne_ne_zero]) rfl
      replace h4 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
        asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
        asg ⟨"a__3_1", some 58⟩, asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩]) := h4
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 56,
        asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
        asg ⟨"a__3_1", some 58⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 5])
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h4)
    · simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · -- the word read at address 40 is written on to address 52
      have h0 := hlow ⟨0, by decide⟩ (by simp [Fin.lt_def]) rfl
        (by simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
          babyBear_negOne_ne_zero]) rfl
      replace h0 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
        asg ⟨"a__3_0", some 22⟩, asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩]) := h0
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 52,
        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
        asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 6])
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h0)
    · -- the fresh write at address 44, byte-valued because the bitwise table masked it
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
        asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩
    · simp [apc2105000Opt, BusInteraction.eval, Expression.eval,
        babyBear_negOne_ne_one] at hmult
    · show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 0, 0, 0, 0, 0,
        asg ⟨"from_state__timestamp_0", some 1⟩ + 10])
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
        ⟨isByte_zero, isByte_zero, isByte_zero, isByte_zero⟩
    · -- the bridge send: `openVmPayloadOk` asks nothing of an execution-bridge state
      simp [apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules,
        openVmPayloadOk, defaultBusMap]
    all_goals
      simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst

/-- **A real optimized APC is a legal OpenVM guest.** All four clauses, for a circuit nobody wrote
    by hand: the two multiplicity ones by `Audit/SendOnlyPolarity.lean`'s checker, the layout by
    `apc2105000Opt_hasStepLayout`, the size by counting. -/
theorem apc2105000Opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    apc2105000Opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := apc2105000Opt_legalMultiplicities.1
  polarity := apc2105000Opt_legalMultiplicities.2
  stepLayout := apc2105000Opt_hasStepLayout hw
  size := by simpa [apc2105000Opt] using hi

--------- The unoptimized APC: same clauses, via constant propagation ---------

/-- **The strengthened check passes on the unoptimized APC.** Its multiplicities are not literals —
    each is a sum of that instruction's opcode flags, or an operand's address space — so
    `checkMultiplicities` cannot see them. `checkMultiplicitiesWith` reads 27 pin rules off the
    constraints, among them `1 - (add + sub + xor + or + and) = 0` (the flag sum is `1`) and
    `rs2_as_i - 0 = 0` (that operand is an immediate), and every one of the 71 multiplicities folds
    against them. -/
theorem apc2105000Unopt_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful apc2105000Unopt = true := by decide

/-- **Both multiplicity clauses for the unoptimized APC**, again from the `Bool` rather than from a
    proof about this circuit. With `apc2105000Opt_legalMultiplicities` this says the two clauses
    survive powdr's optimizer on this block — the interesting direction for `PreservesLegality`. -/
theorem apc2105000Unopt_legalMultiplicities :
    apc2105000Unopt.statelessSendOnly apcRules ∧ apc2105000Unopt.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound apc2105000Unopt_checkMultiplicitiesWith rfl

--------- The gated APC: the padding row kills `advancesClock` ---------

/-- **The padding row.** Every column zero satisfies the gated APC's four constraints: they are
    `cmp * (cmp - 1)`, `(1 - cmp) * a`, `free * a - cmp`, and `is_valid * (is_valid - 1)`, each of
    which vanishes at `0`. Nothing pins `is_valid` to `1`. -/
theorem apc2105000Gated_satisfiesAlgebraic_zero :
    apc2105000Gated.satisfiesAlgebraic (fun _ => 0) := by
  intro c hc
  simp only [apc2105000Gated, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Expression.eval]

/-- On that row the gated APC is silent: every multiplicity is `±is_valid`, which is `0`. -/
theorem apc2105000Gated_mults_zero_on_padding :
    ∀ bi ∈ apc2105000Gated.busInteractions,
      (bi.eval (fun _ => 0)).multiplicity = 0 := by
  intro bi hbi
  simp only [apc2105000Gated, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BusInteraction.eval, Expression.eval]

/-- **The padding row is a no-op instance, and the clause now says so.** `StepLayout` decomposes
    an instance's bridge net into a *list* of steps, and the empty list is a legal witness: it nets
    zero, which is exactly what a row with `is_valid = 0` puts on the bridge.

    This is the half of finding G1 the arc form closes. The clause used to demand a bridge receive
    netting `-1` on *every* algebraically-satisfying assignment, which the all-zero row has no way
    to supply — so stage `040` failed the clause outright. It no longer does; what still fails, for
    `040` and `039` alike, is the memory conjunct (finding G3). -/
theorem apc2105000Gated_padding_bridge {maxWindow : ℕ} (hw : 0 < maxWindow) :
    ∃ arcs : List (ClockArc babyBear),
      (∀ α ∈ arcs, 0 < α.d) ∧ (arcs.map (·.d)).sum < maxWindow ∧
      ∀ m : BusMessage babyBear, m.1 = openVmExecBusId →
        apc2105000Gated.allEffects (fun _ => 0) m
          = (arcs.map (fun α => α.effect openVmExecBusId m)).sum := by
  refine ⟨[], by simp, by simpa using hw, fun m _ => ?_⟩
  simpa using allEffects_eq_zero_of_mults_zero apc2105000Gated_mults_zero_on_padding m

/-- **The unoptimized APC has no padding row either**: it pins each fused instruction's opcode-flag
    sum to `1` (`1 - (add + sub + xor + or + and) = 0`, one per instruction). -/
theorem apc2105000Unopt_zero_not_satisfiesAlgebraic :
    ¬ apc2105000Unopt.satisfiesAlgebraic (fun _ => 0) := by
  intro h
  have := h
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
          (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
          (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))
      (.const 1))
    (by simp [apc2105000Unopt])
  simp only [Expression.eval] at this
  exact absurd this (by decide)

end ApcOptimizer.OpenVM
