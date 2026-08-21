import ApcOptimizer.VmSpec.Audit.Apc2105000
import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxHeartbeats 4000000

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
    | `advancesClock` | false | false, memory clause only | **false**, no bus traffic at all |

    Every "true" above is discharged by `Audit/SendOnlyPolarity.lean`'s decidable checker and its
    soundness theorem — a `Bool` and a `rfl`, with no case analysis over the circuit written by
    hand. The optimized APC needs only the constant-folding tier; the unoptimized one needs the
    constant-propagation tier, since its multiplicities are opcode-flag sums that are legal only
    because a constraint pins them.

    **Why `039` and not the pipeline's final output.** The last pass introduces a fresh `is_valid`
    column and multiplies every multiplicity by it, carrying only `is_valid * (is_valid - 1) = 0`.
    That is the AIR's padding gate — with it, the all-zero row is algebraically satisfying, the
    circuit nets `0` on every message of every bus, and `Circuit.advancesClock`, which demands a
    bridge receive with net `-1` on *every* algebraically-satisfying assignment, has no witness
    (`apc2105000Gated_not_advancesClock`). Stage `039` is that same circuit one pass earlier:
    identical bus interactions and constraints, multiplicities the literal `±1`, no padding row.
    It is the form these clauses are stated for, so it is the one the results below use.

    **What still fails, and is not fixable by choosing a different circuit.**
    `Circuit.advancesClock` requires *every* memory interaction to sit at `base + δ` with
    `0 < δ < d`. At every stage of the pipeline the APC violates this twice: its memory *receives*
    sit at free `*_prev_timestamp_*` columns — the record left by an earlier instruction, which the
    AssertLt gadget constrains to be *less than* `base` — and its first memory *send* sits at
    `from_state__timestamp_0 + 0`, i.e. exactly `base`, so `δ = 0`. That is how OpenVM memory
    works; no circuit in the dump avoids it. `OpenVmLegalAudit.lean`'s `stepChip` satisfies the
    clause only because it idealizes, putting its receive at `base + 1`.

    See `agent-docs/vm-spec-audit.md`, finding G. -/

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

/-- **The optimized APC has no padding row**, so `apc2105000Gated_not_advancesClock` below does not
    transfer to it: its multiplicities are literals, and one of them is nonzero under every
    assignment. -/
theorem apc2105000Opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ apc2105000Opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (apc2105000Opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [apc2105000Opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

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

/-- **`Circuit.advancesClock` is false of the gated APC**, at every window — where it is *not*
    false of `apc2105000Opt` for this reason, the two circuits differing only by the `is_valid`
    gate. This is why the results above are stated at stage `039`. -/
theorem apc2105000Gated_not_advancesClock (maxWindow : ℕ) :
    ¬ apc2105000Gated.advancesClock apcRules maxWindow := by
  intro h
  obtain ⟨pcFrom, pcTo, base, d, -, -, hrecv, -⟩ :=
    h (fun _ => 0) apc2105000Gated_satisfiesAlgebraic_zero
  rw [allEffects_eq_zero_of_mults_zero apc2105000Gated_mults_zero_on_padding] at hrecv
  exact absurd hrecv (by decide)

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
