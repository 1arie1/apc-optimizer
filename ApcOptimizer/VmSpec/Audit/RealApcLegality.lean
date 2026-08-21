import ApcOptimizer.VmSpec.Audit.Apc2105000
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! **`Circuit.legalGuest` measured against two real APCs.**

    `Audit/OpenVmLegalAudit.lean` checks the legality clauses against hand-written chips in the
    shape a real OpenVM AIR has. This file does the same against two circuits nobody wrote by
    hand: the keccak basic block at pc `2105000`, before and after powdr's own optimizer
    (`Apc2105000.lean`, emitted from the dumps by `Scripts/emit-apc-lean.py`). Same block, same
    semantics, two forms — so the difference between the two results is a statement about the
    optimizer, not about the block.

    The results:

    | clause | unoptimized | optimized |
    | --- | --- | --- |
    | `statelessSendOnly` | true | true |
    | `statefulPolarity` | true | true |
    | `advancesClock` | **false** | **false**, for a different reason |

    Both multiplicity clauses hold, but by different mechanisms. The unoptimized APC pins each
    instruction's opcode-flag sum to `1` and `rs2_as` to `0` outright, so every multiplicity is a
    literal `0`/`±1` once the constraints are used. The optimized APC has replaced all of that with
    one fresh `is_valid` column carrying only `is_valid * (is_valid - 1) = 0`.

    That replacement is what breaks `advancesClock` on the optimized side, and it is a live
    instance of the gap `agent-docs/legality-preservation.md` describes: the optimization is sound,
    and it destroys legality. Pinning the flags to `1` made an inactive row *algebraically
    impossible*; a free boolean `is_valid` makes the all-zero padding row algebraically satisfying,
    and on that row the circuit puts nothing on the execution bridge at all, so the "exactly one
    bridge receive" clause has no witness.

    The unoptimized APC fails the same clause for an unrelated and more basic reason:
    `Circuit.advancesClock` drops bus acceptance (it is stated on `satisfiesAlgebraic` alone), and
    nothing *algebraic* chains one instruction's timestamp to the next — that chaining is enforced
    by execution-bridge balance, which the clause deliberately does not assume. So an assignment
    may give the four fused instructions four unrelated start times, leaving four distinct bridge
    states each with net `-1` where the clause allows one.

    See `agent-docs/vm-spec-audit.md`, finding G. -/

namespace ApcOptimizer.OpenVM

/-! `Spec.lean` assumes primality of the characteristic for every `p` it quantifies over. These
    circuits sit at the literal `babyBear`, so the theorems that need `ZMod babyBear` to be a field
    take the same assumption as an instance hypothesis rather than re-proving it (Mathlib's
    `norm_num` primality extension is not built in this checkout). -/

/-- The rules both circuits are checked against: OpenVM's own bus map, memory on bus `1`. -/
abbrev apcRules : GuestBusRules babyBear :=
  openVmGuestRules defaultBusMap openVmMemBusId

/-- powdr emits `-1` as the literal `p - 1`; the two are the same field element. Stated without
    the primality hypothesis in scope, so `decide` sees a closed term. -/
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

--------- The optimized APC: multiplicities are legal ---------

/-- `is_valid * (is_valid - 1) = 0` is the optimized APC's fourth constraint, so `is_valid` is
    boolean on every algebraically-satisfying assignment. This single fact is the whole content of
    both multiplicity clauses below — and, on the `0` side, of the disproof after them. -/
theorem apc2105000Opt_isValid_bool [Fact (Nat.Prime babyBear)] (asg : ChipAssignment babyBear)
    (halg : apc2105000Opt.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 137⟩ = 0 ∨ asg ⟨"is_valid", some 137⟩ = 1 := by
  have h := halg
    (.mul (.var ⟨"is_valid", some 137⟩)
      (.add (.var ⟨"is_valid", some 137⟩) (.mul (.const 2013265920) (.const 1))))
    (by simp [apc2105000Opt])
  simp only [Expression.eval] at h
  rw [mul_one, babyBear_negOne] at h
  rcases mul_eq_zero.mp h with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (by rwa [← sub_eq_add_neg, sub_eq_zero] at h2)

/-- **The optimized APC sends only `0`/`1` to stateless buses.** Every multiplicity it carries is
    literally `is_valid`, which the constraint above pins to `{0, 1}`. -/
theorem apc2105000Opt_statelessSendOnly [Fact (Nat.Prime babyBear)] :
    apc2105000Opt.statelessSendOnly apcRules := by
  intro asg halg bi hbi hst
  have hb := apc2105000Opt_isValid_bool asg halg
  simp only [apc2105000Opt, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hst (by decide)
      | (simp only [BusInteraction.eval, Expression.eval]
         rcases hb with h | h <;> rw [h] <;> simp)

/-- **The optimized APC sends only `0`/`±1` to stateful buses.** Same fact, one more shape: a
    receive carries `-is_valid`, emitted as `(p - 1) * is_valid`. -/
theorem apc2105000Opt_statefulPolarity [Fact (Nat.Prime babyBear)] :
    apc2105000Opt.statefulPolarity apcRules := by
  intro asg halg bi hbi hst
  have hb := apc2105000Opt_isValid_bool asg halg
  simp only [apc2105000Opt, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hst (by decide)
      | (simp only [BusInteraction.eval, Expression.eval]
         rcases hb with h | h <;> rw [h] <;> simp [babyBear_negOne])

--------- The optimized APC: `advancesClock` is false ---------

/-- **The padding row.** Every column zero satisfies the optimized APC's four constraints: they are
    `cmp * (cmp - 1)`, `(1 - cmp) * a`, `free * a - cmp`, and `is_valid * (is_valid - 1)`, each of
    which vanishes at `0`. Nothing pins `is_valid` to `1`. -/
theorem apc2105000Opt_satisfiesAlgebraic_zero :
    apc2105000Opt.satisfiesAlgebraic (fun _ => 0) := by
  intro c hc
  simp only [apc2105000Opt, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Expression.eval]

/-- On that row the APC is silent: every multiplicity is `±is_valid`, which is `0`. -/
theorem apc2105000Opt_mults_zero_on_padding :
    ∀ bi ∈ apc2105000Opt.busInteractions,
      (bi.eval (fun _ => 0)).multiplicity = 0 := by
  intro bi hbi
  simp only [apc2105000Opt, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BusInteraction.eval, Expression.eval]

/-- **`Circuit.advancesClock` is false of the optimized APC**, at every window.

    The witness is the padding row. `advancesClock` demands a bridge receive with net `-1` on
    *every* algebraically-satisfying assignment; on the all-zero row this circuit nets `0` on every
    message of every bus, and `0 ≠ -1`. -/
theorem apc2105000Opt_not_advancesClock (maxWindow : ℕ) :
    ¬ apc2105000Opt.advancesClock apcRules maxWindow := by
  intro h
  obtain ⟨pcFrom, pcTo, base, d, -, -, hrecv, -⟩ :=
    h (fun _ => 0) apc2105000Opt_satisfiesAlgebraic_zero
  rw [allEffects_eq_zero_of_mults_zero apc2105000Opt_mults_zero_on_padding] at hrecv
  exact absurd hrecv (by decide)

--------- The unoptimized APC has no padding row ---------

/-- **The optimizer is what introduced the padding row.** The unoptimized APC pins each fused
    instruction's opcode-flag sum to `1` (`1 - (add + sub + xor + or + and) = 0`, one per
    instruction), so the all-zero assignment is *not* algebraically satisfying and the disproof
    above does not transfer. powdr's optimizer replaced those pinned sums with one fresh `is_valid`
    column carrying only booleanity — sound, and it destroys `Circuit.advancesClock`.

    This is the `PreservesLegality` gap of `agent-docs/legality-preservation.md`, observed in the
    wild rather than constructed. -/
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
