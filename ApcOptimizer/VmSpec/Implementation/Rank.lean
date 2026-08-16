import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! **The soundness argument's ordering on stateful state.** Nothing here is audited.

    `maintains_of_stateful_active` derives the memory byte invariant by strong induction, and an
    induction needs something to descend on. A `RankModel` is that something: a natural-number rank
    on bus messages, plus the window inside which it is trustworthy.

    It is *not* part of the VM. No field of `Host` mentions it, and neither does `VmSat`,
    `CanProduce` or `VmEquivalent` — so a reader checking what the correctness theorem *says* never
    meets it. It appears only as a parameter of `Host.realizes`, which the argument discharges once
    per VM, and it is inferred rather than written at every use site.

    Why a wrong choice cannot make the theorem unsound: the rank occurs in the statement only
    through `Host.realizes`'s `legalGuest` field, which relates the VM's own `Host.legalGuest` to
    `Circuit.legalGuest` at this rank. A degenerate rank makes `Circuit.lowerRanksMaintain` vacuous
    and so makes legality *harder* to establish — a stronger hypothesis, hence a weaker theorem,
    never a false one. What it can do is make the hypothesis unsatisfiable, i.e. the theorem
    vacuous, which is why `OpenVmLegalAudit.lean` exhibits real chips that meet it. -/

variable {p : ℕ}

/-- A rank on stateful bus messages together with the window it is valid in.

    For OpenVM: a memory record's timestamp, and `2 ^ timestamp_max_bits`. A rank reads a field
    element as a natural number, so "the rank went up" is the order it looks like only while ranks
    stay inside a window too narrow to wrap — which is what `bound` records, and what
    `Host.pinsRanks` claims of a run. -/
structure RankModel (p : ℕ) where
  /-- How the argument orders stateful state — for OpenVM, a memory record's timestamp. -/
  rank : BusMessage p → ℕ
  /-- How far `rank` may reach in a run the VM will accept. -/
  bound : ℕ

/-- Every guest instance's traffic stays inside the rank window.

    Needed to prevent overflow, but of a different kind than `VmAssignment.withinBudget`: not in a
    multiplicity but in the rank itself.

    Not a conjunct of `VmSat`, because no OpenVM AIR checks it: the connector constrains the two
    timestamps on its own two rows, and a memory access constrains only the *difference* across it.
    That every timestamp in between is in range is a multi-chip consequence, and deriving it is
    this argument's job rather than its premise — see `Host.pinsRanks`. -/
def VmAssignment.withinRankBound {vm : Vm p} (a : VmAssignment p vm) (rm : RankModel p) : Prop :=
  ∀ t : Fin vm.guest.length, ∀ asg ∈ a.guestAssignments t,
    (vm.guest.get t).ranksBounded rm.rank rm.bound asg
