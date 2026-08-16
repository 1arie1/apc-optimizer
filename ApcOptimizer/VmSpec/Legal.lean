import ApcOptimizer.VmSpec.Basic

set_option autoImplicit false

/-! What a VM requires of a guest circuit before it will run it.

    These are the manuscript's per-IR legality conditions (`bus_int.tex`), and they sit in their
    own file because both sides need them: `OpenVm.lean` instantiates the `Host.legalGuest` field
    with them, and `Realizes.lean` consumes them in the balancing arguments.

    Each clause is checkable against a given circuit without reference to the rest of the VM. The
    first two are `Circuit.algebraicallyForces` — the algebraic constraints alone settle them. The
    third, `Circuit.statefulSendsMaintain`, cannot be: what a chip writes to memory is either a
    value it *read* or one it *range-checked*, and no algebraic constraint bounds either. It is
    stated conditionally instead, on the chip's own lookups, its own lower-ranked traffic, and the
    VM's rank window; see there.

    Everything here is stated against `GuestBusRules`, not `Spec.lean`'s `BusSemantics`. That is
    deliberate: `BusSemantics` carries a fourth field, `admissible`, which nothing in the VM-level
    soundness argument touches — it exists for `Circuit.isCompleteReplacementOf` — and its
    `maintainsInvariants` is a predicate on whole messages where only the payload part is ever
    used. Auditing this file should not require reading either. -/

variable {p : ℕ}

/-- **What a guest chip's legality is stated against**: the three things about the surrounding VM
    that the per-chip conditions below actually consult.

    A deliberate narrowing of `Spec.lean`'s `BusSemantics`, which has a fourth field (`admissible`,
    used only by completeness) and states its invariant on whole messages rather than payloads.

    A VM supplies these directly — see `openVmGuestRules`. Only `accepts` is *shared* with
    `BusSemantics`, and it has to be: `Circuit.satisfies`, which the chip-level theorems are stated
    against, is defined in terms of it. `isStateful` and `payloadOk` are written out instead, so
    that reading this record's instance never means unfolding a `BusSemantics`. -/
structure GuestBusRules (p : ℕ) where
  /-- Whether this bus carries VM state (memory, the execution bridge) rather than being a
      stateless lookup table. -/
  isStateful : Nat → Bool
  /-- Whether the receiving chip accepts this message — for a lookup bus, whether the tuple is in
      the table. Only consulted at nonzero multiplicity. -/
  accepts : BusInteraction (ZMod p) → Prop
  /-- Whether a *payload* on a stateful bus carries the invariant soundness depends on — for
      OpenVM, that a memory word's data limbs are bytes.

      On the payload rather than the message, because that is how it is used: a chip vouches for
      what it *sends*, and the fact has to transfer to whoever *receives* the same tuple at the
      opposite multiplicity. Nothing here mentions polarity, so nothing has to quantify it away. -/
  payloadOk : BusMessage p → Prop

/-- Every message this instance actively touches has rank below `bound` — for OpenVM, every
    memory record it reads or writes carries a timestamp inside the VM's window.

    `rank`/`bound` are the *argument's* choice, not the VM's (`Implementation/Rank.lean`); what is
    audited here is only that `Circuit.statefulSendsMaintain` may assume this of the assignment it
    is handed. -/
def Circuit.ranksBounded (c : Circuit p) (rank : BusMessage p → ℕ) (bound : ℕ)
    (asg : ChipAssignment p) : Prop :=
  ∀ bi ∈ c.busInteractions, (bi.eval asg).multiplicity ≠ 0 →
    rank ((bi.eval asg).busId, (bi.eval asg).payload) < bound

/-- Whether a circuit's **algebraic** constraints alone force `P` on every message it writes to a
    bus of the given statefulness. -/
def Circuit.algebraicallyForces (c : Circuit p) (r : GuestBusRules p) (stateful : Bool)
    (P : BusInteraction (ZMod p) → Prop) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
    ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = stateful → P (bi.eval asg)

/-- A guest chip writes only `0`/`1` multiplicities to stateless buses — the manuscript's
    `eq:legal:stateless:mult`, and OpenVM's requirement on every IR. -/
def Circuit.statelessSendOnly (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r false fun msg => msg.multiplicity = 0 ∨ msg.multiplicity = 1

/-- A guest chip writes only `0`/`±1` multiplicities to stateful buses — the manuscript's
    `eq:legal:stateful:mult`. -/
def Circuit.statefulPolarity (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r true fun msg =>
    msg.multiplicity = 0 ∨ msg.multiplicity = 1 ∨ msg.multiplicity = -1

/-- Every stateless message this instance actively sends is one the semantics accepts — the
    chip's lookups all hit their tables.

    Free to assume in `Circuit.statefulSendsMaintain` below: `statelessAccepted_of_sinks` derives
    it for every guest instance of a satisfying run from `Circuit.statelessSendOnly`, the host's
    table sinks and bus balance. No stateful clause takes part, so there is no circularity. It is
    what lets a chip point at a range check to justify a value it computed. -/
def Circuit.statelessAccepted (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p) :
    Prop :=
  ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = false →
    (bi.eval asg).multiplicity ≠ 0 → r.accepts (bi.eval asg)

/-- Everything this instance touches on a stateful bus *below* rank `bound` already maintains the
    bus invariants. The induction hypothesis of `maintains_of_stateful_active`, in the per-chip
    form `Circuit.statefulSendsMaintain` may lean on. -/
def Circuit.lowerRanksMaintain (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (asg : ChipAssignment p) (bound : ℕ) : Prop :=
  ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = true →
    (bi.eval asg).multiplicity ≠ 0 →
      rank ((bi.eval asg).busId, (bi.eval asg).payload) < bound →
        r.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload)

/-- What a guest chip *sends* on a stateful bus maintains that bus's invariants — the
    manuscript's `eq:legal:stateful:send_byte`, but conditionally.

    Sends only, and that restriction is the whole point: a chip that *reads* memory receives
    whatever was there, and demanding the receive side per-chip would assert something false. The
    receive side is derived from balancing instead (`maintains_of_stateful_active`), exactly as the
    manuscript derives `eq:legal:recv_byte` rather than assuming it.

    Three hypotheses, and none is circular:

    * `Circuit.statelessAccepted` — the chip's own lookups hold. This is how a *computed* write
      justifies itself: an OpenVM ALU range-checks the limbs it writes on the bitwise bus, and
      nothing but that lookup makes them bytes (`freshWriteChip`).
    * `Circuit.lowerRanksMaintain` at the send's own rank — everything the chip touched earlier
      was already good. This is how a *read-echo* justifies itself: OpenVM sends back the word it
      read at a fresh timestamp, and the word is byte-valued exactly because the receive it came
      from was, at a strictly smaller timestamp (`readEchoChip`).
    * `Circuit.ranksBounded` — the chip's own ranks sit inside the VM's window. This is what a
      read-echo needs to *reach* the previous clause: OpenVM's `AssertLtSubAir` bounds
      `timestamp - prev_timestamp - 1`, which orders the two only while both stay in the window
      (`RankModel.bound`, `Implementation/Rank.lean`).

    `rank` is the VM's ordering on stateful state (`RankModel.rank`; for OpenVM the memory
    timestamp). It is a natural number rather than a field element on purpose: `<` on `ℕ` is
    well-founded, so the global induction has something to descend on, and the wrap-sensitivity of
    "the timestamp went up" lands in the per-chip check of *this* predicate rather than in the
    spec. Without a rank the invariant is not derivable at all: two chips can each receive a
    non-byte word and send another one, balancing perfectly, and only strictly increasing
    timestamps rule that out. -/
def Circuit.statefulSendsMaintain (c : Circuit p) (r : GuestBusRules p)
    (rank : BusMessage p → ℕ) (rankBound : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.statelessAccepted r asg →
    c.ranksBounded rank rankBound asg →
      ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = true →
        (bi.eval asg).multiplicity = 1 →
          c.lowerRanksMaintain r rank asg (rank ((bi.eval asg).busId, (bi.eval asg).payload)) →
            r.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload)

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (rankBound : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  sendsMaintain : c.statefulSendsMaintain r rank rankBound
