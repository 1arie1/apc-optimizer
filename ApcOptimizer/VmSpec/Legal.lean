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
  /-- Which bus is the execution bridge and which is memory, and how to read a message's own
      timestamp off its payload — what `Circuit.advancesClock`'s temporal contract needs. Naming
      them here, rather than passing them as loose parameters wherever `advancesClock` is
      invoked, is what lets it become a field of `Circuit.legalGuest` below instead of a
      condition bolted on separately by each VM's `Host.legalGuest`. -/
  execBusId : Nat
  memBusId : Nat
  getTimestamp : BusMessage p → ZMod p

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

/-- **One instruction, bounded clock steps** — a VM's temporal contract on an instruction
    executor, and the missing premise that makes a run's timestamps orderable.

    For OpenVM (whitepaper §4.5): every instruction executor AIR "must constrain that it adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once for each instruction that appears in the AIR trace", and "must also constrain
    that `t_from < t_to`". §4.2 adds that the timestamps at which it touches guest state satisfy
    `t_from < t_{i,j} < t_to`.

    The advance `d` and the memory offsets `δ` are *natural numbers*, and every timestamp is given
    as `base + δ` rather than by comparing `.val`s. That is what makes the clause wrap-free: it
    says where a timestamp sits relative to the instruction's own start, which is a statement no
    field wraparound can spoof, and it is why this — unlike `Circuit.statefulSendsMaintain` — needs
    no rank window as a hypothesis. Establishing that window is precisely what it is for.

    `r.getTimestamp` is how a VM reads a message's own timestamp off its payload (for OpenVM,
    `openVmMemTimestamp`, payload index `6`) — a fixed VM-wide convention, the same way
    `r.execBusId`/`r.memBusId` are, so it lives on `r` too rather than as a parameter here.
    `maxWindow` bounds the advance and is *not* such a fixed convention — it is a property of the
    instruction set rather than the VM state: for the RV32 chips the advance is a literal
    `timestamp_delta`, but a fused APC advances by its whole basic block, so it stays a parameter
    here (like `rankBound`) instead of living on `r`. Every clause is a statement about the
    evaluated interactions of a satisfying assignment, so a static pass over a chip's timestamp
    expressions decides it; the intended recognizer is "exactly two execution-bridge interactions,
    at literal multiplicities `1` and `-1`, whose timestamp expressions differ by a literal". -/
def Circuit.advancesClock (c : Circuit p) (r : GuestBusRules p) (maxWindow : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
    ∃ (pcFrom pcTo base : ZMod p) (d : ℕ),
      0 < d ∧ d < maxWindow ∧
      -- Exactly one bridge receive, at the instruction's start.
      c.allEffects asg (r.execBusId, [pcFrom, base]) = -1 ∧
      -- Exactly one bridge send, `d` ticks later.
      c.allEffects asg (r.execBusId, [pcTo, base + (d : ZMod p)]) = 1 ∧
      -- (Nothing else on the bridge---making the "exactly" above meaningful.)
      (∀ m : BusMessage p, m.1 = r.execBusId → m ≠ (r.execBusId, [pcFrom, base]) →
        m ≠ (r.execBusId, [pcTo, base + (d : ZMod p)]) → c.allEffects asg m = 0) ∧
      -- Every memory access sits strictly inside the step.
      (∀ bi ∈ c.busInteractions, bi.busId = r.memBusId → (bi.eval asg).multiplicity ≠ 0 →
        ∃ δ : ℕ, 0 < δ ∧ δ < d ∧
          r.getTimestamp ((bi.eval asg).busId, (bi.eval asg).payload) = base + (δ : ZMod p))

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (rankBound : ℕ) (maxWindow : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  sendsMaintain : c.statefulSendsMaintain r rank rankBound
  advancesClock : c.advancesClock r maxWindow
