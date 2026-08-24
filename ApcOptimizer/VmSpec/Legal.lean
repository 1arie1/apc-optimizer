import ApcOptimizer.VmSpec.Basic

set_option autoImplicit false

/-! What a VM requires of a guest circuit to run it correctly.

    Defines a property `Circuit.legalGuest` of an individual circuit, and **not** with respect to a
    concrete assignemnt.

    Everything here is stated against `GuestBusRules`, not `Spec.lean`'s `BusSemantics`. That is
    deliberate: `BusSemantics` carries a fourth field, `admissible`, which is hard to audit. -/

variable {p : ℕ}

/-- Host-specific bus rules that legality depends on. -/
structure GuestBusRules (p : ℕ) where
  /-- Whether this bus ID carries VM state (memory, the execution bridge), rather than being a
      stateless lookup table. -/
  isStateful : Nat → Bool
  /-- For a stateless bus, whether the receiving chip accepts this message. I.e., if it is in the
      table. -/
  accepts : BusInteraction (ZMod p) → Prop
  /-- Whether a *payload* on a stateful bus is Ok, i.e., respects VM invariants.  This `Prop`
      defines the invariant. Elsewhere, we inductively prove it everywhere it is needed.

      For OpenVM: that a memory send's data limbs are bytes. -/
  payloadOk : BusMessage p → Prop
  execBusId : Nat
  memBusId : Nat
  /-- How to get the timestamp for a memory access. -/
  getTimestamp : BusMessage p → ZMod p
  /-- Off the memory bus, a stateful message's payload carries no invariant at all — `payloadOk`
      is the memory-byte invariant specifically, not a general property of every stateful bus.
      This is what lets `StepLayout.memOrdered`/`memSendsOk` restrict their reach to the memory
      bus without losing anything: an execution-bridge (or other stateful, non-memory) message is
      `payloadOk` unconditionally. -/
  memPayloadOnly : ∀ m : BusMessage p, isStateful m.1 = true → m.1 ≠ memBusId → payloadOk m

/-- Whether a circuit's **algebraic** constraints alone force property `P` on every message it
    writes to a bus of the given statefulness. -/
def Circuit.algebraicallyForces (c : Circuit p) (r : GuestBusRules p) (stateful : Bool)
    (P : BusInteraction (ZMod p) → Prop) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
    ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = stateful → P (bi.eval asg)

/-- A guest chip writes only `0`/`1` multiplicities to stateless buses

    OpenVM §2.2.4: multiset balancing implies lookup-table relations only "under certain conditions
    which prevent integer overflow of the field characteristic". This is that condition on the
    lookup side. -/
def Circuit.statelessSendOnly (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r false fun msg => msg.multiplicity = 0 ∨ msg.multiplicity = 1

/-- A guest chip writes only `0`/`±1` multiplicities to stateful buses.

    OpenVM §4.5, an instruction executor adds `(pc_from, t_from)` to the execution bus's receive set
    and `(pc_to, t_to)` to its send set "exactly once for each instruction"; and §4.6.1, a read or a
    write adds one memory message to each set. -/
def Circuit.statefulPolarity (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r true fun msg =>
    msg.multiplicity = 0 ∨ msg.multiplicity = 1 ∨ msg.multiplicity = -1

/-- This assignment respects the table semantics of stateless buses.

    See `Circuit.statelessSendsMaintain`. -/
def Circuit.satisfiesStateless (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p) :
    Prop :=
  ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = false →
    (bi.eval asg).multiplicity ≠ 0 → r.accepts (bi.eval asg)

/-- The message the `i`th interaction writes under `asg`: its bus and payload, dropping the
    multiplicity. -/
def Circuit.msgAt (c : Circuit p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : BusMessage p :=
  (((c.busInteractions.get i).eval asg).busId, ((c.busInteractions.get i).eval asg).payload)

/-- The multiplicity the `i`th interaction writes under `asg`. -/
def Circuit.multAt (c : Circuit p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : ZMod p :=
  ((c.busInteractions.get i).eval asg).multiplicity

/-- The `i`th interaction is on a stateful bus and actually happens. -/
def Circuit.activeStateful (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  r.isStateful (c.busInteractions.get i).busId = true ∧ c.multAt asg i ≠ 0

/-- …and is a *send*. -/
def Circuit.statefulSend (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  r.isStateful (c.busInteractions.get i).busId = true ∧ c.multAt asg i = 1

/-- The layout of a guest instance's stateful traffic in time.

    The instance performs one instruction step, advancing the clock by fewer than `maxWindow` ticks:
    it receives `(pcFrom, base)` from the execution bridge, sends `(pcTo, base + d)` back, and puts
    nothing else there (`recv`, `send`, `other` — OpenVM whitepaper §4.5, an executor "adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once", and "must also constrain that `t_from < t_to`").

    Every stateful interaction it makes sits at an integer offset (`place`) from that step's `base`,
    somewhere in `[-maxLookback, d]`: inside the step, or up to `maxLookback` ticks before it, which
    is where a memory *receive* lives — it names the record an earlier instruction left, and
    OpenVM's `AssertLtSubAir` range-checks the difference to `timestamp_max_bits` bits, so it cannot
    be further back than that. (§4.2 puts guest-state timestamps at `t_from < t < t_to`)

    Offsets are integers---not field elements, hence comparisons work. The timestamps are `ZMod p`
    elements.

    This assumes that a **fused** APC equates adjacent timestamps on the execution bridge, so that
    the step's `d` is the sum of the fused instructions' `d_i`.

    **NB**: currently, powdr does not do this equation, so the timestamps are free. That is odd and
    I am not sure if somehow we can derive the equations through a global argument. Even if we can,
    it certainly makes the local legality definition harder. I think they should just add the
    equations to the fused APCs---I think that is their intent.
    -/
structure StepLayout {p : ℕ} (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (maxWindow maxLookback : ℕ) where
  /-- The `pc` the step starts at. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p
  /-- The timestamp it starts at. -/
  base : ZMod p
  /-- How far it advances the clock. -/
  d : ℕ
  /-- Where in the step's window each interaction sits.
      Receives from previous steps get negative values. -/
  place : Fin c.busInteractions.length → ℤ
  /-- The step *advances* the clock. -/
  dPos : 0 < d
  /-- ... and fits in the window. -/
  dLt : d < maxWindow
  /-- We receive `(pcFrom, base)` on the bridge -/
  recv : c.allEffects asg (r.execBusId, [pcFrom, base]) = -1
  /-- We send `(pcTo, base+d)` on the bridge -/
  send : c.allEffects asg (r.execBusId, [pcTo, base + (d : ZMod p)]) = 1
  /-- ... and nothing else. -/
  other : ∀ m : BusMessage p, m.1 = r.execBusId →
    m ≠ (r.execBusId, [pcFrom, base]) →
    m ≠ (r.execBusId, [pcTo, base + (d : ZMod p)]) →
      c.allEffects asg m = 0
  /-- Every active stateful interaction is placed in the step's window. -/
  placed : ∀ i : Fin c.busInteractions.length, c.activeStateful r asg i →
    -(maxLookback : ℤ) ≤ place i ∧ place i ≤ (d : ℤ) ∧
      r.getTimestamp (c.msgAt asg i) = base + ((place i : ℤ) : ZMod p)
  /-- Every *memory* send is placed *after* prior *memory* interactions. Restricted to the memory
      bus, not every stateful one: `memPayloadOnly` already settles the execution bridge (and any
      other stateful, non-memory bus) unconditionally, so ordering them buys nothing, and — for a
      circuit chaining several unfused instruction steps — insisting on it would force a total
      order on messages that are only coincidentally simultaneous in time (two steps' own
      bookkeeping can legitimately land on the same field timestamp without either justifying the
      other's memory byte invariant). -/
  memOrdered : ∀ i j : Fin c.busInteractions.length, j < i →
    c.statefulSend r asg i → (c.busInteractions.get i).busId = r.memBusId →
    c.activeStateful r asg j → (c.busInteractions.get j).busId = r.memBusId →
    place j < place i
  /-- Each memory send is Ok, given that prior memory interactions are Ok.

      This is the induction that carries the memory-byte invariant: a send is justified by the
      receives that precede it. The induction is on timestamps, but `memOrdered` couples that to
      syntactic index for the sends. Restricted to the memory bus for the same reason
      `memOrdered` is — `memPayloadOnly` already settles every other stateful bus.

      OpenVM §3.2.5, elements of address spaces 1 (registers) and 2 (user memory) "are constrained
      to lie in `[0, 2^8)`". In §4.6: a message appears "if and only if at timestamp `t` the data
      memory had values `data`" at that address. -/
  memSendsOk : ∀ i : Fin c.busInteractions.length, c.statefulSend r asg i →
    (c.busInteractions.get i).busId = r.memBusId →
    (∀ j : Fin c.busInteractions.length, j < i → c.activeStateful r asg j →
      (c.busInteractions.get j).busId = r.memBusId → r.payloadOk (c.msgAt asg j)) →
    r.payloadOk (c.msgAt asg i)

/-- Every assignment a guest chip admits lays out as one instruction step.

    Needed to avoid timestamp overflow, and to give the soundness argument's induction something to
    descend on. -/
def Circuit.hasStepLayout (c : Circuit p) (r : GuestBusRules p) (maxWindow maxLookback : ℕ) :
    Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    Nonempty (StepLayout c r asg maxWindow maxLookback)

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field.

    See the consituent fields for the conditions. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p)
    (maxWindow maxLookback maxInteractions : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  stepLayout : c.hasStepLayout r maxWindow maxLookback
  size : c.busInteractions.length ≤ maxInteractions
