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

/-- **How a guest instance's stateful traffic is laid out in time**, under one assignment.

    The instance performs one instruction **step**, advancing the clock by fewer than `maxWindow`
    ticks: it receives `(pcFrom, base)` from the execution bridge, sends
    `(pcTo, base + d)` back, and puts nothing else there (`recv`, `send`, `other` — OpenVM
    whitepaper §4.5, an executor "adds a message `(pc_from, t_from)` to the receive set and a
    message `(pc_to, t_to)` to the send set exactly once", and "must also constrain that
    `t_from < t_to`").

    Every stateful interaction it makes sits at an integer **offset** (`place`) from that step's
    `base`, somewhere in `[-maxLookback, d]`: inside the step, or up to `maxLookback` ticks before
    it, which is where a memory *receive* lives — it names the record an earlier instruction left,
    and OpenVM's `AssertLtSubAir` range-checks the difference to `timestamp_max_bits` bits, so it
    cannot be further back than that. (§4.2 puts guest-state timestamps at `t_from < t < t_to`; the
    lookback is where a real chip differs, and `placed` is the honest version.)

    Offsets are integers, so comparing them is wraparound-free. That is what makes `ordered` and
    `sendsOk` per-chip checkable: the timestamps themselves are `ZMod p` elements whose `.val`
    order is not what any AIR constrains.

    A **fused** APC is one instance covering several instructions, and it is laid out by this
    clause only once its intermediate bridge states cancel. Powdr pins each fused instruction's
    `pc` to a literal, so consecutive ones already chain there; the missing half is the timestamps.
    With `from_state__timestamp_{i+1} = from_state__timestamp_i + d_i` the six intermediate
    messages of a four-instruction APC cancel against each other (their multiplicities are the
    per-block opcode-flag sums, each pinned to `1`) and the net is the single pair above. Without
    those equations the timestamps are free — each occurs only in its own lt gadget — the instance
    genuinely nets one step per fused instruction, and it is *not* legal by this clause. -/
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
  /-- Where in the step's window each interaction sits. -/
  place : Fin c.busInteractions.length → ℤ
  /-- The step advances the clock. -/
  dPos : 0 < d
  /-- …and fits in the window. -/
  dLt : d < maxWindow
  /-- **The instance receives the state its step consumes**, exactly once. -/
  recv : c.allEffects asg (r.execBusId, [pcFrom, base]) = -1
  /-- **…and sends the state it produces**, `d` ticks later, exactly once. -/
  send : c.allEffects asg (r.execBusId, [pcTo, base + (d : ZMod p)]) = 1
  /-- **…and puts nothing else on the bridge**, which is what makes those two "exactly once". -/
  other : ∀ m : BusMessage p, m.1 = r.execBusId →
    m ≠ (r.execBusId, [pcFrom, base]) →
    m ≠ (r.execBusId, [pcTo, base + (d : ZMod p)]) →
      c.allEffects asg m = 0
  /-- Every active stateful interaction sits in the step's window. -/
  placed : ∀ i : Fin c.busInteractions.length, c.activeStateful r asg i →
    -(maxLookback : ℤ) ≤ place i ∧ place i ≤ (d : ℤ) ∧
      r.getTimestamp (c.msgAt asg i) = base + ((place i : ℤ) : ZMod p)
  /-- **A send dominates everything before it.**

      Only sends are constrained: a receive may sit at a larger offset than an earlier send, and in
      a real optimized APC one does (its second read is at offset `1 - n`, after a write at `0`). -/
  ordered : ∀ i j : Fin c.busInteractions.length, j < i →
    c.statefulSend r asg i → c.activeStateful r asg j → place j < place i
  /-- **What a guest chip sends on a stateful bus is Ok** (`GuestBusRules.payloadOk`), given that
      everything it already touched is.

      This is the induction step that carries the memory-byte invariant: a send is justified by the
      receives that precede it, and `ordered` is what makes "precedes" an honest order on time. The
      induction itself is global — `maintains_of_stateful_active` — because what a chip *receives*
      is vouched for by whoever sent it, not by the chip.

      OpenVM §3.2.5, elements of address spaces 1 (registers) and 2 (user memory) "are constrained
      to lie in `[0, 2^8)`". In §4.6: a message appears "if and only if at timestamp `t` the data
      memory had values `data`" at that address. -/
  sendsOk : ∀ i : Fin c.busInteractions.length, c.statefulSend r asg i →
    (∀ j : Fin c.busInteractions.length, j < i → c.activeStateful r asg j →
      r.payloadOk (c.msgAt asg j)) →
    r.payloadOk (c.msgAt asg i)

/-- What the step puts on the execution bridge: `1` at the state it produces, `-1` at the state it
    consumes. Reads only `pcFrom`, `pcTo`, `base` and `d`. -/
def StepLayout.effect {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {maxWindow maxLookback : ℕ} (L : StepLayout c r asg maxWindow maxLookback)
    (m : BusMessage p) : ZMod p :=
  (if (r.execBusId, [L.pcTo, L.base + (L.d : ZMod p)]) = m then (1 : ZMod p) else 0)
    - (if (r.execBusId, [L.pcFrom, L.base]) = m then (1 : ZMod p) else 0)

/-- A step's two bridge endpoints are distinct: were they equal, `recv` and `send` would make the
    same net both `-1` and `1`. -/
theorem StepLayout.endpoints_ne {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {maxWindow maxLookback : ℕ} (L : StepLayout c r asg maxWindow maxLookback)
    (h2 : (-1 : ZMod p) ≠ 1) :
    ((r.execBusId, [L.pcFrom, L.base]) : BusMessage p)
      ≠ (r.execBusId, [L.pcTo, L.base + (L.d : ZMod p)]) := by
  intro h
  have hr := L.recv
  rw [h, L.send] at hr
  exact h2 hr.symm

/-- **The instance's bridge net is exactly what its step puts there.** The `recv`/`send`/`other`
    triple repackaged as a single equation, which is the form the chain argument consumes. -/
theorem StepLayout.net {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {maxWindow maxLookback : ℕ} (L : StepLayout c r asg maxWindow maxLookback)
    (h2 : (-1 : ZMod p) ≠ 1) :
    ∀ m : BusMessage p, m.1 = r.execBusId → c.allEffects asg m = L.effect m := by
  intro m hm
  simp only [StepLayout.effect]
  by_cases hd : ((r.execBusId, [L.pcTo, L.base + (L.d : ZMod p)]) : BusMessage p) = m <;>
    by_cases hs : ((r.execBusId, [L.pcFrom, L.base]) : BusMessage p) = m
  · exact absurd (hs.trans hd.symm) (L.endpoints_ne h2)
  · rw [if_pos hd, if_neg hs, sub_zero, ← hd]; exact L.send
  · rw [if_neg hd, if_pos hs, zero_sub, ← hs]; exact L.recv
  · rw [if_neg hd, if_neg hs, sub_zero]
    exact L.other m hm (fun h => hs h.symm) (fun h => hd h.symm)

/-- **Every assignment a guest chip admits lays out as one instruction step.**

    The `satisfiesStateless` hypothesis is not decoration: a real APC's timestamp-difference bound
    survives powdr's optimizer only as a range-check *payload* (the lt gadget's algebraic
    constraint is substituted away, and `15360 = -1/2^17` in BabyBear), so nothing about a memory
    receive's offset is derivable from the algebraic constraints alone. Being a hypothesis, it only
    weakens the clause.

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
