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

/-- One instruction step, as an execution-bridge arc: it consumes `(pcFrom, base)` and produces
    `(pcTo, base + d)`. -/
structure ClockArc (p : ℕ) where
  /-- The `pc` the instruction starts at. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p
  /-- The timestamp it starts at. -/
  base : ZMod p
  /-- How far it advances the clock. -/
  d : ℕ

/-- What one step puts on the execution bridge: `1` at the state it produces, `-1` at the state it
    consumes. -/
def ClockArc.effect (execBusId : ℕ) (α : ClockArc p) (m : BusMessage p) : ZMod p :=
  (if (execBusId, [α.pcTo, α.base + (α.d : ZMod p)]) = m then (1 : ZMod p) else 0)
    - (if (execBusId, [α.pcFrom, α.base]) = m then (1 : ZMod p) else 0)

/-- The bridge condition of `StepLayout` for a **single**-step instance, in the shape a
    hand-written executor proves it: one receive at `base`, one send `d` ticks later, and nothing
    else on the bridge. A repackaging — `ClockArc.effect` is exactly that difference of
    indicators — kept here so that the familiar three-condition form stays visible to a reader. -/
theorem ClockArc.net_singleton {c : Circuit p} {asg : ChipAssignment p} {execBusId : ℕ}
    (α : ClockArc p)
    (hne : ((execBusId, [α.pcFrom, α.base]) : BusMessage p)
      ≠ (execBusId, [α.pcTo, α.base + (α.d : ZMod p)]))
    (hrecv : c.allEffects asg (execBusId, [α.pcFrom, α.base]) = -1)
    (hsend : c.allEffects asg (execBusId, [α.pcTo, α.base + (α.d : ZMod p)]) = 1)
    (hother : ∀ m : BusMessage p, m.1 = execBusId →
      m ≠ (execBusId, [α.pcFrom, α.base]) →
      m ≠ (execBusId, [α.pcTo, α.base + (α.d : ZMod p)]) → c.allEffects asg m = 0) :
    ∀ m : BusMessage p, m.1 = execBusId →
      c.allEffects asg m = ([α].map (fun β => β.effect execBusId m)).sum := by
  intro m hm
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ClockArc.effect]
  by_cases hd : ((execBusId, [α.pcTo, α.base + (α.d : ZMod p)]) : BusMessage p) = m <;>
    by_cases hs : ((execBusId, [α.pcFrom, α.base]) : BusMessage p) = m
  · exact absurd (hs.trans hd.symm) hne
  · rw [if_pos hd, if_neg hs, sub_zero, ← hd]; exact hsend
  · rw [if_neg hd, if_pos hs, zero_sub, ← hs]; exact hrecv
  · rw [if_neg hd, if_neg hs, sub_zero]
    exact hother m hm (fun h => hs h.symm) (fun h => hd h.symm)

/-- **How a guest instance's stateful traffic is laid out in time**, under one assignment.

    The instance performs a sequence of instruction **steps** (`arcs`), totalling fewer than
    `maxWindow` ticks. Every stateful interaction it makes belongs to one of them (`place`, first
    component) and sits at an integer **offset** from that step's `base` (`place`, second
    component), somewhere in `[-maxLookback, d]`: at the step itself, or up to `maxLookback` ticks
    before it, which is where a memory *receive* lives — it names the record an earlier
    instruction left, and OpenVM's `AssertLtSubAir` range-checks the difference to
    `timestamp_max_bits` bits, so it cannot be further back than that.

    Offsets are integers, so comparing them is wraparound-free. That is what makes `ordered` and
    `sendsOk` per-chip checkable: the timestamps themselves are `ZMod p` elements whose `.val`
    order is not what any AIR constrains.

    For OpenVM (whitepaper §4.5): every instruction executor AIR "must constrain that it adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once for each instruction that appears in the AIR trace", and "must also constrain
    that `t_from < t_to`". §4.2 adds that the timestamps at which it touches guest state satisfy
    `t_from < t_{i,j} < t_to`. -/
structure StepLayout {p : ℕ} (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (maxWindow maxLookback : ℕ) where
  /-- The instruction steps this instance performs. -/
  arcs : List (ClockArc p)
  /-- Which step an interaction belongs to, and where in that step's window it sits. -/
  place : Fin c.busInteractions.length → ℕ × ℤ
  /-- Every step advances the clock. -/
  dPos : ∀ α ∈ arcs, 0 < α.d
  /-- The steps fit in the window together. -/
  dSumLt : (arcs.map (·.d)).sum < maxWindow
  /-- **The instance's bridge net is exactly what its steps put there.**

      Stated on the *sum* rather than on the exact net, which is what lets one witness serve every
      assignment: a fused APC is one step per fused instruction, and nothing algebraic chains them
      (powdr pins each instruction's `pc` to a literal but leaves its `from_state__timestamp`
      free). Where an assignment happens to chain two steps, the state between them cancels inside
      the sum; where it does not, the two stand as separate arcs. So the same clause holds of an
      APC before and after powdr's substitution pass collapses it.

      The empty list is allowed, and means the instance is a no-op — it nets zero on the bridge,
      and `placed` then leaves it no room for other stateful traffic either. That is exactly what
      an AIR's padding row is. -/
  net : ∀ m : BusMessage p, m.1 = r.execBusId →
    c.allEffects asg m = (arcs.map (fun α => α.effect r.execBusId m)).sum
  /-- Every active stateful interaction sits in the window of the step it is placed in. -/
  placed : ∀ i : Fin c.busInteractions.length,
    r.isStateful (c.busInteractions.get i).busId = true →
    (((c.busInteractions.get i).eval asg).multiplicity ≠ 0) →
      ∃ α ∈ arcs[(place i).1]?,
        -(maxLookback : ℤ) ≤ (place i).2 ∧ (place i).2 ≤ (α.d : ℤ) ∧
          r.getTimestamp (((c.busInteractions.get i).eval asg).busId,
            ((c.busInteractions.get i).eval asg).payload)
            = α.base + ((place i).2 : ZMod p)
  /-- **A send dominates everything before it in its own step.**

      Only sends are constrained: a receive may sit at a larger offset than an earlier send, and in
      a real optimized APC one does. Same-step is what makes this true of a *fused* instance, whose
      steps are not ordered relative to each other by anything algebraic. -/
  ordered : ∀ i j : Fin c.busInteractions.length, j < i →
    r.isStateful (c.busInteractions.get i).busId = true →
    r.isStateful (c.busInteractions.get j).busId = true →
    (((c.busInteractions.get j).eval asg).multiplicity ≠ 0) →
    (((c.busInteractions.get i).eval asg).multiplicity = 1) →
    (place j).1 = (place i).1 →
      (place j).2 < (place i).2
  /-- **What a guest chip sends on a stateful bus is Ok** (`GuestBusRules.payloadOk`), given that
      everything it already touched *earlier in its own step* is.

      This is the induction step that carries the memory-byte invariant: a send is justified by the
      receives that precede it, and `ordered` is what makes "precedes" an honest order on time. The
      induction itself is global — `maintains_of_stateful_active` — because what a chip *receives*
      is vouched for by whoever sent it, not by the chip.

      OpenVM §3.2.5, elements of address spaces 1 (registers) and 2 (user memory) "are constrained
      to lie in `[0, 2^8)`". In §4.6: a message appears "if and only if at timestamp `t` the data
      memory had values `data`" at that address. -/
  sendsOk : ∀ i : Fin c.busInteractions.length,
    r.isStateful (c.busInteractions.get i).busId = true →
    (((c.busInteractions.get i).eval asg).multiplicity = 1) →
    (∀ j : Fin c.busInteractions.length, j < i →
      r.isStateful (c.busInteractions.get j).busId = true →
      (((c.busInteractions.get j).eval asg).multiplicity ≠ 0) →
      (place j).1 = (place i).1 →
        r.payloadOk (((c.busInteractions.get j).eval asg).busId,
          ((c.busInteractions.get j).eval asg).payload)) →
      r.payloadOk (((c.busInteractions.get i).eval asg).busId,
        ((c.busInteractions.get i).eval asg).payload)

/-- **Every assignment a guest chip admits lays out as a sequence of instruction steps.**

    The `satisfiesStateless` hypothesis is not decoration: a real APC's timestamp-difference bound
    survives powdr's optimizer only as a range-check *payload* (the lt gadget's algebraic
    constraint is substituted away), so nothing about a memory receive's offset is derivable from
    the algebraic constraints alone. Being a hypothesis, it only weakens the clause.

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
