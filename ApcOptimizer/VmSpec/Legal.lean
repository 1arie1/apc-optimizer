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

/-- Every active interaction has rank below `bound`, under rank function `rank`.

    See `Circuit.statefulSendsMaintain`. -/
def Circuit.ranksBounded (c : Circuit p) (rank : BusMessage p → ℕ) (bound : ℕ)
    (asg : ChipAssignment p) : Prop :=
  ∀ bi ∈ c.busInteractions, (bi.eval asg).multiplicity ≠ 0 →
    rank ((bi.eval asg).busId, (bi.eval asg).payload) < bound

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

/-- All stateful interactions below this rank are Ok.

    See `Circuit.statefulSendsMaintain`. -/
def Circuit.lowerRanksMaintain (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (asg : ChipAssignment p) (bound : ℕ) : Prop :=
  ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = true →
    (bi.eval asg).multiplicity ≠ 0 →
      rank ((bi.eval asg).busId, (bi.eval asg).payload) < bound →
        r.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload)

/-- What a guest chip *sends* on a stateful bus is Ok (`BusRules.payloadOk`).

    Technically, given a ranking function & bound, for any assignment that:

    * satisfies the chip's algebraic constraints (`Circuit.satisfiesAlgebraic`),
    * and its stateless buses (`Circuit.satisfiesStateless`),
    * and assigns in-bound ranks to all active stateful messages (`Circuit.ranksBounded`),
    * for all stateful bus interactions it actively sends (`multiplicity ≠ 0`), and
    * assuming all lower-rank interactions are Ok (`Circuit.lowerRanksMaintain`),

    this interaction is Ok too (`BusRules.payloadOk`).

    This implication sets up an induction on rank to prove that all interactions are Ok. That
    induction is necessary, which is why we need this clause.

    This clause only applies to assignments with in-bound ranks. At first that might seem fishy,
    since it is not clear that the VM guarentees in-bound ranks for satisfying assignments! But,
    the VM does guarantee that in a complex way, see `Host.pinsRanks`. Since that argument is global
    (relies on all chips and the host), we cannot use that argument locally (in this single-chip
    context). Instead, we assume that the assignment is in-bound, and combine this condition's
    conclusion with `Host.pinsRanks` elsewhere.

    Also, note that from a correctness perspective, additional hypotheses are harmless, since they
    weaken legality---they make it easier for a chip to be legal. So, the above discussion is more
    about why the substitution proof goes through, despite this oddly weak legality condition.

    OpenVM §3.2.5, elements of address spaces 1 (registers) and 2 (user memory) "are constrained to
    lie in `[0, 2^8)`". In §4.6: a message appears "if and only if at timestamp `t` the data memory
    had values `data`" at that address. -/
def Circuit.statefulSendsMaintain (c : Circuit p) (r : GuestBusRules p)
    (rank : BusMessage p → ℕ) (rankBound : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    -- TODO(AO): AG and I were worried about this clause's location, but actually it is correct. See
    -- the revised comment above. We should discuss.
    c.ranksBounded rank rankBound asg →
      ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = true →
        (bi.eval asg).multiplicity = 1 →
          c.lowerRanksMaintain r rank asg (rank ((bi.eval asg).busId, (bi.eval asg).payload)) →
            r.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload)

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

/-- The bridge condition of `Circuit.advancesClock` for a **single**-step instance, in the shape a
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

/-- **A guest instance performs a sequence of instruction steps**, totalling fewer than `maxWindow`
    ticks, and every memory access it makes sits strictly inside one of them.

    For OpenVM (whitepaper §4.5): every instruction executor AIR "must constrain that it adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once for each instruction that appears in the AIR trace", and "must also constrain
    that `t_from < t_to`". §4.2 adds that the timestamps at which it touches guest state satisfy
    `t_from < t_{i,j} < t_to`.

    A *list* of steps rather than one, because a fused APC is one step per fused instruction and
    nothing algebraic chains them — powdr pins each instruction's `pc` to a literal but leaves its
    `from_state__timestamp` free, and only bus balance ties them together. The bridge condition is
    therefore stated on the **sum** of the steps' effects rather than on the exact net: where an
    assignment happens to chain two steps, the state between them cancels inside the sum, and where
    it does not, the two stand as separate arcs. One witness serves both, so the same clause holds
    of an APC before and after powdr's substitution pass collapses it.

    The empty list is allowed, and means the instance is a no-op: it nets zero on the bridge and
    the memory condition leaves it no room for memory traffic either. That is exactly what an AIR's
    padding row is.

    This is needed to avoid timestamp overflow, enabling inductions on time, like the one mentioned
    above in `Circuit.statefulSendsMaintain`.  -/
def Circuit.advancesClock (c : Circuit p) (r : GuestBusRules p) (maxWindow : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
    ∃ arcs : List (ClockArc p),
      -- Every step advances the clock, and they fit in the window together.
      (∀ α ∈ arcs, 0 < α.d) ∧
      (arcs.map (·.d)).sum < maxWindow ∧
      -- The instance's bridge net is exactly what its steps put there.
      (∀ m : BusMessage p, m.1 = r.execBusId →
        c.allEffects asg m = (arcs.map (fun α => α.effect r.execBusId m)).sum) ∧
      -- Every memory access sits strictly inside one of the steps.
      (∀ bi ∈ c.busInteractions, bi.busId = r.memBusId → (bi.eval asg).multiplicity ≠ 0 →
        ∃ α ∈ arcs, ∃ δ : ℕ, 0 < δ ∧ δ < α.d ∧
          r.getTimestamp ((bi.eval asg).busId, (bi.eval asg).payload) = α.base + (δ : ZMod p))

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field.

    See the consituent fields for the conditions. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (rankBound maxWindow maxInteractions : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  sendsMaintain : c.statefulSendsMaintain r rank rankBound
  advancesClock : c.advancesClock r maxWindow
  size : c.busInteractions.length ≤ maxInteractions
