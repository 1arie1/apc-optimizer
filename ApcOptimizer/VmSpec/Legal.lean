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

/-- Every guest chip increases the clock by at most `maxWindow` ticks, and every memory access sits
    strictly inside that time interval.

    For OpenVM (whitepaper §4.5): every instruction executor AIR "must constrain that it adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once for each instruction that appears in the AIR trace", and "must also constrain
    that `t_from < t_to`". §4.2 adds that the timestamps at which it touches guest state satisfy
    `t_from < t_{i,j} < t_to`.

    This is needed to avoid timestamp overflow, enabling inductions on time, like the one mentioned
    above in `Circuit.statefulSendsMaintain`.  -/
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

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field.

    See the consituent fields for the conditions. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p) (rank : BusMessage p → ℕ)
    (rankBound maxWindow maxInteractions : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  sendsMaintain : c.statefulSendsMaintain r rank rankBound
  advancesClock : c.advancesClock r maxWindow
  size : c.busInteractions.length ≤ maxInteractions
