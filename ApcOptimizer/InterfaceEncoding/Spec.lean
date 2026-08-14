import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Interface-encoding metatheory: the audited definitions

A standalone metatheory justifying the *interface encoding* of the memory bus used by an
external SMT equivalence verifier. The encoding replaces all memory semantics by a
rely/guarantee contract over a 1:1 matching of the two circuits' bus traffic: per matched
pair, receive-tuple equalities are assumed and send-tuple equalities are proof obligations.
Semantically, a memory receive is a *nondeterministic input* — nothing in a single circuit
constrains its data beyond the invariants `BusSemantics.accepts` grants (e.g. byte-ness) —
and the matching says the two circuits exchange identical traffic with that environment.

This file holds the definitions; the theorems are stated in
`ApcOptimizer/InterfaceEncoding.lean` (with proof machinery under
`ApcOptimizer/Implementation/InterfaceEncoding/`, which needs no audit): abstract
equivalence implies concrete equivalence, and the closure semantics below grounds the
observable — identical traffic means identical closed compositions with every memory
environment.

Two deliberate divergences from `ApcOptimizer/Spec.lean`:
* `ConcreteEquiv` is symmetric with an *existential* witness in both directions, unlike
  `Circuit.isCompleteReplacementOf`, whose witness is pinned to `Derivations.witgen` — this
  theory serves an external equivalence verifier, not the optimizer's witness generator.
  The divergence is bridged by keeping the witness rather than weakening the Spec:
  `ReplacesWithVia` is the same relation along a *given* witness map, it forgets down to
  `ReplacesWith`, and along `Derivations.witgen ds` it lands `isCompleteReplacementOf`.
* `ConcreteEquiv` carries no `guaranteesInvariants` clause: interface data says nothing
  about *stateless* interactions, whose `maintainsInvariants` (multiplicity pinned to `1`)
  does not follow from `accepts` — an accepted lookup message sent with multiplicity `2`
  satisfies every `accepts` clause yet violates the invariant. The bridge
  `isSoundReplacementOf_of_concreteEquiv` takes that clause as a hypothesis, and
  `statefulInvariants_of_abstractEquiv` proves the derivable stateful fragment.

Each notion comes in an exact form and a removal-tolerant one, the latter suffixed `UpTo`
(match, abstract equivalence) or built on `MonoPair` (concrete equivalence, replacement).
The exact forms are the special case of no removal and are kept because their admissibility
clause is a genuine `↔`; see `InterfaceMatchUpTo` for what a removal costs.
-/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-! ## The interface data and match -/

/-- The evaluated messages of the circuit's *active stateful* interactions — syntactically
    the list `Circuit.admissible` judges (`admissible_def`). This is the interface data: the
    traffic the circuit exchanges with the stateful environment. -/
def activeStateful (circuit : Circuit p) (bs : BusSemantics p)
    (assignment : Variable → ZMod p) : List (BusInteraction (ZMod p)) :=
  (circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
    (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)

/-- `Circuit.admissible` is the bus rely on exactly the interface data. -/
theorem admissible_def (circuit : Circuit p) (bs : BusSemantics p)
    (assignment : Variable → ZMod p) :
    circuit.admissible bs assignment ↔ bs.admissible (activeStateful circuit bs assignment) :=
  Iff.rfl

/-- The interface match between two runs: the active stateful message lists agree up to a
    bijective 1:1 pairing with per-pair equal bus, multiplicity, and payload tuple — i.e. a
    permutation. This is what the verifier's per-aligned-pair tuple equalities certify. -/
def InterfaceMatch (bs : BusSemantics p) (A B : Circuit p)
    (a b : Variable → ZMod p) : Prop :=
  (activeStateful A bs a).Perm (activeStateful B bs b)

/-! ## Removal-tolerant matching: internal pairs -/

/-- The message that cancels `m`: same bus and tuple, opposite multiplicity. An involution
    that preserves everything the address projection and the side effects read, and swaps
    the roles of `sendsAt` and `recvsAt`. -/
def flipMult (m : BusInteraction (ZMod p)) : BusInteraction (ZMod p) :=
  { m with multiplicity := -m.multiplicity }

/-- Traffic that cancels within the block: a list of messages together with a cancelling
    counterpart of each. This is what an optimizer removes when it drops an
    internally-matched send/receive pair (powdr's `busUnify`; the verifier's *internal
    pairs*), and no environment can see it — it contributes nothing to
    `Circuit.sideEffects` (the net multiplicity per tuple is zero), nothing to the memory
    rely's per-address excess (it adds the same payload to the receives and to the sends),
    and nothing to a closing environment (`interfaceMatchUpTo_closes_iff`).

    Deliberately unconstrained beyond the pairing: neither a multiplicity range nor
    statefulness is needed for any of the three, and `InterfaceMatchUpTo` places `D` inside
    `activeStateful` anyway. -/
def InternallyBalanced (D : List (BusInteraction (ZMod p))) : Prop :=
  ∃ S : List (BusInteraction (ZMod p)), D.Perm (S ++ S.map flipMult)

/-- The interface match, tolerating removals: `A`'s traffic is `B`'s together with
    internally-balanced traffic `D`. `InterfaceMatch` is the case `D = []`
    (`interfaceMatchUpTo_of_interfaceMatch`).

    The asymmetry is the point: `B` — the optimized circuit — may cancel pairs that `A`
    carries, so the two traffics are not permutations, and the transfer chain must be
    re-established rather than inherited. All of it survives except one half of one clause:
    the rely transports only *downward* (`AdmissibleDropInvariant`, `ReplacesWithMono`),
    because a dropped message's ∀-style conjuncts — a timestamp bound, `x0ReturnsZero` —
    cannot be reinstated from `B`'s traffic alone. -/
def InterfaceMatchUpTo (bs : BusSemantics p) (A B : Circuit p)
    (a b : Variable → ZMod p) : Prop :=
  ∃ D : List (BusInteraction (ZMod p)), InternallyBalanced D ∧
    (activeStateful A bs a).Perm (activeStateful B bs b ++ D)

/-- The stateful interactions of a circuit, *syntactically*: statefulness is a property of
    the data-level `busId`, so this sublist is independent of the assignment. -/
def statefulInteractions (circuit : Circuit p) (bs : BusSemantics p) :
    List (BusInteraction (Expression p)) :=
  circuit.busInteractions.filter (fun bi => bs.isStateful bi.busId)

/-- Per-pair equality along a *circuit-level* alignment: `σ` pairs the two circuits'
    syntactic stateful interactions — one bijection, fixed before any assignment is chosen,
    the Lean shadow of the verifier's `kept_pairs` — and the two runs make every pair
    evaluate to the same message (multiplicity and payload). A per-assignment pairing would
    be no stronger than `InterfaceMatch` itself; the certificate's strength is that the SAME
    `σ` serves every assignment and both proof directions
    (`abstractEquivUnder_of_aligned`). -/
def AlignedMatch (bs : BusSemantics p) (A B : Circuit p)
    (σ : Fin (statefulInteractions A bs).length ≃ Fin (statefulInteractions B bs).length)
    (a b : Variable → ZMod p) : Prop :=
  ∀ i, ((statefulInteractions A bs).get i).eval a
    = ((statefulInteractions B bs).get (σ i)).eval b

/-! ## Abstract and concrete equivalence -/

/-- Equivalence in the abstract semantics: every satisfying run of either circuit is matched
    by a satisfying run of the other with identical interface traffic. Receives are
    nondeterministic inputs here — a "run" is any satisfying assignment, so the ∃-side must
    reproduce the ∀-side's traffic whatever the environment supplied. -/
def AbstractEquiv (bs : BusSemantics p) (A B : Circuit p) : Prop :=
  (∀ a, A.satisfies bs a → ∃ b, B.satisfies bs b ∧ InterfaceMatch bs A B a b) ∧
  (∀ b, B.satisfies bs b → ∃ a, A.satisfies bs a ∧ InterfaceMatch bs A B a b)

/-- `AbstractEquiv` with the ∀-side restricted to runs whose interface messages satisfy an
    invariant `I` — the verifier's premise channel, which grants environment facts (e.g.
    "received memory data are bytes") on the reference side only. Harmless when `accepts`
    already entails `I` (`abstractEquiv_of_under`). -/
def AbstractEquivUnder (bs : BusSemantics p) (I : BusInteraction (ZMod p) → Prop)
    (A B : Circuit p) : Prop :=
  (∀ a, A.satisfies bs a → (∀ m ∈ activeStateful A bs a, I m) →
    ∃ b, B.satisfies bs b ∧ InterfaceMatch bs A B a b) ∧
  (∀ b, B.satisfies bs b → (∀ m ∈ activeStateful B bs b, I m) →
    ∃ a, A.satisfies bs a ∧ InterfaceMatch bs A B a b)

/-- `AbstractEquiv` over the removal-tolerant match. `A` is the traffic-richer circuit in
    both clauses — whichever run is given, it is `A` that may carry the cancelling pairs —
    so the two clauses are not each other's mirror image the way `AbstractEquiv`'s are. -/
def AbstractEquivUpTo (bs : BusSemantics p) (A B : Circuit p) : Prop :=
  (∀ a, A.satisfies bs a → ∃ b, B.satisfies bs b ∧ InterfaceMatchUpTo bs A B a b) ∧
  (∀ b, B.satisfies bs b → ∃ a, A.satisfies bs a ∧ InterfaceMatchUpTo bs A B a b)

/-- `AbstractEquivUpTo` with the ∀-side restricted by an invariant `I`, as
    `AbstractEquivUnder` restricts `AbstractEquiv`. -/
def AbstractEquivUnderUpTo (bs : BusSemantics p) (I : BusInteraction (ZMod p) → Prop)
    (A B : Circuit p) : Prop :=
  (∀ a, A.satisfies bs a → (∀ m ∈ activeStateful A bs a, I m) →
    ∃ b, B.satisfies bs b ∧ InterfaceMatchUpTo bs A B a b) ∧
  (∀ b, B.satisfies bs b → (∀ m ∈ activeStateful B bs b, I m) →
    ∃ a, A.satisfies bs a ∧ InterfaceMatchUpTo bs A B a b)

/-- One direction of concrete replacement, with an existential witness: every satisfying run
    of `X` is reproduced by a satisfying run of `Y` with equal side effects, and the two runs
    are admissible together or not at all.

    Only `X.admissible → Y.admissible` is consumed downstream — the Spec bridge
    `isSoundReplacementOf_of_concreteEquiv` drops the clause outright, and
    `Circuit.isCompleteReplacementOf` asks for no more than that direction. The converse is
    kept because it is free (an `InterfaceMatch` is a permutation and the rely is order-free,
    `AdmissiblePermInvariant`) and it is not implied by the rest of the clause:
    `Circuit.sideEffects` is a *net* multiplicity per tuple, so it cannot see a canceling
    send/receive pair that changes admissibility. It makes the witness a simulation of the
    source run rather than merely a more-admissible one. -/
def ReplacesWith (bs : BusSemantics p) (X Y : Circuit p) : Prop :=
  ∀ x, X.satisfies bs x → ∃ y, Y.satisfies bs y ∧
    X.sideEffects bs x = Y.sideEffects bs y ∧
    (X.admissible bs x ↔ Y.admissible bs y)

/-- Equivalence in the concrete semantics: mutual replacement. -/
def ConcreteEquiv (bs : BusSemantics p) (A B : Circuit p) : Prop :=
  ReplacesWith bs A B ∧ ReplacesWith bs B A

/-- What a removal-tolerant match says about a pair of runs: equal side effects, and the
    rely transported from the traffic-richer circuit to the optimized one.

    The admissibility clause of `ReplacesWith` degrades to this. It cannot be an `↔`, and it
    cannot be turned around: reinstating a dropped message would need the rely conjuncts it
    carried (a timestamp bound, `x0ReturnsZero`), which `B`'s traffic no longer has. The
    direction is fixed by which circuit is traffic-richer, not by which run was given — so
    `MonoPair bs A B` takes `A`'s run first in *both* clauses of `ConcreteEquivUpTo`. -/
def MonoPair (bs : BusSemantics p) (A B : Circuit p) (a b : Variable → ZMod p) : Prop :=
  A.sideEffects bs a = B.sideEffects bs b ∧ (A.admissible bs a → B.admissible bs b)

/-- `ReplacesWith` with its side-effect and admissibility clauses weakened to `MonoPair`.
    This is what the Spec's *completeness* bridge consumes, which uses only `.mp` of the
    admissibility `↔` (`isCompleteReplacementOf_of_replacesWithViaMono`). -/
def ReplacesWithMono (bs : BusSemantics p) (X Y : Circuit p) : Prop :=
  ∀ x, X.satisfies bs x → ∃ y, Y.satisfies bs y ∧ MonoPair bs X Y x y

/-- The reverse direction: every run of `Y` is witnessed by a run of `X` with the same side
    effects. The pair statement is unchanged — the rely still travels `X → Y` — so this is
    *not* `ReplacesWithMono bs Y X`.

    It is exactly what the Spec's *soundness* clause asks for, which never mentions
    admissibility at all (`isSoundReplacementOf_of_witnessedBy`). -/
def WitnessedBy (bs : BusSemantics p) (X Y : Circuit p) : Prop :=
  ∀ y, Y.satisfies bs y → ∃ x, X.satisfies bs x ∧ MonoPair bs X Y x y

/-- Concrete equivalence as a removal-tolerant match delivers it: mutual coverage of runs,
    with the rely travelling `A → B` throughout. `ConcreteEquiv` refines it
    (`concreteEquivUpTo_of_concreteEquiv`), and it still lands the Spec's soundness notion
    (`isSoundReplacementOf_of_concreteEquivUpTo`). -/
def ConcreteEquivUpTo (bs : BusSemantics p) (A B : Circuit p) : Prop :=
  ReplacesWithMono bs A B ∧ WitnessedBy bs A B

/-- `ReplacesWith` with the existential witness replaced by a *given* witness map `w`:
    the run reproducing `x` is `w x`, named rather than merely known to exist. Forgetting
    `w` gives `ReplacesWith` (`replacesWith_of_via`), so `ConcreteEquiv` is the forgetful
    image of this notion.

    This is what the Spec's completeness needs and no equivalence can supply: its witness
    is pinned to `Derivations.witgen ds`, which keeps every powdr-ID variable at the input
    value and computes the rest from recorded methods, whereas `ReplacesWith` is invariant
    under swapping in any other witness (`isCompleteReplacementOf_of_replacesWithVia`). -/
def ReplacesWithVia (bs : BusSemantics p) (X Y : Circuit p)
    (w : (Variable → ZMod p) → (Variable → ZMod p)) : Prop :=
  ∀ x, X.satisfies bs x → Y.satisfies bs (w x) ∧
    X.sideEffects bs x = Y.sideEffects bs (w x) ∧
    (X.admissible bs x ↔ Y.admissible bs (w x))

/-- `ReplacesWithVia` over `MonoPair` — the witnessed notion a removal-tolerant match can
    supply, and still enough for the Spec's completeness clause
    (`isCompleteReplacementOf_of_replacesWithViaMono`). -/
def ReplacesWithViaMono (bs : BusSemantics p) (X Y : Circuit p)
    (w : (Variable → ZMod p) → (Variable → ZMod p)) : Prop :=
  ∀ x, X.satisfies bs x → Y.satisfies bs (w x) ∧ MonoPair bs X Y x (w x)

/-- The bus rely is order-free. `BusSemantics.admissible` is an opaque field, so this is a
    hypothesis of the transfer theorems; both VM semantics discharge it
    (`openVmAdmissible_perm`, `sp1Admissible_perm`). -/
def AdmissiblePermInvariant (bs : BusSemantics p) : Prop :=
  ∀ ⦃L L' : List (BusInteraction (ZMod p))⦄, L.Perm L' →
    (bs.admissible L ↔ bs.admissible L')

/-- The bus rely survives *removing* internally-balanced traffic. Like
    `AdmissiblePermInvariant` a hypothesis of the transfer theorems, since
    `BusSemantics.admissible` is an opaque field; both VM semantics discharge it
    (`openVm_admissibleDropInvariant`, `sp1_admissibleDropInvariant`).

    Only this direction is available, and the two halves of the rely fail differently. The
    memory discipline and `entryKeyed` are genuinely invariant — a cancelling pair adds the
    same payload to the receives and to the sends, leaving the per-address excess untouched,
    so they would support an `↔`. The ∀-over-messages conjuncts (the timestamp bound,
    `x0ReturnsZero`) hold of a sublist without holding of the whole, and it is they that
    make the removal one-way. -/
def AdmissibleDropInvariant (bs : BusSemantics p) : Prop :=
  ∀ ⦃L D : List (BusInteraction (ZMod p))⦄, InternallyBalanced D →
    bs.admissible (L ++ D) → bs.admissible L

/-- The stateful fragment of `Circuit.guaranteesInvariants`: every active *stateful* message
    of a satisfying run maintains the invariants. This is the fragment interface data can
    transport (see the module docstring for why the full notion cannot be). -/
def GuaranteesStatefulInvariants (circuit : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ a, circuit.satisfies bs a →
    ∀ m ∈ activeStateful circuit bs a, bs.maintainsInvariants m

/-- The stateless fragment of `Circuit.guaranteesInvariants`: every active message on a
    stateless bus maintains the invariants. Interface data cannot supply this fragment — the
    match carries no stateless messages — so it is a per-circuit obligation. The two
    fragments assemble the full clause with nothing in the gap
    (`guaranteesInvariants_of_fragments`); for OpenVM this fragment's whole content is the
    multiplicity value (`openVm_stateless_maintainsInvariants_iff`). -/
def GuaranteesStatelessInvariants (circuit : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ a, circuit.satisfies bs a →
    ∀ bi ∈ circuit.busInteractions,
      bs.isStateful (bi.eval a).busId = false →
      (bi.eval a).multiplicity ≠ 0 → bs.maintainsInvariants (bi.eval a)

/-- The multiplicity discipline: every active interaction is *sent once* (`1`) or — only on a
    stateful bus — *received once* (`-1`). A per-interaction check on the circuit alone,
    needing no reference circuit and no matching: multiplicities are flags or constants, so
    it is read off the syntax. It is what `ConcreteEquiv` cannot see, because
    `Circuit.sideEffects` records only the *net* multiplicity per tuple
    (`openVm_isSoundReplacementOf_of_concreteEquiv`). -/
def MultiplicityDiscipline (circuit : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ a, circuit.satisfies bs a →
    ∀ bi ∈ circuit.busInteractions,
      (bi.eval a).multiplicity ≠ 0 →
        (bi.eval a).multiplicity = 1 ∨
          (bs.isStateful (bi.eval a).busId = true ∧ (bi.eval a).multiplicity = -1)

/-! ## Closure semantics: memory environments

The observable above is justified semantically in `ApcOptimizer/InterfaceEncoding.lean`: the
audited window-atomicity rely says exactly "the traffic admits an environment"
(`admissibleMemoryBusM_of_closes` / `exists_closes_of_admissible`); under any closing
environment the nondeterministic receive payloads are a *function* of the environment and
the send history (`closes_recv_determined`); and interface-matched runs close with the same
environments (`interfaceMatch_closes_iff`). Together: no memory environment can observe a
difference between interface-matched runs, or supply data distinguishing them. -/

/-- A memory environment for one memory-shaped bus, as seen through a block's window: per
    evaluated address, the record entering the block from outside (consumed by the entry
    receive) and the record the block leaves behind (its exit send). `Option`-valued per
    address — window atomicity is structural in the type. The execution bridge is the
    single-cell case (`addressFields = []`). -/
structure MemEnv (p : ℕ) where
  /-- The record the environment supplies at an address, if any. -/
  entry : List (Option (ZMod p)) → Option (List (ZMod p))
  /-- The record the environment consumes at an address, if any. -/
  exit : List (Option (ZMod p)) → Option (List (ZMod p))

/-- The entry record at an address, as a multiset (`0` or a singleton). -/
def MemEnv.entryMS (E : MemEnv p) (addr : List (Option (ZMod p))) :
    Multiset (List (ZMod p)) :=
  (E.entry addr).elim 0 (fun P => {P})

/-- The exit record at an address, as a multiset (`0` or a singleton). -/
def MemEnv.exitMS (E : MemEnv p) (addr : List (Option (ZMod p))) :
    Multiset (List (ZMod p)) :=
  (E.exit addr).elim 0 (fun P => {P})

/-- Traffic `M` closes with environment `E`: per address, consumption balances production —
    every received record is a sent record or the environment's entry record, and every sent
    record is received or left to the environment. -/
def Closes (shape : MemoryBusShape) (E : MemEnv p)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)),
    (recvsAt shape addr M).map BusInteraction.payload + E.exitMS addr
      = (sendsAt shape addr M).map BusInteraction.payload + E.entryMS addr

/-- The traffic a run places on one bus — a projection of the interface data. -/
def busTraffic (circuit : Circuit p) (bs : BusSemantics p) (busId : Nat)
    (a : Variable → ZMod p) : Multiset (BusInteraction (ZMod p)) :=
  ↑((activeStateful circuit bs a).filter (fun m => m.busId = busId))

end ApcOptimizer.Interface
