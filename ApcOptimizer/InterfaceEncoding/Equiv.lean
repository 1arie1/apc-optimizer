import ApcOptimizer.Spec

set_option autoImplicit false

/-! # Interface-encoding equivalence: the abstract and concrete notions

A standalone metatheory justifying the *interface encoding* of the memory bus used by an
external SMT equivalence verifier. The encoding replaces all memory semantics by a
rely/guarantee contract over a 1:1 matching of the two circuits' bus traffic: per matched
pair, receive-tuple equalities are assumed and send-tuple equalities are proof obligations.
Semantically, a memory receive is a *nondeterministic input* — nothing in a single circuit
constrains its data beyond the invariants `BusSemantics.accepts` grants (e.g. byte-ness) —
and the matching says the two circuits exchange identical traffic with that environment.

The main theorem (`Transfer.lean`, `concreteEquiv_of_abstractEquiv`): equivalence in this
abstract semantics (`AbstractEquiv`) implies equivalence in the concrete semantics
(`ConcreteEquiv` — `Circuit.satisfies` plus equal `Circuit.sideEffects`, with admissibility
transported). `Closure.lean` then justifies the observable itself: identical traffic means
identical closed compositions with every memory environment.

Two deliberate divergences from `ApcOptimizer/Spec.lean`:
* `ConcreteEquiv` is symmetric with an *existential* witness in both directions, unlike
  `Circuit.isCompleteReplacementOf`, whose witness is pinned to `Derivations.witgen` — this
  theory serves an external equivalence verifier, not the optimizer's witness generator.
* `ConcreteEquiv` carries no `guaranteesInvariants` clause: interface data says nothing
  about *stateless* interactions, whose `maintainsInvariants` (multiplicity pinned to `1`)
  does not follow from `accepts` — an accepted lookup message sent with multiplicity `2`
  satisfies every `accepts` clause yet violates the invariant. The bridge
  `isSoundReplacementOf_of_concreteEquiv` takes that clause as a hypothesis, and
  `statefulInvariants_of_abstractEquiv` proves the derivable stateful fragment.
-/

namespace ApcOptimizer.Interface

variable {p : ℕ}

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

/-- One direction of concrete replacement, with an existential witness: every satisfying run
    of `X` is reproduced by a satisfying run of `Y` with equal side effects, and the two runs
    are admissible together or not at all. -/
def ReplacesWith (bs : BusSemantics p) (X Y : Circuit p) : Prop :=
  ∀ x, X.satisfies bs x → ∃ y, Y.satisfies bs y ∧
    X.sideEffects bs x = Y.sideEffects bs y ∧
    (X.admissible bs x ↔ Y.admissible bs y)

/-- Equivalence in the concrete semantics: mutual replacement. -/
def ConcreteEquiv (bs : BusSemantics p) (A B : Circuit p) : Prop :=
  ReplacesWith bs A B ∧ ReplacesWith bs B A

/-- The bus rely is order-free. `BusSemantics.admissible` is an opaque field, so this is a
    hypothesis of the transfer theorems; both VM semantics discharge it
    (`openVmAdmissible_perm`, `sp1Admissible_perm`). -/
def AdmissiblePermInvariant (bs : BusSemantics p) : Prop :=
  ∀ ⦃L L' : List (BusInteraction (ZMod p))⦄, L.Perm L' →
    (bs.admissible L ↔ bs.admissible L')

/-- The stateful fragment of `Circuit.guaranteesInvariants`: every active *stateful* message
    of a satisfying run maintains the invariants. This is the fragment interface data can
    transport (see the module docstring for why the full notion cannot be). -/
def GuaranteesStatefulInvariants (circuit : Circuit p) (bs : BusSemantics p) : Prop :=
  ∀ a, circuit.satisfies bs a →
    ∀ m ∈ activeStateful circuit bs a, bs.maintainsInvariants m

end ApcOptimizer.Interface
