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
* `ConcreteEquiv` carries no `guaranteesInvariants` clause: interface data says nothing
  about *stateless* interactions, whose `maintainsInvariants` (multiplicity pinned to `1`)
  does not follow from `accepts` — an accepted lookup message sent with multiplicity `2`
  satisfies every `accepts` clause yet violates the invariant. The bridge
  `isSoundReplacementOf_of_concreteEquiv` takes that clause as a hypothesis, and
  `statefulInvariants_of_abstractEquiv` proves the derivable stateful fragment.
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
