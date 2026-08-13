import ApcOptimizer.Spec

set_option autoImplicit false

/-! `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` (per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates).

    It's equivalence definition is conditioned on certain VM-level invariants
    and assumptions.  It is not clear whether those hold.

    This file defines equivalence for a *list* of guest chips together in the
    context of a host.  It's definition omits complex assumptions and
    invariants.

    Our next task is to ensure that if each chip (`Circuit`) in the list is
    replaced by an equivalent chip, according to the other definition, then this
    equivalence definition holds.

    The basic structure of the definition is equi-effectfulness: for every
    effect one chipset can produce, the other can produce it too, and vice
    versa.

    So, we need to define chips, effects, whether a chipset can produce an
    effect (i.e., whether some assignment to it has that effect).
    -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip (memory init/final, a lookup table, the input chip, the output
    chip, ...). It is defined only by the effects it can have and by how many
    instances it can have. There is no explicit circuit. -/
structure HostChip (p : ℕ) where
  /-- Whether this `BusState` is a valid effect for an instance of this host-chip type. -/
  canEffect : BusState p → Prop
  -- TODO: call this accepts A *semantic* representation of possible effects
  /-- Must a satisfying assignment instantiate this chip just once? E.g. mem-init. -/
  singleton : Prop := False

/-- A VM's input: a stream of values. -/
abbrev VmInput (p : ℕ) := List (ZMod p)

/-- A VM's output: an array of values. -/
abbrev VmOutput (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM: inputs and outputs. -/
structure VmEffect (p : ℕ) where
  input : VmInput p
  output : VmOutput p

/-- A Host, comprising its:
    * chips,
    * input chip,
    * input computation function,
    * output chip,
    * output computation function, and
    * a proof that the output is a singleton.

    This abstracts the Host's details from the correctness definition.
    -/
structure Host (p : ℕ) where
  chips : List (HostChip p)
  /-- The VM's trace budget: the most guest-chip instances a satisfying assignment may realize,
      in total across all types (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- The `chips` index that is the input chip type. -/
  inputChip : Fin chips.length
  /-- Map from an input chip instance's effects to its contribution to the input stream. -/
  getInputChunk : BusState p → VmInput p
  /-- The `chips` index that is the output chip type/instance (it's a singleton). -/
  outputChip : Fin chips.length
  /-- Map from an output chip instance's effects to the output array. -/
  getOutput : BusState p → VmOutput p
  /-- The output must be a singleton. -/
  outputSingleton : (chips.get outputChip).singleton

/-- A VM: a host and guest chips. -/
structure Vm (p : ℕ) where
  host : Host p
  guestChips : List (Circuit p)


/-- An assignment to a single chip instance: for each variable, what value it takes. -/
abbrev ChipAssignment (p : ℕ) := Variable → ZMod p

/-- The net multiplicity a circuit's bus interactions contribute to every message, under a
    given assignment. Unlike `Circuit.sideEffects`, this includes all buses, not
    just stateful ones. -/
def Circuit.allEffects (circuit : Circuit p) (assignment : ChipAssignment p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

abbrev HostAssignment (p : ℕ) (host : Host p) := (t : Fin host.chips.length) → List (BusState p)
-- TODO: getter for instantiation counts?

/-- An assignment to a VM: for each guest-chip *type*, however many algebraic assignments the
    witness chooses to realize (the trip count is not fixed by `guestChips` itself — see the
    module docstring); likewise, for each host-chip type, however many bus contributions it
    realizes, one per instance (constrained to at most one wherever `HostChip.singleton`
    opts in — see `VmSat`). -/
structure VmAssignment (p : ℕ) (vm : Vm p) where
  guestAssignments : Fin (vm.guestChips.length) → List (ChipAssignment p)
  hostAssignment : HostAssignment p vm.host

/-- The net multiplicity contributed to every bus message, summed over host and guest. -/
def VmAssignment.netBus {vm : Vm p} (a : VmAssignment p vm) : BusState p :=
  fun message =>
    (∑ t : Fin vm.guestChips.length,
      ((a.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
    (∑ t : Fin vm.host.chips.length,
      ((a.hostAssignment t).map (fun effect => effect message)).sum)

/-- Every realized guest-chip instance's algebraic constraints hold under its own assignment. -/
def VmAssignment.satisfiesGuest {vm : Vm p}
    (a : VmAssignment p vm) : Prop :=
  ∀ t : Fin vm.guestChips.length, ∀ asg ∈ a.guestAssignments t,
    ∀ c ∈ (vm.guestChips.get t).algebraicConstraints, c.eval asg = 0

/-- Every realized host-chip instance's contribution is one its type may legally make, and
    every host-chip type that opts into `HostChip.singleton` has at most one realized
    instance. -/
def VmAssignment.satisfiesHost {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  (∀ t : Fin vm.host.chips.length, ∀ effect ∈ a.hostAssignment t,
    (vm.host.chips.get t).canEffect effect) ∧
  (∀ t : Fin vm.host.chips.length,
    (vm.host.chips.get t).singleton → (a.hostAssignment t).length = 1)

/-- Every bus balances: the net contribution to every message is zero. -/
def VmAssignment.balances {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  ∀ message : BusMessage p, a.netBus message = 0

/-- The assignment fits the VM's trace budget.

    Balance alone is weaker than it looks, because multiplicities live in `ZMod p`: `p` instances
    that each send the *same* message net to zero, so no host chip has to receive it and a lookup
    table never gets to object. Bounding how many instances a witness may realize is what closes
    that off — see `Host.forcesAccepts` in `VmSpecConnection.lean`, which is unprovable without
    it. The bound is on instance counts alone, not on instances × bus interactions, so that it is
    fixed by the `Host` and therefore identical for the two guest-chip lists an equivalence
    compares; converting it into a bound on *messages* is the connecting theorem's job. -/
def VmAssignment.withinBudget {vm : Vm p} (a : VmAssignment p vm) : Prop :=
  (∑ t : Fin vm.guestChips.length, (a.guestAssignments t).length) ≤ vm.host.maxInstances

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (its own algebraic
    constraints, or, for a host-chip instance, its type's legality), every host-chip type that
    opts into `singleton` stays a singleton, every bus balances, and the whole thing fits the
    VM's trace budget. -/
def VmSat (vm: Vm p) (a : VmAssignment p vm) : Prop :=
  a.satisfiesGuest ∧ a.satisfiesHost ∧ a.balances ∧ a.withinBudget
-- ANCHOR_END: vmSat

/-- The effects of a satisfying VM assignment: the input stream its input-chip instances pulled,
    concatenated in list order, and the array its output-chip instance left behind. -/
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) (h : VmSat vm a) : VmEffect p :=
  { input := (a.hostAssignment vm.host.inputChip).map vm.host.getInputChunk |>.flatten,
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).head (by
      obtain ⟨-, ⟨-, hsingle⟩, -⟩ := h
      have hlen := hsingle vm.host.outputChip vm.host.outputSingleton
      intro hnil
      simp [hnil] at hlen)) }

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (unidirectional). -/
theorem VmSat.of_perm {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t))
    (hsat : VmSat vm a) : VmSat vm a' := by
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := hsat
  have hnet : a'.netBus = a.netBus := by
    funext message
    show (∑ t : Fin vm.guestChips.length,
        ((a'.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin vm.host.chips.length,
        ((a'.hostAssignment t).map (fun effect => effect message)).sum) =
      (∑ t : Fin vm.guestChips.length,
        ((a.guestAssignments t).map (fun asg => (vm.guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin vm.host.chips.length,
        ((a.hostAssignment t).map (fun effect => effect message)).sum)
    rw [Finset.sum_congr rfl (fun t _ => ((hguest t).map _).sum_eq),
      Finset.sum_congr rfl (fun t _ => ((hhost t).map _).sum_eq)]
  exact ⟨fun t asg hasg => h1 t asg ((hguest t).mem_iff.mp hasg),
    ⟨fun t effect hcontrib => h2 t effect ((hhost t).mem_iff.mp hcontrib),
      fun t hsingle => (hhost t).length_eq ▸ h3 t hsingle⟩,
    ⟨fun message => (congrFun hnet message).trans (h4 message),
      (Finset.sum_congr rfl (fun t _ => (hguest t).length_eq)).trans_le h5⟩⟩

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (bidirectional). -/
theorem VmSat.perm_iff {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t)) :
    VmSat vm a' ↔ VmSat vm a :=
  ⟨fun h => VmSat.of_perm (fun t => (hguest t).symm) (fun t => (hhost t).symm) h,
    fun h => VmSat.of_perm hguest hhost h⟩

-- TODO: more validation theorems?
-- TODO: prove that host chip list and guest chip lists are *sets*

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `host`, can produce effect `e`. -/
-- TODO: combine host and guest into vm
-- TODO: alternative name?
def CanEffect (host : Host p) (guestChips : List (Circuit p)) (e : VmEffect p) : Prop :=
  let vm : Vm p := { host := host, guestChips := guestChips }
  ∃ (a : VmAssignment p vm) (h : VmSat vm a), a.effects h = e
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed
    `host`: they are equi-effectful.

    This is the multi-chip analogue of `Circuit.isSoundReplacementOf` /
    `Circuit.isCompleteReplacementOf`. -/
def VmEquivalent (host : Host p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : VmEffect p, CanEffect host guestChips e ↔ CanEffect host guestChips' e
-- ANCHOR_END: vmEquivalent
-- TODO: degree at the chipset level?
