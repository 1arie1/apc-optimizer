import ApcOptimizer.Spec

set_option autoImplicit false

/-! `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` (per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates). This file instead defines equivalence for a *list* of guest chips together,
    following the "VM equivalence" definition at the end of the `manuscript-powdr-ver` writeup:
    a VM is some guest-chip types (what the optimizer touches, each a full `Circuit`) plus some
    host-chip types (memory init/final, lookup tables, the input chip, the output chip —
    everything else), and two guest-chip lists are equivalent when they can each produce exactly
    the same externally observable effects.

    Every chip is a *type*: a real VM assignment realizes however many *instances* of each type
    it needs (a basic block's trip count, or how many times the input chip is invoked, are
    data-dependent and unknowable to the optimizer), so instance counts are part of the witness
    (`VmAssignment`), never fixed by `guestChips`/`hostChips` themselves. A few chip types (per
    vm.tex: memory init, memory final, output, each lookup table) can only ever have at most one
    instance; that's `HostChip.singleton`, opt-in and `False` by default.

    Host chips are represented directly by the interactions they may legally make (`HostChip`
    below), never by algebraic constraints of their own — mirroring how `BusSemantics` already
    stood in for "an opaque chip, specified only by what it accepts." Unlike `Spec.lean`, this
    file has no notion of *stateful* vs *stateless* buses, and no ordering discipline on bus
    interactions (contrast `MemoryBus.lean`'s `admissibleMemoryBus`, which reasons about
    consecutive-in-list-order pairs for one circuit). At VM level, every bus — lookup or memory
    alike — is subject to exactly one requirement: the net multiplicity of every message, summed
    over every realized instance's contribution, is zero. That single requirement is what
    `VmSat` checks.

    Effects are the VM's two externally observable interfaces: `Input`, the flat stream of
    values fed to the input chip across all of its realized instances, and `Output`, the flat
    array read back from the output chip's single realized instance. Both are plain arrays, not
    the raw per-message `BusState` — `BusState` is order-blind (it nets *by message*), which
    fits a final memory snapshot but not a stream, where position is the whole point. `VmSat`
    never constrains the order of a chip type's realized instances (its `legal` check is by
    membership, its balance check sums — both order-blind), so *that* order is already a free
    choice of the witness `a`, and `CanEffect` reads the input stream straight off
    `a.hostContribution vm.inputChipType` in list order: no separate notion of chip execution
    order is needed anywhere in the model. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip type, standing in for one of the VM's non-guest chips (memory init/final, a
    lookup table, the input chip, the output chip, ...). It has no algebraic constraints of its
    own — only the set of bus contributions each of its instances may legally make. -/
structure HostChip (p : ℕ) where
  /-- Whether a candidate contribution (a net multiplicity per bus message) is one an instance
      of this host-chip type may legally make. For a lookup table, e.g., this restricts
      contributions to nonpositive multiplicities whose payload is an actual table entry. -/
  legal : BusState p → Prop
  /-- Whether this type may only ever have at most one realized instance in a satisfying VM
      assignment (e.g. memory initialization/finalization, the output chip, each lookup table —
      per vm.tex's manuscript). Opt-in: defaults to `False`, i.e. unbounded instances — most
      chip types, the input chip included, may run any number of times. -/
  singleton : Prop := False

/-- The net multiplicity a circuit's bus interactions contribute to every message, under a
    given assignment. Unlike `Circuit.sideEffects`, this covers *every* bus interaction, not
    just stateful ones: at VM level, lookups balance the very same way memory does (see
    `VmSat`), so there is no separate stateless/`accepts` case to carve out. -/
def Circuit.allEffects (circuit : Circuit p) (assignment : Variable → ZMod p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- An assignment to a VM: for each guest-chip *type*, however many algebraic assignments the
    witness chooses to realize (the trip count is not fixed by `guestChips` itself — see the
    module docstring); likewise, for each host-chip type, however many bus contributions it
    realizes, one per instance (constrained to at most one wherever `HostChip.singleton`
    opts in — see `VmSat`). -/
structure VmAssignment (p : ℕ) (guestChips : List (Circuit p)) (hostChips : List (HostChip p)) where
  guestAssignment : (t : Fin guestChips.length) → List (Variable → ZMod p)
  hostContribution : (t : Fin hostChips.length) → List (BusState p)

/-- Every realized guest-chip instance's algebraic constraints hold under its own assignment. -/
def VmAssignment.guestSatisfies {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin guestChips.length, ∀ asg ∈ a.guestAssignment t,
    ∀ c ∈ (guestChips.get t).algebraicConstraints, c.eval asg = 0

/-- Every realized host-chip instance's contribution is one its type may legally make. -/
def VmAssignment.hostLegal {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin hostChips.length, ∀ contribution ∈ a.hostContribution t,
    (hostChips.get t).legal contribution

/-- Every host-chip type that opts into `HostChip.singleton` has at most one realized
    instance. -/
def VmAssignment.singletonsRespected {guestChips : List (Circuit p)}
    {hostChips : List (HostChip p)} (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ t : Fin hostChips.length, (hostChips.get t).singleton → (a.hostContribution t).length ≤ 1

/-- The net multiplicity contributed to every bus message, summed over every realized guest- and
    host-chip instance's contribution. -/
def VmAssignment.netContribution {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : BusState p :=
  fun message =>
    (∑ t : Fin guestChips.length,
      ((a.guestAssignment t).map (fun asg => (guestChips.get t).allEffects asg message)).sum) +
    (∑ t : Fin hostChips.length,
      ((a.hostContribution t).map (fun contribution => contribution message)).sum)

/-- Every bus balances: the net contribution to every message is zero. -/
def VmAssignment.balances {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    (a : VmAssignment p guestChips hostChips) : Prop :=
  ∀ message : BusMessage p, a.netContribution message = 0

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (its own algebraic
    constraints, or, for a host-chip instance, its type's legality), every host-chip type that
    opts into `singleton` stays a singleton, and every bus balances. -/
def VmSat (guestChips : List (Circuit p)) (hostChips : List (HostChip p))
    (a : VmAssignment p guestChips hostChips) : Prop :=
  a.guestSatisfies ∧ a.hostLegal ∧ a.singletonsRespected ∧ a.balances
-- ANCHOR_END: vmSat

omit [Fact p.Prime] in
theorem VmSat.of_perm {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    {a a' : VmAssignment p guestChips hostChips}
    (hguest : ∀ t, (a'.guestAssignment t).Perm (a.guestAssignment t))
    (hhost : ∀ t, (a'.hostContribution t).Perm (a.hostContribution t))
    (hsat : VmSat guestChips hostChips a) : VmSat guestChips hostChips a' := by
  obtain ⟨h1, h2, h3, h4⟩ := hsat
  have hnet : a'.netContribution = a.netContribution := by
    funext message
    show (∑ t : Fin guestChips.length,
        ((a'.guestAssignment t).map (fun asg => (guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin hostChips.length,
        ((a'.hostContribution t).map (fun contribution => contribution message)).sum) =
      (∑ t : Fin guestChips.length,
        ((a.guestAssignment t).map (fun asg => (guestChips.get t).allEffects asg message)).sum) +
      (∑ t : Fin hostChips.length,
        ((a.hostContribution t).map (fun contribution => contribution message)).sum)
    rw [Finset.sum_congr rfl (fun t _ => ((hguest t).map _).sum_eq),
      Finset.sum_congr rfl (fun t _ => ((hhost t).map _).sum_eq)]
  exact ⟨fun t asg hasg => h1 t asg ((hguest t).mem_iff.mp hasg),
    fun t contribution hcontrib => h2 t contribution ((hhost t).mem_iff.mp hcontrib),
    fun t hsingle => (hhost t).length_eq ▸ h3 t hsingle,
    fun message => (congrFun hnet message).trans (h4 message)⟩

omit [Fact p.Prime] in
/-- `VmSat` only depends on each chip type's realized instances as a *multiset*: permuting any
    type's instance list, guest or host, preserves satisfiability. This is why `CanEffect` can
    read the input stream straight off `a.hostContribution vm.inputChipType` in list order with
    no separate existential permutation — reordering that list (or any other type's) never
    changes whether an assignment is `VmSat`, so the freedom to choose an order was already
    available through the witness `a` itself. -/
theorem VmSat.perm_iff {guestChips : List (Circuit p)} {hostChips : List (HostChip p)}
    {a a' : VmAssignment p guestChips hostChips}
    (hguest : ∀ t, (a'.guestAssignment t).Perm (a.guestAssignment t))
    (hhost : ∀ t, (a'.hostContribution t).Perm (a.hostContribution t)) :
    VmSat guestChips hostChips a' ↔ VmSat guestChips hostChips a :=
  ⟨fun h => VmSat.of_perm (fun t => (hguest t).symm) (fun t => (hhost t).symm) h,
    fun h => VmSat.of_perm hguest hhost h⟩

/-- The VM's input interface: the flat stream of values fed, in order, to the input chip
    across all of its realized instances. Where one instance's chunk ends and the next begins is
    not part of the type — only the concatenation is externally observable (see `CanEffect`). -/
abbrev Input (p : ℕ) := List (ZMod p)

/-- The VM's output interface: the flat array read back from the output chip's single realized
    instance. -/
abbrev Output (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM run: what it consumed and what it produced. -/
structure Effect (p : ℕ) where
  input : Input p
  output : Output p

/-- A VM: its host-chip types, which one is the input chip's type (it may have any number of
    realized instances) and which is the output chip's type (expected — by convention, opt into
    `HostChip.singleton` on it — to have exactly one, so `e.output` is well-defined), and how to
    read one instance's own bus contribution as its stream chunk / output array. That extraction
    is left abstract here — it depends on the payload layout of whichever bus the input/output
    chips use, which is VM-specific in the same way `OpenVmSemantics.lean`'s payload decoding
    is. -/
structure Vm (p : ℕ) where
  hostChips : List (HostChip p)
  /-- The `hostChips` index that is the input chip's type. -/
  inputChipType : Fin hostChips.length
  /-- An input-chip instance's stream chunk, read off its own bus contribution. -/
  inputChunk : BusState p → Input p
  /-- The `hostChips` index that is the output chip's type. -/
  outputChipType : Fin hostChips.length
  /-- The output chip's output array, read off its (single realized) instance's contribution. -/
  outputArray : BusState p → Output p

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `vm`, can produce effect `e`: whether some satisfying VM
    assignment realizes exactly that input stream and output array. The input stream is the
    concatenation, in list order, of `a.hostContribution vm.inputChipType`'s chunks; since
    `VmSat` never constrains that order, this already ranges over every possible way the
    realized input-chip instances could line up (see the module docstring) — no separate
    permutation is needed on top of the witness `a`. The output is read off the single realized
    output-chip instance (there is none, or more than one, unless the `Vm`'s `outputChipType`
    opts into `HostChip.singleton`; see `VmSat`). -/
def CanEffect (vm : Vm p) (guestChips : List (Circuit p)) (e : Effect p) : Prop :=
  ∃ a : VmAssignment p guestChips vm.hostChips, VmSat guestChips vm.hostChips a ∧
    ((a.hostContribution vm.inputChipType).map vm.inputChunk).flatten = e.input ∧
    ∃ c, a.hostContribution vm.outputChipType = [c] ∧ vm.outputArray c = e.output
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed `vm`:
    every effect one can produce, the other can produce too, and vice versa. This is the
    multi-chip analogue of `Circuit.isSoundReplacementOf` / `Circuit.isCompleteReplacementOf`
    from `Spec.lean` — a future connecting theorem should show that per-chip `refines` (matched
    up between `guestChips` and `guestChips'`) implies this. -/
def vmEquivalent (vm : Vm p) (guestChips guestChips' : List (Circuit p)) : Prop :=
  ∀ e : Effect p, CanEffect vm guestChips e ↔ CanEffect vm guestChips' e
-- ANCHOR_END: vmEquivalent
