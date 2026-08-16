import ApcOptimizer.Spec
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-! VM-level correctness: what it means to correctly replace one list of guest
    chips with another, against a fixed host.

    `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of
    the VM" abstracted away as `BusSemantics` — per-message `accepts` /
    `admissible` / `maintainsInvariants` predicates — and conditioned on
    VM-level invariants it cannot itself justify. This file makes the VM
    explicit instead: host chips are named, buses balance globally, and the
    observable is the VM's input/output, so no per-message assumption is needed.

    The definition is equi-effectfulness: for every effect one chipset can produce
    (`CanProduce`), the other can produce it too. Soundness is one direction
    (`VmSoundReplacement`), completeness the other.

    This file must be audited, as must the host definition that it uses.

    Nothing in `Implementation/` need be checked.

    What is not yet here: a theorem wiring a real per-chip optimizer (`ApcOptimizer/Optimizer.lean`)
    into `VmSoundReplacement` for a whole VM. `vmSoundReplacement_of_forall₂`
    (`Implementation/Connection.lean`) already consumes exactly the per-chip
    `Circuit.isSoundReplacementOf` a chip-level optimizer proves; what blocks assembling the two is
    `PreservesLegality`, which soundness does not give for free — see the counterexample in
    `agent-docs/legality-preservation.md`. Closing that gap needs each optimizer pass to also prove
    it preserves `Circuit.legalGuest`/`Circuit.advancesClock`, which no pass does today. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip (memory init/final, a lookup table, the input chip, the output
    chip, ...). It is defined only by the effects it can have and by how many
    instances it can have. There is no explicit circuit. -/
structure HostChip (p : ℕ) where
  /-- Whether this `BusState` can be produced by this host-chip type. -/
  canProduce : BusState p → Prop
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

/-- **The VM the correctness statement is about.** Every field here is *spec*: it feeds `VmSat`
    or `VmAssignment.effects`, and so determines what `CanProduce` — and hence `VmEquivalent` —
    means. Get one wrong and the theorem is about the wrong machine.

    Deliberately absent is anything the *soundness argument* needs but the statement does not. The
    ordering on stateful state and its window live in `Implementation/Rank.lean`'s `RankModel`,
    which no statement in this file mentions; the backend's degree bound is a parameter of
    `PreservesDegree`. See this module's header for the audit tiers. -/
structure Host (p : ℕ) where
  chips : List (HostChip p)
  /-- The VM's trace budget: the most guest-chip instances a satisfying assignment may realize,
      in total across all types (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- Which guest circuits this host is prepared to run — the VM's well-formedness requirements
      on a guest chip (for OpenVM: binary multiplicities on lookup buses, `±1` on stateful ones,
      byte-valued memory sends).

      These live on the `Host` because they are the VM's requirements, not any chip's. They are
      *not* a conjunct of `VmSat`, and that placement matters: a real OpenVM AIR cannot check any
      of them — each quantifies over all assignments of the circuit, which no constraint system
      evaluates — so a run that breaks one still exists, and folding legality into satisfaction
      would quietly drop those runs from `CanProduce`. They are hypotheses of the equivalence
      theorems instead (`PreservesLegality`). -/
  legalGuest : Circuit p → Prop
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

/-- A list of guest chips. -/
abbrev Guest (p : ℕ) := List (Circuit p)

/-- A VM: a host and guest chips. -/
structure Vm (p : ℕ) where
  host : Host p
  guest : Guest p


/-- An assignment to one chip instance: for each variable, what value it takes. -/
abbrev ChipAssignment (p : ℕ) := Variable → ZMod p

/-- A circuit's effects: its net multiplicity contribution to each bus messsage.

    Unlike `Circuit.sideEffects`, this includes all buses, not just stateful
    ones. -/
def Circuit.allEffects (circuit : Circuit p) (assignment : ChipAssignment p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- The guest half of a VM assignment: for each chip *type*, however many algebraic
    assignments the witness chooses to realize. -/
abbrev GuestAssignment (p : ℕ) (guestChips : Guest p) :=
  Fin guestChips.length → List (ChipAssignment p)

/-- The host half of a VM assignment: for each chip type, however many effects
    it realizes, one per instance. -/
abbrev HostAssignment (p : ℕ) (host : Host p) := Fin host.chips.length → List (BusState p)

/-- An assignment to a VM. -/
structure VmAssignment (p : ℕ) (vm : Vm p) where
  guestAssignments : GuestAssignment p vm.guest
  hostAssignment : HostAssignment p vm.host

/-- The net effect of the guest instances. -/
def GuestAssignment.busEffect {G : Guest p} (gA : GuestAssignment p G) : BusState p :=
  fun message => ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg message)).sum

/-- The net effect of the host instances. -/
def HostAssignment.busEffect {host : Host p} (hA : HostAssignment p host) : BusState p :=
  fun message => ∑ t : Fin host.chips.length, ((hA t).map (fun effect => effect message)).sum

/-- How many guest instances the assignment realizes, across all types. -/
def GuestAssignment.instanceCount {G : Guest p} (gA : GuestAssignment p G) : ℕ :=
  ∑ t : Fin G.length, (gA t).length

/-- Every realized guest instance satisfies its own chip's algebraic constraints. -/
def GuestAssignment.satisfiesAlgebraic {G : Guest p} (gA : GuestAssignment p G) : Prop :=
  ∀ t : Fin G.length, ∀ asg ∈ gA t, (G.get t).satisfiesAlgebraic asg

/-- All host assignments are producible and (if applicable) respect singleton-ness. -/
def HostAssignment.satisfies {host : Host p} (hA : HostAssignment p host) : Prop :=
  (∀ t : Fin host.chips.length, ∀ effect ∈ hA t, (host.chips.get t).canProduce effect) ∧
  (∀ t : Fin host.chips.length, (host.chips.get t).singleton → (hA t).length = 1)

/-- The net multiplicity contributed to every bus message, summed over host and guest. -/
def VmAssignment.busEffect {vm : Vm p} (a : VmAssignment p vm) : BusState p :=
  fun message => a.guestAssignments.busEffect message + a.hostAssignment.busEffect message

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves
    (guests meet alebraic constraints and hosts can produce their effects),
    every bus balances, and the instance count is small enough.

    Every conjunct is and must be *directly* checked at runtime on a real OpenVM
    run. Thus, two other kinds of constraints are explicitly *excluded* here:

    * Requirements on a guest *circuit* — `Host.legalGuest`, the degree bound. These quantify
      over all assignments---not checkable or checked at runtime. These become
      assumptions/obligations on the optimizer instead (`PreservesLegality`,
      `PreservesDegree`).
    * Invariants that are *consequences* of several chips and/or the host. Such
      invariants are proved in `Implementation/` and are not part of this
      specification. For example, rank constraints and byte constraints on
      writes.
    -/
structure VmSat (vm : Vm p) (a : VmAssignment p vm) : Prop where
  /-- Every guest-chip instance's algebraic constraints hold under `a`. -/
  satisfiesGuest : a.guestAssignments.satisfiesAlgebraic
  /-- The host side of the assignment is producible and singleton-respecting
      (`HostAssignment.satisfies`). -/
  satisfiesHost : a.hostAssignment.satisfies
  /-- Every bus balances: the net multiplicity of every message is zero. -/
  balances : ∀ message : BusMessage p, a.busEffect message = 0
  /-- There are not too many guest-chip instances in total.

      This is enforced by OpenVM's proof system and is needed to prevent overflow, e.g., in
      multiplicities. -/
  withinBudget : a.guestAssignments.instanceCount ≤ vm.host.maxInstances
-- ANCHOR_END: vmSat

/-- The effects of a satisfying VM assignment: the input stream its input-chip instances pulled,
    concatenated in list order, and the array its output-chip instance left behind. -/
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) (h : VmSat vm a) : VmEffect p :=
  { input := (a.hostAssignment vm.host.inputChip).map vm.host.getInputChunk |>.flatten,
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).head (by
      -- proof: the output chip's assignment is nonempty, so `head` is safe to call
      have hlen := h.satisfiesHost.2 vm.host.outputChip vm.host.outputSingleton
      intro hnil
      simp [hnil] at hlen)) }

-- ANCHOR: canEffect
/-- Whether `vm` can produce effect `e`. -/
def CanProduce (vm : Vm p) (e : VmEffect p) : Prop :=
  ∃ (a : VmAssignment p vm) (h : VmSat vm a), a.effects h = e
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a *sound* VM-level replacement for `guestChips`: it can produce no effect
    the original could not. Nothing new becomes possible.

    The contextual, multi-chip analogue of `Circuit.isSoundReplacementOf`. -/
def VmSoundReplacement (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips'⟩ e → CanProduce ⟨host, guestChips⟩ e

/-- `guestChips'` is a *complete* VM-level replacement for `guestChips`: every effect the
    original could produce, it can produce too. Nothing is lost.

    The contextual, multi-chip analogue of `Circuit.isCompleteReplacementOf`. -/
def VmCompleteReplacement (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips⟩ e → CanProduce ⟨host, guestChips'⟩ e

/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed
    `host`: they are equi-effectful. -/
def VmEquivalent (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  VmSoundReplacement host guestChips guestChips' ∧
    VmCompleteReplacement host guestChips guestChips'
-- ANCHOR_END: vmEquivalent

/-- If `guestChips` are legal for `host`, then so are `guestChips'`.

    Not derivable from soundness — `agent-docs/legality-preservation.md` has a formal
    counterexample (`VmSpec/Audit/LegalityPreservation.lean`). Each optimizer pass will need
    its own argument for this. -/
def PreservesLegality (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  (∀ c ∈ guestChips, host.legalGuest c) → ∀ c ∈ guestChips', host.legalGuest c

/-- If `guestChips` fit the backend's degree bound, then so do `guestChips'`.

    Analog of `optimizerRespectsDegreeBound`.

    We'll have to prove that the optimizer meets this. -/
def PreservesDegree (b : DegreeBound) (guestChips guestChips' : Guest p) : Prop :=
  (∀ c ∈ guestChips, c.withinDegree b) → ∀ c ∈ guestChips', c.withinDegree b
