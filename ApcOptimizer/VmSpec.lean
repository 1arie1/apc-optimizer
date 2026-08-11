import ApcOptimizer.Spec

set_option autoImplicit false

/-! `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    away as an opaque `BusSemantics` (per-message `accepts`/`admissible`/`maintainsInvariants`
    predicates). This file instead defines equivalence for a *list* of guest chips together,
    following the "VM equivalence" definition at the end of the `manuscript-powdr-ver` writeup:
    a VM is some guest chips (what the optimizer touches, each a full `Circuit`) plus some host
    chips (memory init/final, lookup tables, the input chip, the output chip — everything else),
    and two guest-chip lists are equivalent when they admit exactly the same externally
    observable effects.

    Host chips are represented directly by the interactions they may legally make (`HostChip`
    below), never by algebraic constraints of their own — mirroring how `BusSemantics` already
    stood in for "an opaque chip, specified only by what it accepts." Unlike `Spec.lean`, this
    file has no notion of *stateful* vs *stateless* buses, and no ordering discipline on bus
    interactions (contrast `MemoryBus.lean`'s `admissibleMemoryBus`, which reasons about
    consecutive-in-list-order pairs for one circuit). At VM level, every bus — lookup or memory
    alike — is subject to exactly one requirement: the net multiplicity of every message, summed
    over every chip's contribution, is zero. That single requirement is what `VmSat` checks.

    Effects are the VM's two externally observable interfaces: `Input`, the flat stream of
    values fed to the (possibly many times run) input chip, and `Output`, the flat array read
    back from the (run exactly once) output chip. Both are plain arrays, not the raw
    per-message `BusState` — `BusState` is order-blind (it nets *by message*), which fits a
    final memory snapshot but not a stream, where position is the whole point. Chunk boundaries
    between input-chip invocations, and *which* invocation produced which chunk, are not
    themselves observable — only the concatenated stream is — so `CanEffect` existentially
    quantifies over how a VM assignment's input-chip instances line up into that stream, rather
    than the model fixing (or reasoning about) any notion of chip execution order. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host chip, standing in for one of the VM's non-guest chips (memory init/final, a lookup
    table, the input chip, the output chip, ...). It has no algebraic constraints of its own —
    only the set of bus contributions it may legally make. -/
structure HostChip (p : ℕ) where
  /-- Whether a candidate contribution (a net multiplicity per bus message) is one this host
      chip may legally make. For a lookup table, e.g., this restricts contributions to
      nonpositive multiplicities whose payload is an actual table entry. -/
  legal : BusState p → Prop

/-- The net multiplicity a circuit's bus interactions contribute to every message, under a
    given assignment. Unlike `Circuit.sideEffects`, this covers *every* bus interaction, not
    just stateful ones: at VM level, lookups balance the very same way memory does (see
    `VmSat`), so there is no separate stateless/`accepts` case to carve out. -/
def Circuit.netContribution (circuit : Circuit p) (assignment : Variable → ZMod p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- An assignment to a VM: one algebraic assignment per guest-chip instance (`guestChips`'
    list order fixes the instances — e.g. two instances of "the same" chip are just two equal
    entries in the list), and one bus contribution per host-chip instance. -/
structure VmAssignment (p : ℕ) (guestChips : List (Circuit p)) (hostChips : List (HostChip p)) where
  guestAssignment : Fin guestChips.length → (Variable → ZMod p)
  hostContribution : Fin hostChips.length → BusState p

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying:
    - every guest chip's own algebraic constraints hold under its assignment;
    - every host chip's contribution is one it may legally make; and
    - every bus balances — the net multiplicity of every message, summed over every guest
      chip's evaluated bus interactions and every host chip's contribution, is zero. -/
def VmSat (guestChips : List (Circuit p)) (hostChips : List (HostChip p))
    (a : VmAssignment p guestChips hostChips) : Prop :=
  (∀ i : Fin guestChips.length,
    ∀ c ∈ (guestChips.get i).algebraicConstraints, c.eval (a.guestAssignment i) = 0) ∧
  (∀ j : Fin hostChips.length, (hostChips.get j).legal (a.hostContribution j)) ∧
  (∀ message : BusMessage p,
    (∑ i : Fin guestChips.length, (guestChips.get i).netContribution (a.guestAssignment i) message) +
      (∑ j : Fin hostChips.length, a.hostContribution j message) = 0)
-- ANCHOR_END: vmSat

/-- The VM's input interface: the flat stream of values fed, in order, to the input chip
    across all of its invocations. Where one invocation's chunk ends and the next begins is not
    part of the type — only the concatenation is externally observable (see `CanEffect`). -/
abbrev Input (p : ℕ) := List (ZMod p)

/-- The VM's output interface: the flat array read back from the (single) output chip. -/
abbrev Output (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM run: what it consumed and what it produced. -/
structure Effect (p : ℕ) where
  input : Input p
  output : Output p

/-- A VM: its host chips, which of them are input-chip instances (any number of them, since the
    input chip may run many times) and which is the (single) output chip, and how to read each
    one's own bus contribution as its stream chunk / output array. That extraction is left
    abstract here — it depends on the payload layout of whichever bus the input/output chips
    use, which is VM-specific in the same way `OpenVmSemantics.lean`'s payload decoding is. -/
structure Vm (p : ℕ) where
  hostChips : List (HostChip p)
  /-- The `hostChips` indices that are input-chip instances. -/
  inputChipIndices : List (Fin hostChips.length)
  /-- An input-chip instance's stream chunk, read off its own bus contribution. -/
  inputChunk : BusState p → Input p
  /-- The `hostChips` index of the (single) output chip. -/
  outputChipIndex : Fin hostChips.length
  /-- The output chip's output array, read off its own bus contribution. -/
  outputArray : BusState p → Output p

-- ANCHOR: canEffect
/-- Whether `guestChips`, run against `vm`, can produce effect `e`: whether some satisfying VM
    assignment realizes exactly that input stream and output array. The input stream is the
    concatenation of the input-chip instances' chunks in *some* order matching (as a
    permutation) `vm.inputChipIndices` — which instance produced which position in the stream
    is part of the witness, not fixed by the model. -/
def CanEffect (vm : Vm p) (guestChips : List (Circuit p)) (e : Effect p) : Prop :=
  ∃ a : VmAssignment p guestChips vm.hostChips, VmSat guestChips vm.hostChips a ∧
    (∃ order : List (Fin vm.hostChips.length), order.Perm vm.inputChipIndices ∧
      (order.map (fun j => vm.inputChunk (a.hostContribution j))).flatten = e.input) ∧
    vm.outputArray (a.hostContribution vm.outputChipIndex) = e.output
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
