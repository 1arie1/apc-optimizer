import VersoManual

import ApcOptimizer.Spec
import ApcOptimizer.MemoryBus
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics
import ApcOptimizer.Optimizer

import Docs.Bibliography
import Docs.Cite

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Docs

set_option pp.rawOnError true

-- Render signatures even where a field/theorem carries no docstring: for the audited theorems the
-- signature *is* the statement we want to show, and we do not add prose to the audited source.
set_option verso.docstring.allowMissing true

#doc (Manual) "`apc-optimizer`: A Verified Constraint-System Optimizer" =>
%%%
shortTitle := "apc-optimizer"
%%%

This document describes `apc-optimizer`{citeNum powdr_apc_compiler}[], a formally verified zkVM circuit optimizer. `apc-optimizer` is a core component in the powdr autoprecompiles{citeNum powdr_autoprecompiles}[] pipeline.

# Background: zkVMs and autoprecompiles

zkVMs such as OpenVM{citeNum openVM}[], SP1{citeNum sp1}[], or powdr WASM{citeNum powdr_wasm}[] are virtual machines that output a cryptographic proof that a program executed correctly. They differ in which instruction set they emulate, but use the same underlying primitives: They are a collection of _circuits_ communicating via shared _buses_.

Each circuit is responsible for one or more instructions in the instruction set. They are defined by a set of _constraints_ over a _prime field_. Buses serve two purposes:
- They implement _lookups_ into precomputed tables. For example, a byte range check might me implemented by proving that a circuit variable is in a size-256 table of all bytes.
- They implement _stateful communication_ between circuits. For example, a _memory_ is implemented via bus interactions.

_Autoprecompiles_ prove correct execution of an entire _basic block_, which is a sequence of assembly instructions that can only be entered at the first instruction and exited at the last. The initial circuit is compiled from the instruction circuits of the zkVM and the concrete assembly program by instantiating whatever circuits would have been used by the vanilla zkVM within one monolithic circuit:

![Autoprecompiles](autoprecompiles.svg)

Having all instructions within the same circuits enables various optimizations, typically shrinking the circuit size by a factor of 3-4. Examples of these optimizations include:
- *Inlining of constants*. For example, immediate values can be inlined directly, as they are known at compile time. In combination with constant propagation, this specialized the circuit to the concrete basic block being proven.
- *Memory optimizations*. When proving instruction-by-instruction, even temporary values are written to memory and read back. Within a monolithic circuit, these values can be accessed directly, avoiding the overhead of the memory argument. One consequence of this is that each register is only accessed once, independent of how many instructions read or write it.
- *Gadget optimizations*. Circuits often contain repeated sub-circuits, that can be optimized for how exactly they are used. An example is RISC-V's `SEQZ` pseudo-instruction, which sets the output register to 1 if the input is zero, and 0 otherwise. It expands to the `SLTIU` instruction (a less-than comparison) with immediate value 1. But there exists a more efficient circuit for this specific comparison than the general-purpose `SLTIU` circuit.

# Circuits

A circuit is the constraint system of a single {deftech}_chip_: one component of a zkVM, such as an
instruction executor, a memory argument, or a range-check table. It is a list of algebraic
constraints together with a list of bus interactions, both over arithmetic expressions in a finite
field. The algebraic constraints are the AIR-style identities of STARK arithmetization; the bus interactions are the multiplicity-weighted messages of a
logarithmic-derivative lookup argument, the mechanism modern zkVMs use for range
checks, table lookups, memory, and communication between chips.

An {deftech}_expression_ is a constant, a variable, or a sum or product of expressions:

{docstring Expression}

Expressions are evaluated under an {deftech}_environment_ assigning a field element to every
variable, and carry a multiplicative {deftech}_degree_, on which the proving backend imposes an
upper bound (see [The degree bound](#the-degree-bound)).

{docstring Expression.eval}

{docstring Expression.degree}

A {deftech}_bus interaction_ sends a payload tuple to a global bus with a multiplicity. Buses are
how a chip communicates with the rest of the system. A *stateless* bus is a lookup: a chip looks a
tuple up in a table, such as a range check or an XOR table, and globally every lookup must be
matched by a table entry. A *stateful* bus (memory, the execution bridge) instead carries state
such as a timestamp or program counter.

{docstring BusInteraction}

Putting the two together, a {deftech}_constraint system_ is one chip: its algebraic constraints
together with its bus interactions:

{docstring ConstraintSystem}

The {deftech}_side effects_ of a constraint system are the messages it places on the *stateful*
buses. This is the externally observable behavior an optimization must preserve.

{docstring ConstraintSystem.sideEffects}

# Bus semantics

The meaning of a bus is not baked into the circuit; it is supplied separately by the zkVM's
{deftech}_bus semantics_. This is the interface an auditor reviews once per VM. It is deliberately
abstract: the optimizer is proven correct against *any* semantics of this shape, and a particular
VM is one instance.

{docstring BusSemantics}

Two fields deserve emphasis. `violatesConstraint` is the opaque handle on the lookup tables of
*other* chips; sending a message that a table would reject is forbidden. `admissible` is where the
"this is a real trace" assumption lives: it is a predicate on the active stateful messages, and it
is the hinge of the asymmetry described next. For memory buses it encodes the memory discipline of
{citeNum blum}[] (see [the memory discipline](#the-memory-discipline)).

# The correctness relation

The heart of the specification is what it means for an optimized circuit to be a faithful
replacement for its input. The relation is deliberately *asymmetric*, split into soundness and
completeness, because a prover and an honest trace place opposite demands on it.

## What a circuit does

A circuit is {deftech}_satisfied_ under an environment when every algebraic constraint vanishes and
no active bus interaction violates another chip's table:

{docstring ConstraintSystem.satisfies}

An assignment is {deftech}_admissible_ when its active stateful messages satisfy the VM's
`admissible` predicate. Completeness is required only for admissible assignments, so this is the
condition that picks out the real traces the optimizer must preserve:

{docstring ConstraintSystem.admissible}

Side effects are compared up to *net multiplicity* per message: an identical-payload send/receive
pair cancels, so two circuits are equivalent when they leave the same net effect on every stateful
bus.

## Soundness

Soundness protects against a cheating prover: *anything the optimized circuit accepts, the original
would have accepted too, with the same effect on the rest of the system.* It is required for
*every* assignment, because a malicious prover may choose any.

{docstring ConstraintSystem.isSoundReplacementOf}

## Completeness

Completeness protects against a uselessly strict optimizer that accepts nothing: *every real
(admissible) trace of the input is reproduced by the output.* It is required *only* for admissible
assignments, and it is *constructive*. The optimizer emits, alongside the circuit, a list of
{deftech}_derivations_: a computation method for each column it introduced.

{docstring ComputationMethod}

{docstring Derivations}

Witness generation runs these methods on the input trace to fill the optimized circuit's columns.
Completeness demands that the result is itself satisfying and admissible, with the same side
effects. That is exactly what lets an input trace be extended to an output trace.

{docstring Derivations.witgen}

{docstring ConstraintSystem.isCompleteReplacementOf}

## The degree bound

The proving backend caps the multiplicative degree of every expression. The optimizer must respect
that bound: a within-bound input yields a within-bound output.

{docstring ConstraintSystem.withinDegree}

{docstring optimizerRespectsDegreeBound}

## Correctness

An optimizer is {deftech}_correct_ for a given bus semantics and degree bound when, on every input,
its output is both a sound and a complete replacement, and it respects the bound:

{docstring Optimizer.isCorrect}

# The memory discipline

Memory and the execution bridge are stateful buses. Their `admissible` predicate is the offline
memory-checking discipline of {citeNum blum}[], reused in essentially every zkVM and, in its modern
multiplicity-based form, by arguments like Twist-and-Shout {citeNum twistShout}[]. `apc-optimizer`
does not prove this discipline; it takes it as an assumption about real (admissible) traces, and the
`busUnify` pass relies on it to cancel and chain memory accesses. The utility that states it is
small and shared across VMs.

A memory access is a `getPrevious`/`setNew` pair carrying opposite multiplicities. Which one is the
send depends on the VM's convention:

{docstring MemoryBusDirection}

{docstring MemoryBusShape}

The discipline itself: after a `setNew` to an address, the next same-address `getPrevious`, with no
active same-address message in between, observes the same payload. The crucial phrase is *in list
order*: the exporter must therefore list memory interactions in chronological order (see
[Assumptions](#assumptions)).

{docstring admissibleMemoryBus}

# VM instantiations

## OpenVM

{citeNum openVM}[] runs over the BabyBear field. Its bus map assigns each bus id a type. The stateful
ones are the execution bridge and memory; the stateless ones are the range-checker, bitwise/XOR,
and PC-lookup tables:

{docstring ApcOptimizer.OpenVM.OpenVmBusType}

The two opaque predicates of the semantics are given concretely. `violates` encodes each lookup
table (byte and XOR checks, range widths, lookup arities); `breaksInvariant` encodes the soundness
invariant that data written to the register / main-memory address spaces is byte-ranged.

{docstring ApcOptimizer.OpenVM.violates}

{docstring ApcOptimizer.OpenVM.breaksInvariant}

These assemble into the audited OpenVM semantics, with memory using OpenVM's send-the-new-record
convention:

{docstring ApcOptimizer.OpenVM.openVmBusSemantics}

## SP1

{citeNum sp1}[] (whose Hypercube proof system is described in {citeNum sp1Jagged}[]) runs over the
KoalaBear field. It uses a single byte-lookup bus multiplexing AND/OR/XOR/range/comparison
operations, 16-bit memory limbs, and, unlike OpenVM, sends the *previous* memory record and
receives the new one, so its memory shape carries the reversed direction.

{docstring ApcOptimizer.SP1.Sp1BusType}

{docstring ApcOptimizer.SP1.violates}

{docstring ApcOptimizer.SP1.sp1BusSemantics}

# The theorems

The master theorem states that the optimizer is correct for *every* bus semantics and *every* choice
of proven bus facts (the mechanism by which optimization passes learn sound properties of the
tables, itself carrying zero audit surface):

{docstring optimizerWithBusFacts_maintainsCorrectness}

The optimizers actually shipped are one-line instances. The fact-free optimizer, usable with any VM:

{docstring simpleOptimizer_maintainsCorrectness}

The OpenVM optimizer the CLI runs:

{docstring ApcOptimizer.OpenVM.openVmOptimizer_maintainsCorrectness}

And the SP1 optimizer:

{docstring ApcOptimizer.SP1.sp1Optimizer_maintainsCorrectness}

# Trust boundary

![Trust map: green nodes are machine-checked and discharged by the proofs; amber nodes are what the auditor must establish by hand: the VM semantics, the memory discipline, and the input-circuit assumptions.](trust.svg)

Everything reachable from the four theorems above is machine-checked and rests only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). What an auditor must still establish
by hand is therefore exactly the following, and nothing more:

1. *The audited definitions say what you think they say.* This document exists to make that check
   tractable. The relation is `Optimizer.isCorrect`; read it, and the soundness/completeness
   definitions it unfolds to.
2. *The VM semantics faithfully model the real VM.* `openVmBusSemantics` / `sp1BusSemantics` are
   claims about the deployed system's buses. They are audited files precisely because a wrong table
   entry here would silently license a wrong optimization.
3. *The input-circuit assumptions below hold.* The theorem is stated relative to them.

Everything else is discharged by the proofs and needs no audit: that each of the ~dozen passes
refines the circuit, that the fixpoint loop terminates, that degree guards fire.

## Assumptions

The guarantee is proven against the spec and semantics above. For it to carry over to a real
deployment, the auditor must confirm these properties of the *input* circuits (stated for OpenVM;
the SP1 analogues differ where noted):

> *Memory and execution-bridge interactions are listed in chronological order.* The `admissible`
> predicate pairs each `setNew` with the *next same-address* `getPrevious` in list order, so the
> exporter must emit these interactions in time order. Otherwise completeness may fail.

> *The input guarantees invariants and respects the degree bound.* The optimizer *preserves*
> `guaranteesInvariants` and `withinDegree`, but only assuming the input has them (e.g. that written
> memory limbs are byte-range-checked).

> *Lookup-table messages are pinned.* The semantics checks only the *arity* of the PC lookup, not
> the program table, so we assume constraints fixing the looked-up fields to constants have already
> been added to the input. The same applies to SP1's instruction-fetch and page-protection lookups,
> which `ApcOptimizer.SP1.violates` also accepts on arity alone.

> *Every memory writer is range-checked.* The semantics treats a memory *receive* from the register
> / main-memory address spaces with an out-of-range data limb as conflicting, so the optimizer may
> assume received memory words are in range. This holds only if every chip sending into those
> address spaces maintains the VM's memory-range discipline: byte range for OpenVM, 16-bit limbs for
> SP1.
