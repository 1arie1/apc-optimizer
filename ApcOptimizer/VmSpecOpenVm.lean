import ApcOptimizer.VmSpec
import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Draft `HostChip`s for OpenVM, built against `ApcOptimizer.OpenVM`'s bus semantics
    (`OpenVmSemantics.lean`) — illustrating how `VmSpec.lean`'s host-chip abstraction covers
    OpenVM's actual host chips: its four stateless lookup tables, memory
    initialization/finalization, the output chip, and an input chip modeled after `vm.tex`'s
    description (reads a pointer and a word count from two registers, then writes that many
    unconstrained words starting at the pointer). Assembled into a concrete `openVmHost : Host p`
    at the bottom.

    `Host.getInputChunk`/`Host.getOutput : BusState p → List (ZMod p)` need to read an *ordered
    array* off a bare `BusState p` function, which — unlike a `Circuit`'s own
    `busInteractions : List _` — carries no finite enumeration of what it touches. The fix used
    here: `inputHostChip`/`outputHostChip`'s `legal` predicates don't just restrict a
    contribution, they pin it *exactly* to the messages some witness (`InputRead`/`OutputRead`,
    bundling the count and the values) would produce. `inputChunkOf`/`outputArrayOf` then
    recover *a* witness with classical choice — it need not be the unique one (nothing here
    proves the witness is determined by the resulting `BusState p`), only *some* witness whose
    reconstructed messages match, which is all `inputHostChip.legal`/`outputHostChip.legal`
    promise; on a contribution with no witness at all (not `VmSat`-legal for this chip) they
    fall back to `[]`. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- Build a `BusState p` from a list of already-evaluated bus interactions: pointwise, the net
    multiplicity of a message is the sum of multiplicities of list entries carrying it exactly —
    the same rule `Circuit.allEffects`/`VmAssignment.netBus` use. -/
def busStateOf (messages : List (BusInteraction (ZMod p))) : BusState p :=
  fun message =>
    ((messages.filter (fun m => decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity)).sum

/-- A stateless lookup-table host chip for bus `busId`: legal to touch a payload only if it is
    actually in the table, described by `accept`; illegal to touch any other bus. -/
def lookupTableHostChip (busId : Nat) (accept : List (ZMod p) → Prop) : HostChip p where
  canEffect contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 → message.1 = busId ∧ accept message.2

/-- The PC-lookup host chip (OpenVM's instruction-fetch table, default bus `2`). As faithful as
    `OpenVM.accepts`'s own PC-lookup case, which only checks arity and leaves matching against
    the compiled program's actual instructions unmodeled — see that def's docstring for why. -/
def pcLookupHostChip (busId : Nat := 2) : HostChip p :=
  lookupTableHostChip busId (fun args => args.length = 9)

/-- The bitwise-lookup host chip (default bus `6`): `(x, y, z, op)`, mirroring
    `OpenVM.accepts`. -/
def bitwiseLookupHostChip (busId : Nat := 6) : HostChip p :=
  lookupTableHostChip busId fun
    | [x, y, z, op] =>
      match op.val with
      | 0 => isByte x ∧ isByte y ∧ z.val = 0
      | 1 => isByte x ∧ isByte y ∧ z.val = Nat.xor x.val y.val
      | _ => False
    | _ => False

/-- The variable-range-checker host chip (default bus `3`): `(x, bits)`, mirroring
    `OpenVM.accepts`. -/
def variableRangeCheckerHostChip (busId : Nat := 3) : HostChip p :=
  lookupTableHostChip busId fun
    | [x, bits] => bits.val ≤ 17 ∧ x.val < 2 ^ bits.val
    | _ => False

/-- The tuple-range-checker host chip (default bus `7`, default sizes matching
    `defaultBusMap`): `(x, y)` with `x < size1 ∧ y < size2`, mirroring `OpenVM.accepts`. -/
def tupleRangeCheckerHostChip (busId : Nat := 7) (size1 : Nat := 256) (size2 : Nat := 2048) :
    HostChip p :=
  lookupTableHostChip busId fun
    | [x, y] => x.val < size1 ∧ y.val < size2
    | _ => False

/-- The memory-initialization host chip (default bus `1`): sends (multiplicity `1`, OpenVM's
    `setNew` polarity) an all-zero word at timestamp `0` for each touched address, and nothing
    else. Memory starts zeroed everywhere; the program's actual inputs enter through
    `inputHostChip`, which overwrites those zeros, not through initialization. -/
def memoryInitHostChip (memBusId : Nat := 1) : HostChip p where
  canEffect contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = 1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        f.data = #v[0, 0, 0, 0] ∧ message.2.getLast? = some 0
  singleton := True

/-- The memory-finalization host chip (default bus `1`): the last receive (multiplicity `-1`,
    OpenVM's `getPrevious` polarity) of each touched address in the register (`1`) and
    main-memory (`2`) address spaces. Legal to receive any final word. Address
    space `3` is deliberately excluded: `outputHostChip` is what finalizes it,
    and that read *is* observable, so letting this chip absorb AS-3 too would
    let a VM discard its own output. -/
def memoryFinalizeHostChip (memBusId : Nat := 1) : HostChip p where
  canEffect contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = -1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (f.addressSpace.val = 1 ∨ f.addressSpace.val = 2)
  singleton := True

/-- A witness that the output chip's contribution is a legal final read of address space `3`:
    how many words it received (`count`) and which (`words`) — laid out contiguously from
    address `0`, since "receives all of AS-3" has nothing else to index by. -/
structure OutputRead (p : ℕ) where
  count : ZMod p
  words : List (ZMod p)
  wordsLen : words.length = count.val

/-- The bus interactions an `OutputRead` describes: receive each of `r.words`, in order, from
    consecutive address-space-`3` addresses starting at `0`. -/
def OutputRead.interactions (r : OutputRead p) (memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  ((List.range r.count.val).zip r.words).map (fun (i, w) =>
    { busId := memBusId, multiplicity := -1, payload := [3, (i : ZMod p), w, 0, 0, 0, 0] })

/-- The output host chip (default bus `1`): receives (at the very end, `-1`) all of address
    space `3`, contiguously from address `0`. Unlike memory finalization, this is pinned exactly
    to an `OutputRead` witness (not just "any final word") so `outputArrayOf` can recover the
    array. -/
def outputHostChip (memBusId : Nat := 1) : HostChip p where
  canEffect contribution := ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)
  singleton := True

/-- A witness that an input-chip instance's contribution is a legal read: which pointer and
    count it peeked (`ptr`, `count`), which new values it wrote (`bytes`), and which words those
    writes overwrote (`oldWords`, unconstrained — a write doesn't care what was there before,
    but the memory bus still needs a value for the receive half of the access). -/
structure InputRead (p : ℕ) where
  ptr : ZMod p
  count : ZMod p
  bytes : List (ZMod p)
  oldWords : List (Vector (ZMod p) 4)
  bytesLen : bytes.length = count.val
  oldWordsLen : oldWords.length = count.val

/-- The bus interactions an `InputRead` describes: peek `ptrReg` and `countReg`, then write
    `r.bytes` (one value's low limb per word, the rest zeroed — see the module docstring) at
    consecutive addresses starting at `r.ptr`. -/
def InputRead.interactions (r : InputRead p) (ptrReg countReg memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := memBusId, multiplicity := -1,
      payload := [1, (ptrReg : ZMod p), r.ptr, 0, 0, 0, 0] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (ptrReg : ZMod p), r.ptr, 0, 0, 0, 0] },
    { busId := memBusId, multiplicity := -1,
      payload := [1, (countReg : ZMod p), r.count, 0, 0, 0, 0] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (countReg : ZMod p), r.count, 0, 0, 0, 0] } ] ++
  ((List.range r.count.val).zip (r.bytes.zip r.oldWords)).flatMap (fun (i, b, old) =>
    [ { busId := memBusId, multiplicity := -1,
        payload := [2, r.ptr + (i : ZMod p)] ++ old.toList ++ [0] },
      { busId := memBusId, multiplicity := 1,
        payload := [2, r.ptr + (i : ZMod p), b, 0, 0, 0, 0] } ])

/-- The input host chip (default bus `1`): reads a pointer and a word count by peeking two
    fixed registers (address space `1`), then writes that many unconstrained words at
    consecutive addresses starting at the pointer (address space `2`) — pinned exactly to an
    `InputRead` witness, mirroring `outputHostChip`. Legal to run any number of times
    (`singleton` stays `False`), matching that the input chip may be invoked repeatedly to pull
    further chunks off the input stream. -/
def inputHostChip (ptrReg countReg : Nat) (memBusId : Nat := 1) : HostChip p where
  canEffect contribution :=
    ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg countReg memBusId)
  singleton := False

open Classical in
/-- Recover an input-chip instance's stream chunk from its contribution: the `bytes` of *some*
    witnessing `InputRead` (see the module docstring for why "some" is enough), or `[]` if the
    contribution isn't a legal read at all. This is what `Host.getInputChunk` should be, for an
    `openVmHost` built with the same `ptrReg`/`countReg`/`memBusId`. -/
noncomputable def inputChunkOf (ptrReg countReg memBusId : Nat) (contribution : BusState p) :
    VmInput p :=
  if h : ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg countReg memBusId)
  then h.choose.bytes else []

open Classical in
/-- Recover the output chip's array from its contribution: the `words` of *some* witnessing
    `OutputRead`, or `[]` if the contribution isn't a legal final read at all. This is what
    `Host.getOutput` should be, for an `openVmHost` built with the same `memBusId`. -/
noncomputable def outputArrayOf (memBusId : Nat) (contribution : BusState p) : VmOutput p :=
  if h : ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)
  then h.choose.words else []

/-- A concrete OpenVM `Host`: `defaultBusMap`'s four stateless lookup tables (default bus ids),
    memory initialization (all-zero) and finalization, the output chip, and an input chip that
    peeks registers `ptrReg`/`countReg` — all sharing `memBusId` for the (single) memory bus.
    Pair with a `List (Circuit p)` of guest chips to get a `Vm p`, or feed straight into
    `CanEffect`/`vmEquivalent`. -/
noncomputable def openVmHost (ptrReg countReg : Nat) (memBusId : Nat := 1) : Host p where
  chips :=
    [ pcLookupHostChip, bitwiseLookupHostChip, variableRangeCheckerHostChip,
      tupleRangeCheckerHostChip, memoryInitHostChip memBusId,
      memoryFinalizeHostChip memBusId, outputHostChip memBusId,
      inputHostChip ptrReg countReg memBusId ]
  inputChip := ⟨7, by simp⟩
  getInputChunk := inputChunkOf ptrReg countReg memBusId
  outputChip := ⟨6, by simp⟩
  getOutput := outputArrayOf memBusId
  outputSingleton := trivial

end ApcOptimizer.OpenVM
