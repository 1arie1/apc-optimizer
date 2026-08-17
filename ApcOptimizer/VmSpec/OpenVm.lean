import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Draft `HostChip`s for OpenVM, built against `ApcOptimizer.OpenVM`'s bus semantics
    (`OpenVmSemantics.lean`) — illustrating how `Basic.lean`'s host-chip abstraction covers
    OpenVM's actual host chips: its four stateless lookup tables, memory
    initialization/finalization, the output chip, an input chip modeled after `vm.tex`'s
    description (reads a pointer and a word count from two registers, then writes that many
    unconstrained words starting at the pointer), and the connector, which seeds and terminates the
    execution bridge. Assembled into a concrete `openVmHost : Host p` at the bottom.

    `Host.getInputChunk`/`Host.getOutput : BusState p → List (ZMod p)` need to read an *ordered
    array* off a bare `BusState p` function, which — unlike a `Circuit`'s own
    `busInteractions : List _` — carries no finite enumeration of what it touches. The fix used
    here: `inputHostChip`/`outputHostChip`'s `canProduce` predicates don't just restrict a
    contribution, they pin it *exactly* to the messages some witness (`InputRead`/`OutputRead`,
    bundling the count and the values) would produce. `inputChunkOf`/`outputArrayOf` then
    recover *a* witness with classical choice — it need not be the unique one (nothing here
    proves the witness is determined by the resulting `BusState p`), only *some* witness whose
    reconstructed messages match, which is all `inputHostChip.canProduce`/
    `outputHostChip.canProduce` promise; on a contribution with no witness at all (not
    `VmSat`-satisfying for this chip) they fall back to `[]`.

    Words: a memory word is four byte limbs (`MemoryPayload.data`). Registers are modelled as
    OpenVM stores them, a 32-bit value spread across all four (`wordValue`, `InputRead.ptrLimbs`).
    A *datum* pulled off the input stream or handed to the output is a single byte, carried in the
    low limb with the rest zeroed — one value per word rather than four packed together. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- Build a `BusState p` from a list of already-evaluated bus interactions: pointwise, the net
    multiplicity of a message is the sum of multiplicities of list entries carrying it exactly —
    the same rule `Circuit.allEffects`/`VmAssignment.busEffect` use. -/
def busStateOf (messages : List (BusInteraction (ZMod p))) : BusState p :=
  fun message =>
    ((messages.filter (fun m => decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity)).sum

/-- `defaultBusMap`'s execution-bridge bus id (its `0 ↦ some .executionBridge` arm) and memory bus
    id (its `1 ↦ some .memory` arm) — the one place this development picks them, so every other
    `0`/`1` below meaning "the exec bus"/"the mem bus" is one of these two. `abbrev`, not `def`, so
    they stay transparent to `simp`/`decide`/unification wherever a proof already expects the bare
    numeral. -/
abbrev openVmExecBusId : Nat := 0

abbrev openVmMemBusId : Nat := 1

/-- A stateless lookup-table host chip for bus `busId`: legal to touch a payload only if it is
    actually in the table, described by `accept`; illegal to touch any other bus. -/
def lookupTableHostChip (busId : Nat) (accept : List (ZMod p) → Prop) : HostChip p where
  canProduce contribution :=
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

/-- The memory-initialization host chip (default bus `1`): OpenVM's memory boundary chip on its
    send side. Whitepaper §4.6.2 — it "adds messages to the send multiset at timestamp `0`", and
    those messages "must correspond to the initial memory state".

    For persistent mode, the memory state is commited as a Merkle root. For volatile mode, it's all
    `0`.

    The AIR does not byte-constrain the data directly in the persistent mode, but in that mode the
    larger cross-segment structure inductively byte-constrains it. So, we choose to model the data
    as byte-constrained in either case.

    We do not model the Merkle-root itself, because it is a cross-segment fact (§5.2).
    -/
def memoryInitHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = 1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (∀ d ∈ f.data, isByte d) ∧ message.2[6]? = some 0
  singleton := True

/-- The memory-finalization host chip (default bus `1`): the last receive (multiplicity `-1`,
    OpenVM's `getPrevious` polarity) of each touched address in the register (`1`) and
    main-memory (`2`) address spaces.

    Address space `3` is deliberately excluded: see `outputHostChip`.

    Unlike memory initialization, no byte fact is asserted here: this chip only ever receives, so
    whatever it reads is bus-matched to some earlier send, and that send's own byte-ness already
    has to be established (either directly, for the other host chips, or by
    `maintains_of_stateful_active`'s induction, for a guest chip) — asserting it again here would
    be redundant, not merely conservative. `Host.exemptChip`/`openVmHost_finalize_exempt`
    (`Implementation/OpenVmConnection.lean`) fold this chip into that same induction instead of
    assuming its payload good outright — the manuscript's `eq:legal:recv_byte`, derived rather
    than assumed, for the one host chip whose own `canProduce` is simple enough (`singleton`,
    receive-only) to make that possible. -/
def memoryFinalizeHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
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
  /-- Memory holds bytes; see `memoryFinalizeHostChip`. -/
  wordsAreBytes : ∀ w ∈ words, isByte w

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
def outputHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution := ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)
  singleton := True

/-- The value a four-limb OpenVM word encodes: little-endian base-`256`. This is how a 32-bit
    register is spread across `MemoryPayload.data`, and it is why the registers an input read
    peeks are modelled as limb vectors rather than single field elements. -/
def wordValue (limbs : Vector (ZMod p) 4) : ZMod p :=
  limbs[0] + 256 * limbs[1] + 65536 * limbs[2] + 16777216 * limbs[3]

/-- A witness that an input-chip instance's contribution is a legal read: which pointer and
    count registers it peeked (`ptrLimbs`, `countLimbs`, each a 32-bit value spread over four
    byte limbs as OpenVM stores it), which new values it wrote (`bytes`), and which words those
    writes overwrote (`oldWords`, unconstrained — a write doesn't care what was there before,
    but the memory bus still needs a value for the receive half of the access). -/
structure InputRead (p : ℕ) where
  ptrLimbs : Vector (ZMod p) 4
  countLimbs : Vector (ZMod p) 4
  bytes : List (ZMod p)
  oldWords : List (Vector (ZMod p) 4)
  bytesLen : bytes.length = (wordValue countLimbs).val
  oldWordsLen : oldWords.length = (wordValue countLimbs).val
  /-- Memory holds bytes; see `memoryFinalizeHostChip`. Registers included — a peeked register is
      a memory access like any other, so its limbs carry the same discipline. -/
  bytesAreBytes : ∀ b ∈ bytes, isByte b
  oldWordsAreBytes : ∀ w ∈ oldWords, ∀ d ∈ w.toList, isByte d
  ptrLimbsAreBytes : ∀ d ∈ ptrLimbs.toList, isByte d
  countLimbsAreBytes : ∀ d ∈ countLimbs.toList, isByte d
  /-- When each peeked/overwritten word was last set — free rather than pinned to `0`: it was set
      by whatever earlier instruction touched it, at whatever time that was, which has nothing to
      do with *this* instance's own timing. -/
  ptrTime : ZMod p
  countTime : ZMod p
  wordTimes : List (ZMod p)
  wordTimesLen : wordTimes.length = (wordValue countLimbs).val
  /-- This instance's own start time — free rather than pinned to `0`, since the chip may run at
      any point in a segment (it is legal to invoke repeatedly, `singleton` stays `False`), not
      only at its very first instant, which timestamp `0` is reserved for anyway
      (`memoryInitHostChip`). Every write this instance makes lands at `base` plus a fixed
      per-access offset (`InputRead.interactions`) — one shared clock advancing once per access,
      matching `Rv32HintStoreAir`'s single `from_state.timestamp` and its `timestamp_pp` counter,
      not each write independently one tick after whatever it happened to overwrite. -/
  base : ZMod p

/-- The address the read starts writing at, decoded from the pointer register's limbs. -/
def InputRead.ptr (r : InputRead p) : ZMod p := wordValue r.ptrLimbs

/-- How many words the read pulls, decoded from the count register's limbs. -/
def InputRead.count (r : InputRead p) : ZMod p := wordValue r.countLimbs

/-- The bus interactions an `InputRead` describes: peek `ptrReg` and `countReg` (each a full
    four-limb register word, whatever was there at `ptrTime`/`countTime`), then write `r.bytes`
    (one value's low limb per word, the rest zeroed — see the module docstring) at consecutive
    addresses starting at `r.ptr` (each overwriting whatever was at `wordTimes[i]`).

    Every write — all `2 + r.count.val` accesses this instance makes — lands at `r.base` plus its
    own position in a single increasing sequence (`0` for the pointer peek, `1` for the count
    peek, `2 + i` for word `i`), not independently one tick after whatever value it happened to
    overwrite: an instance advances one shared clock once per access
    (`extensions/rv32im/circuit/src/hintstore/mod.rs`'s `Rv32HintStoreAir`, whose
    `timestamp_pp()` does exactly this off one `from_state.timestamp`), not `2 + r.count.val`
    independent per-access clocks. -/
-- TODO(AO): `ptrReg`/`countReg` are *not* actually VM-wide constants the way `openVmHost` treats
-- them (as fixed parameters shared by every `InputRead` in a run). Checked against real OpenVM
-- (`extensions/rv32im/circuit/src/hintstore/execution.rs`, `HintStorePreCompute`/
-- `execute_e12_impl`): the pointer register is instruction operand `b`, chosen per instruction by
-- the compiler, not fixed VM-wide. Worse, this repo's single `inputHostChip` actually conflates
-- two distinct real opcodes: `HINT_STOREW` writes exactly one word and has *no* count register at
-- all (`num_words` is hardcoded to `1`); only `HINT_BUFFER` reads a count, off operand `a`. So a
-- faithful model needs `InputRead`'s registers (and whether a count register exists at all) to be
-- part of the per-instance witness, not `openVmHost`'s fixed `ptrReg`/`countReg` parameters —
-- likely two host chip types, one per real opcode. Deliberately not done yet.
-- TODO(AO): meta-comment. It would be good to be able to abstract host chips without loosing
-- correctness of the theorem. Something like: if our host chip produces more things, and the
-- theorem is true, it's true with the real host chip too. We should investigate this.
def InputRead.interactions (r : InputRead p) (ptrReg countReg memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := memBusId, multiplicity := -1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base] },
    { busId := memBusId, multiplicity := -1,
      payload := [1, (countReg : ZMod p)] ++ r.countLimbs.toList ++ [r.countTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (countReg : ZMod p)] ++ r.countLimbs.toList ++ [r.base + 1] } ] ++
  ((List.range r.count.val).zip (r.bytes.zip (r.oldWords.zip r.wordTimes))).flatMap
    (fun (i, b, old, t) =>
      [ { busId := memBusId, multiplicity := -1,
          payload := [2, r.ptr + (i : ZMod p)] ++ old.toList ++ [t] },
        { busId := memBusId, multiplicity := 1,
          payload := [2, r.ptr + (i : ZMod p), b, 0, 0, 0, r.base + 2 + (i : ZMod p)] } ])

/-- The input host chip (default bus `1`): reads a pointer and a word count by peeking two
    fixed registers (address space `1`), then writes that many unconstrained words at
    consecutive addresses starting at the pointer (address space `2`) — pinned exactly to an
    `InputRead` witness, mirroring `outputHostChip`. Legal to run any number of times
    (`singleton` stays `False`), matching that the input chip may be invoked repeatedly to pull
    further chunks off the input stream. -/
def inputHostChip (ptrReg countReg : Nat) (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
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

/-- OpenVM's ordering on stateful state: a memory record's timestamp — payload field `6`, right
    after the four data limbs read by `memoryPayload?` — as an honest natural number, which is what
    makes `<` well-founded and `maintains_of_stateful_active`'s induction possible. Off the memory
    bus the rank is `0`; the execution bridge's `openVmPayloadOk` is vacuous, so it needs nothing
    from the induction.

    The index is positional rather than `getLast?` so that it agrees with `memoryPayload?` on every
    payload: a payload too short to be a memory record (`memoryPayload? = none`) gets rank `0`
    instead of a data limb misread as a timestamp, and a longer one still reads field `6`. -/
def openVmRank (memBusId : Nat := openVmMemBusId) : BusMessage p → ℕ :=
  fun m => if m.1 = memBusId then (m.2[6]?.getD 0).val else 0

/-- OpenVM's `MemoryConfig.timestamp_max_bits`: "all timestamps must be in the range
    `[0, 2 ^ timestamp_max_bits)`". Capped at `29` by OpenVM itself, and `29` is its default.

    The cap is exactly the anti-wraparound condition of `assertLtChip`: `AssertLtSubAir` decides
    `x < y` by range-checking `y - x - 1` to this many bits, which is the same question only while
    `2 ^ (bits + 1) < p`. For BabyBear `2 ^ 30 < 2013265921`, and `30` bits would not fit —
    hence `29`. -/
def openVmTimestampBits : ℕ := 29

/-- The `RankModel.bound` that goes with `openVmRank` (see `openVmRankModel`): OpenVM pins every
    timestamp below this, its connector chip range-checking the final timestamp of a segment. -/
def openVmRankBound : ℕ := 2 ^ openVmTimestampBits


/-- Which OpenVM buses carry VM state: the execution bridge and memory (`OpenVmBusType.isStateful`);
    the four lookup tables do not, and an unmapped id carries nothing. -/
def openVmIsStateful (busMap : BusMap) (busId : Nat) : Bool :=
  match busMap busId with
  | some t => t.isStateful
  | none => false

/-- OpenVM requires sends to memory to be byte-valued. This is that test. -/
def openVmPayloadOk (busMap : BusMap) (m : BusMessage p) : Prop :=
  match busMap m.1 with
  | some .memory =>
    match memoryPayload? m.2 with
    | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
    | none => True
  | some _ => True
  | none => False

/-- The timestamp an execution-bridge message carries (whitepaper §4.5). -/
def openVmBridgeTimestamp (m : BusMessage p) : ZMod p := m.2[1]?.getD 0

/-- The timestamp a memory message carries: payload index `6` of `(addr_space, ptr, data…, t)`,
    right after the four data limbs (whitepaper §4.6).

    Agrees with `openVmRank` on the memory bus. This is `Circuit.legalGuest`/`Circuit.advancesClock`
    (`Legal.lean`)'s `getTimestamp` for OpenVM. -/
def openVmMemTimestamp (m : BusMessage p) : ZMod p := m.2[6]?.getD 0

/-- This aggregates OpenVM's rules about how guests use buses.

    We deliberately copy the existing `accepts` function (which defines the tables) from
    `OpenVmSemantics.lean` rather than restate it here. So, we are trusting their table definitions.

    `execBusId` is fixed at `openVmExecBusId` because that is `defaultBusMap`'s own convention
    (see `Circuit.advancesClock`'s uses throughout this file); `getTimestamp` is
    `openVmMemTimestamp`. -/
def openVmGuestRules (busMap : BusMap) (memBusId : Nat) : GuestBusRules p where
  isStateful := openVmIsStateful busMap
  accepts := ApcOptimizer.OpenVM.accepts busMap
  payloadOk := openVmPayloadOk busMap
  execBusId := openVmExecBusId
  memBusId := memBusId
  getTimestamp := openVmMemTimestamp

/-- A witness that the connector chip's contribution closes a segment's execution bridge: the
    segment's initial and final `(pc, timestamp)` states.

    `VmConnectorAir` is a two-row trace whose rows are these two states. It constrains
    `begin.timestamp = 1` (hence no field for it here) and range-checks *each* row's `timestamp` to
    `timestamp_max_bits`, which is `finalTimestampBounded` — the one place in this development where
    the rank window is a checked constraint rather than an assumption. -/
structure ConnectorBoundary (p : ℕ) where
  initialPc : ZMod p
  finalPc : ZMod p
  finalTimestamp : ZMod p
  /-- `VmConnectorAir` range-checks every row's `timestamp` to `openVmTimestampBits` bits. -/
  finalTimestampBounded : finalTimestamp.val < openVmRankBound

/-- The bus interactions a `ConnectorBoundary` describes. `ExecutionBus::execute(_, _, prev, next)`
    receives `prev` and sends `next`, and `VmConnectorAir` calls it with `prev` the *final* state
    and `next` the *initial* one: the connector seeds the chain at `(initialPc, 1)` and consumes
    whatever the last instruction left. -/
def ConnectorBoundary.interactions (r : ConnectorBoundary p) (execBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := execBusId, multiplicity := 1, payload := [r.initialPc, 1] },
    { busId := execBusId, multiplicity := -1, payload := [r.finalPc, r.finalTimestamp] } ]

/-- The connector host chip (default bus `0`): OpenVM's `VmConnectorAir`, the execution bridge's
    seed and terminator. Without it the bridge would have to balance among the guest chips alone,
    which no real segment does — every run starts somewhere and ends somewhere.

    Pinned exactly to a `ConnectorBoundary` witness, like the input and output chips, because the
    range-checked final timestamp is what a `Host.pinsRanks` argument has to start from. -/
def connectorHostChip (execBusId : Nat := openVmExecBusId) : HostChip p where
  canProduce contribution :=
    ∃ r : ConnectorBoundary p, contribution = busStateOf (r.interactions execBusId)
  singleton := True

/-- A concrete OpenVM `Host`: `defaultBusMap`'s four stateless lookup tables (default bus ids),
    memory initialization (all-zero) and finalization, the output chip, an input chip that
    peeks registers `ptrReg`/`countReg` — all sharing `openVmMemBusId`, `defaultBusMap`'s memory
    bus — and the connector, which seeds and terminates the execution bridge.
    `maxInstances` is the VM's trace budget (see `VmAssignment.withinBudget`); it has to be small
    enough that a chip's lookups cannot wrap `ZMod p`, which is a hypothesis of the connecting
    theorem rather than something this definition can check on its own. `maxWindow` is the
    `Circuit.advancesClock` bound: the most one guest instance may advance the clock. It has no
    default because it is a property of the chips being run — a fused APC advances by its whole
    basic block, not by one instruction's `timestamp_delta`. There is no degree bound here: it
    belongs to the proving backend rather than the VM, and is a parameter of `PreservesDegree`.

    No `memBusId`/`busMap` parameters: every chip below is already pinned to `defaultBusMap`'s own
    numbering (the same way `pcLookupHostChip`'s default `busId` is), so a free `memBusId` would
    only be able to disagree with it, not vary it — `openVmGuestRules defaultBusMap openVmMemBusId`
    already reads bus `openVmMemBusId` as `.memory` (`defaultBusMap`'s `1 ↦ some .memory` arm).

    Pair with a `Guest p` of guest chips to get a `Vm p`, or feed straight into
    `CanEffect`/`vmEquivalent`. -/
noncomputable def openVmHost (maxInstances : ℕ) (ptrReg countReg : Nat) (maxWindow : ℕ) :
    Host p where
  maxInstances := maxInstances
  legalGuest c :=
    c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId)
      openVmRankBound maxWindow
  chips :=
    [ pcLookupHostChip, bitwiseLookupHostChip, variableRangeCheckerHostChip,
      tupleRangeCheckerHostChip, memoryInitHostChip,
      memoryFinalizeHostChip, outputHostChip,
      inputHostChip ptrReg countReg, connectorHostChip ]
  inputChip := ⟨7, by simp⟩
  getInputChunk := inputChunkOf ptrReg countReg openVmMemBusId
  outputChip := ⟨6, by simp⟩
  getOutput := outputArrayOf openVmMemBusId
  outputSingleton := trivial

end ApcOptimizer.OpenVM
