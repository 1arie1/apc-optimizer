import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Draft `HostChip`s for OpenVM, built against `ApcOptimizer.OpenVM`'s bus semantics
    (`OpenVmSemantics.lean`) — illustrating how `Basic.lean`'s host-chip abstraction covers
    OpenVM's actual host chips: its four stateless lookup tables, memory
    initialization/finalization, the output chip, a `HINT_STOREW` input chip (peeks a pointer
    register, then writes one unconstrained word there), and the connector, which seeds and
    terminates the execution bridge. Assembled into a concrete `openVmHost : Host p` at the
    bottom.

    `Host.getInputChunk`/`Host.getOutput : BusState p → List (ZMod p)` need to read an *ordered
    array* off a bare `BusState p` function, which — unlike a `Circuit`'s own
    `busInteractions : List _` — carries no finite enumeration of what it touches. The fix used
    here: `inputHostChip`/`outputHostChip`'s `canProduce` predicates don't just restrict a
    contribution, they pin it *exactly* to the messages some witness (`InputRead`/`OutputRead`)
    would produce. `inputChunkOf`/`outputArrayOf` then
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
    actually in the table, described by `accept`; illegal to touch any other bus.

    A VM has one table chip per bus, so `instanceBound` is `1` — its rows are its table entries,
    and the one instance's `canProduce` already describes the whole table's net. Nothing is lost
    by pinning the count: the predicate is closed under sums and holds of `0`, so one instance
    reaches exactly the nets any number of them could. -/
def lookupTableHostChip (busId : Nat) (accept : List (ZMod p) → Prop) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 → message.1 = busId ∧ accept message.2
  instanceBound := 1

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

    Address space `3` — the one the output chip reads (`outputHostChip`) — is the exception: its
    words start at `0`. Leaving them free would mean the prover could choose the observed output
    outright, by initializing the cells the output chip goes on to receive and never running a
    guest at all. Zero rather than *absent* because a write is a receive of the cell's previous
    record followed by a send (`MemoryBus.lean`'s `receiveThenSend`), so a guest's first write to
    an address-space-`3` cell needs an initial record to receive. -/
def memoryInitHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = 1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (∀ d ∈ f.data, isByte d) ∧ message.2[6]? = some 0 ∧
        (f.addressSpace.val = 3 → ∀ d ∈ f.data, d = 0)
  instanceBound := 1

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
    than assumed, for the one host chip whose own `canProduce` is simple enough (one instance,
    receive-only) to make that possible. -/
def memoryFinalizeHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = -1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (f.addressSpace.val = 1 ∨ f.addressSpace.val = 2)
  instanceBound := 1

/-- A witness that the output chip's contribution is a legal final read of address space `3`:
    how many words it received (`count`), which (`words`) — laid out contiguously from address `0`,
    since "receives all of AS-3" has nothing else to index by — and when each was last written
    (`times`). -/
structure OutputRead (p : ℕ) where
  count : ZMod p
  words : List (ZMod p)
  wordsLen : words.length = count.val
  /-- Memory holds bytes; see `memoryFinalizeHostChip`. -/
  wordsAreBytes : ∀ w ∈ words, isByte w
  /-- When each word was last written: free, exactly as `memoryFinalizeHostChip` leaves the
      timestamps of the records it receives. A final read takes each cell as it stands, and what
      ordered the writes that got it there is the writers' business.

      Free is load-bearing, not laziness. Pinning these to `0` would mean only memory
      *initialization* could have sent the records the output chip receives — `Host.pinsRanks` puts
      every guest record at a positive timestamp — so no guest could write to address space `3` in
      a satisfying run, and the observed output would be a function of the initial memory alone,
      decoupled from the computation. -/
  times : List (ZMod p)
  timesLen : times.length = count.val

/-- The bus interactions an `OutputRead` describes: receive each of `r.words`, in order, from
    consecutive address-space-`3` addresses starting at `0`, each carrying the timestamp at which
    it was last written. -/
def OutputRead.interactions (r : OutputRead p) (memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  ((List.range r.count.val).zip (r.words.zip r.times)).map (fun (i, w, t) =>
    { busId := memBusId, multiplicity := -1, payload := [3, (i : ZMod p), w, 0, 0, 0, t] })

/-- The output host chip (default bus `1`): receives (at the very end, `-1`) all of address
    space `3`, contiguously from address `0`. Unlike memory finalization, this is pinned exactly
    to an `OutputRead` witness (not just "any final word") so `outputArrayOf` can recover the
    array. -/
def outputHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution := ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)
  instanceBound := 1

/-- The value a four-limb OpenVM word encodes: little-endian base-`256`. This is how a 32-bit
    register is spread across `MemoryPayload.data`, and it is why the registers an input read
    peeks are modelled as limb vectors rather than single field elements. -/
def wordValue (limbs : Vector (ZMod p) 4) : ZMod p :=
  limbs[0] + 256 * limbs[1] + 65536 * limbs[2] + 16777216 * limbs[3]

/-- How far a `HINT_STOREW` instance advances the execution-bridge clock: one tick per memory
    access — the pointer-register peek and the word write — plus one, so both sit *strictly*
    inside `(base, base + inputStepWindow)`, the window `StepLayout.placed` allows and
    `Audit/OpenVmLegalAudit.lean`'s `stepChip` exhibits. -/
def inputStepWindow : ℕ := 3

/-- A witness that an input-chip instance's contribution is a legal `HINT_STOREW`: which pointer
    register it peeked (`ptrLimbs`, a 32-bit value spread over four byte limbs as OpenVM stores
    it), which value it wrote (`byte`), and which word that write overwrote (`oldWord`,
    unconstrained — a write doesn't care what was there before, but the memory bus still needs a
    value for the receive half of the access).

    One word, not a run of them: `Rv32HintStoreAir` implements two opcodes, and `HINT_STOREW`
    hardcodes `num_words` to `1` and reads no count register at all
    (`extensions/rv32im/circuit/src/hintstore/mod.rs`). `HINT_BUFFER`, which does read a count off
    operand `a`, is a second chip type this host does not model yet — `Host.inputChips` is a list
    so that adding it is a new entry rather than a reshape. -/
structure InputRead (p : ℕ) where
  ptrLimbs : Vector (ZMod p) 4
  byte : ZMod p
  oldWord : Vector (ZMod p) 4
  /-- Memory holds bytes; see `memoryFinalizeHostChip`. Registers included — a peeked register is
      a memory access like any other, so its limbs carry the same discipline. -/
  byteIsByte : isByte byte
  oldWordIsBytes : ∀ d ∈ oldWord.toList, isByte d
  ptrLimbsAreBytes : ∀ d ∈ ptrLimbs.toList, isByte d
  /-- When the peeked register and the overwritten word were last set — free rather than pinned to
      `0`: they were set by whatever earlier instruction touched them, at whatever time that was,
      which has nothing to do with *this* instance's own timing. -/
  ptrTime : ZMod p
  wordTime : ZMod p
  /-- This instance's own start time — free rather than pinned to `0`, since the chip may run at
      any point in a segment (it is legal to invoke repeatedly — see `inputHostChip`'s
      `instanceBound`), not only at its very first instant, which timestamp `0` is reserved for
      (`memoryInitHostChip`). Both accesses land at `base` plus a fixed offset
      (`InputRead.interactions`) — one shared clock advancing once per access, matching
      `Rv32HintStoreAir`'s single `from_state.timestamp` and its `timestamp_pp` counter. -/
  base : ZMod p
  /-- The `pc` this instance starts at, on the execution bridge — an input-chip instance is an
      instruction executor like any other (whitepaper §4.5: "every instruction executor AIR must
      constrain that it adds a message `(pc_from, t_from)` to the receive set and `(pc_to, t_to)`
      to the send set"), not traffic outside the instruction stream. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p

/-- The address the write lands at, decoded from the pointer register's limbs. -/
def InputRead.ptr (r : InputRead p) : ZMod p := wordValue r.ptrLimbs

/-- The bus interactions an `InputRead` describes: one execution-bridge step
    (`StepLayout`'s `recv`/`send`/`other` shape, mirrored exactly), receiving `(pcFrom,
    base)` and sending `(pcTo, base + inputStepWindow)`; then peek `ptrReg` (a full four-limb
    register word, whatever was there at `ptrTime`) at `base + 1`, then write `r.byte` (in the low
    limb, the rest zeroed — see the module docstring) at `r.ptr` at `base + 2`, overwriting
    whatever was there at `wordTime`.

    Both accesses land at `r.base` plus their own position in a single increasing sequence, not
    independently one tick after whatever value they happened to overwrite: an instance advances
    one shared clock once per access (`extensions/rv32im/circuit/src/hintstore/mod.rs`'s
    `Rv32HintStoreAir`, whose `timestamp_pp()` does exactly this off one `from_state.timestamp`). -/

-- TODO(AO): `ptrReg` is *not* actually a VM-wide constant the way `openVmHost` treats it (as a
-- fixed parameter shared by every `InputRead` in a run). Checked against real OpenVM
-- (`extensions/rv32im/circuit/src/hintstore/execution.rs`, `HintStorePreCompute`/
-- `execute_e12_impl`): the pointer register is instruction operand `b`, chosen per instruction by
-- the compiler, not fixed VM-wide. A faithful model needs it in the per-instance witness rather
-- than in `openVmHost`'s parameters. Deliberately not done yet.
def InputRead.interactions (r : InputRead p) (ptrReg execBusId memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := execBusId, multiplicity := -1, payload := [r.pcFrom, r.base] },
    { busId := execBusId, multiplicity := 1,
      payload := [r.pcTo, r.base + (inputStepWindow : ZMod p)] },
    { busId := memBusId, multiplicity := -1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1] },
    { busId := memBusId, multiplicity := -1,
      payload := [2, r.ptr] ++ r.oldWord.toList ++ [r.wordTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [2, r.ptr, r.byte, 0, 0, 0, r.base + 2] } ]

/-- The `HINT_STOREW` input host chip (default bus `1` for memory, `0` for the execution bridge):
    peeks a pointer register (address space `1`), then writes one unconstrained word at that
    pointer (address space `2`) — pinned exactly to an `InputRead` witness, mirroring
    `outputHostChip`. The one host chip a segment may realize more than once, matching that the
    hint instruction is executed again for each further word pulled off the input stream — but at
    most `maxInstances` times, since it writes to memory and the trace budget caps it as it caps a
    guest chip (`HostChip.instanceBound`).

    Its clock advance is the constant `inputStepWindow`, not a witness field: a real `HINT_STOREW`
    makes a fixed number of accesses. `OpenVmParams.inputWindowOk` is where that constant meets
    `maxWindow`, the anti-wraparound budget an instance needs to sit alongside guest instances on
    the same execution bridge (`OpenVmParams.windowOk`). -/
def inputHostChip (ptrReg maxInstances : Nat)
    (execBusId : Nat := openVmExecBusId) (memBusId : Nat := openVmMemBusId) :
    HostChip p where
  canProduce contribution :=
    ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg execBusId memBusId)
  instanceBound := maxInstances

open Classical in
/-- Recover an input-chip instance's stream datum from its contribution: the `byte` of *some*
    witnessing `InputRead` (see the module docstring for why "some" is enough) as a one-element
    chunk, or `[]` if the contribution isn't a legal read at all. This is what
    `Host.getInputChunk` should be, for an `openVmHost` built with the same
    `ptrReg`/`execBusId`/`memBusId`. -/
noncomputable def inputChunkOf (ptrReg execBusId memBusId : Nat)
    (contribution : BusState p) : VmInput p :=
  if h : ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg execBusId memBusId)
  then [h.choose.byte] else []

open Classical in
/-- Recover an input-chip instance's start time from its contribution: the `base` of the *same*
    witnessing `InputRead` `inputChunkOf` recovers its `byte` from — `Classical.choose` depends
    only on the existential's proposition, not on which proof of it is in hand, so the two agree
    on one witness — or `0` if the contribution isn't a legal read at all (irrelevant: sorting
    puts such a chunk somewhere, but it contributes `[]` either way). This is what
    `Host.getInputTime` should be, for an `openVmHost` built with the same
    `ptrReg`/`execBusId`/`memBusId`. -/
noncomputable def inputTimeOf (ptrReg execBusId memBusId : Nat)
    (contribution : BusState p) : ZMod p :=
  if h : ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg execBusId memBusId)
  then h.choose.base else 0

open Classical in
/-- Recover the output chip's array from its contribution: the `words` of *some* witnessing
    `OutputRead`, or `[]` if the contribution isn't a legal final read at all. This is what
    `Host.getOutput` should be, for an `openVmHost` built with the same `memBusId`. -/
noncomputable def outputArrayOf (memBusId : Nat) (contribution : BusState p) : VmOutput p :=
  if h : ∃ r : OutputRead p, contribution = busStateOf (r.interactions memBusId)
  then h.choose.words else []

/-- The timestamp a stateful message carries: payload index `6` for a memory record
    `(addr_space, ptr, data…, t)`, right after the four data limbs (whitepaper §4.6), and index `1`
    for an execution-bridge state `(pc, t)` (§4.5). Off both, `0`.

    Reading the bridge too is what lets `StepLayout` place *every* stateful interaction in a step's
    window on one scale, so that `StepLayout.ordered` can be stated across buses: a step's bridge
    receive sits at offset `0`, its memory accesses in between, and its bridge send at offset `d`.

    The index is positional rather than `getLast?` so that it agrees with `memoryPayload?` on every
    payload: a payload too short to be a memory record (`memoryPayload? = none`) reads `0` instead
    of a data limb misread as a timestamp, and a longer one still reads field `6`. -/
def openVmTimestamp (memBusId : Nat := openVmMemBusId) : BusMessage p → ZMod p :=
  fun m => if m.1 = memBusId then m.2[6]?.getD 0
    else if m.1 = openVmExecBusId then m.2[1]?.getD 0 else 0

/-- OpenVM's `MemoryConfig.timestamp_max_bits`: "all timestamps must be in the range
    `[0, 2 ^ timestamp_max_bits)`". Capped at `29` by OpenVM itself, and `29` is its default.

    The cap is exactly the anti-wraparound condition of `assertLtChip`: `AssertLtSubAir` decides
    `x < y` by range-checking `y - x - 1` to this many bits, which is the same question only while
    `2 ^ (bits + 1) < p`. For BabyBear `2 ^ 30 < 2013265921`, and `30` bits would not fit —
    hence `29`. -/
def openVmTimestampBits : ℕ := 29

/-- The ceiling every timestamp in a segment sits below, and — the same constant, and not by
    accident — the furthest back a memory access may reach. The lt gadget is sized so that any
    difference between two legitimate timestamps fits in it, which is why merging accesses can
    never push one out of its range: both endpoints stay in `[0, openVmTimestampBound)`.

    This is `Circuit.hasStepLayout`'s `maxLookback` for OpenVM, and the bound
    `ConnectorBoundary.finalTimestampBounded` range-checks. -/
def openVmTimestampBound : ℕ := 2 ^ openVmTimestampBits

/-- How far `openVmRank` shifts a timestamp before reading it as a natural.

    A memory *receive* names a record from before its own step, so its offset from the step's base
    is negative and its raw `.val` may have wrapped. Shifting by the maximum lookback moves the
    whole window `[-maxLookback, maxWindow)` into the non-negative naturals, which is what makes
    the rank monotone in the offset — the one thing the soundness induction needs of it. -/
def openVmRankShift : ℕ := openVmTimestampBound

/-- OpenVM's ordering on stateful state: a message's timestamp, shifted into the naturals by
    `openVmRankShift`, which is what makes `<` well-founded and
    `maintains_of_stateful_active`'s induction possible. Off the stateful buses the rank is `0`;
    nothing there needs the induction. -/
def openVmRank (memBusId : Nat := openVmMemBusId) : BusMessage p → ℕ :=
  fun m => if m.1 = memBusId ∨ m.1 = openVmExecBusId then
    ((openVmTimestamp memBusId m) + (openVmRankShift : ZMod p)).val else 0

/-- The `RankModel.bound` that goes with `openVmRank` (see `openVmRankModel`): the timestamp
    ceiling plus the shift that makes room for a step's lookback. `2 ^ 30` for the default
    configuration — exactly the headroom OpenVM already reserves for `AssertLtSubAir`. -/
def openVmRankBound : ℕ := openVmTimestampBound + openVmRankShift

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

    Agrees with `openVmRank` on the memory bus. This is `GuestBusRules.getTimestamp`
    (`Legal.lean`) for OpenVM. -/
def openVmMemTimestamp (m : BusMessage p) : ZMod p := m.2[6]?.getD 0

/-- This aggregates OpenVM's rules about how guests use buses.

    We deliberately copy the existing `accepts` function (which defines the tables) from
    `OpenVmSemantics.lean` rather than restate it here. So, we are trusting their table definitions.

    `execBusId` is fixed at `openVmExecBusId` because that is `defaultBusMap`'s own convention
    (see `StepLayout`'s uses throughout this file); `getTimestamp` is
    `openVmMemTimestamp`. -/
def openVmGuestRules (busMap : BusMap) (memBusId : Nat) : GuestBusRules p where
  isStateful := openVmIsStateful busMap
  accepts := ApcOptimizer.OpenVM.accepts busMap
  payloadOk := openVmPayloadOk busMap
  execBusId := openVmExecBusId
  memBusId := memBusId
  getTimestamp := openVmTimestamp memBusId

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
  finalTimestampBounded : finalTimestamp.val < openVmTimestampBound

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
  instanceBound := 1

/-- **How one OpenVM segment is configured.** Everything `openVmHost` needs that is not fixed by
    OpenVM itself, bundled so that the theorems about it quantify over a single `P` rather than
    over five numbers and two inequalities.

    The two `Ok` fields are the anti-wraparound conditions, and they are *proof obligations on the
    configuration*, checked once here rather than carried through every statement: a segment
    proved at these sizes is one whose timestamps and multiplicities provably stay inside
    `ZMod p`. There is no degree bound among them — that belongs to the proving backend rather
    than the VM, and is a parameter of `PreservesDegree`. -/
structure OpenVmParams (p : ℕ) where
  /-- The VM's trace budget (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- The register the input chip peeks for its write pointer. -/
  ptrReg : Nat
  /-- The most input-chip instances a segment may realize. Every other host chip is capped at one
      instance, so this is what keeps the host side of a run finite
      (`HostAssignment.satisfies`). One instance is one `HINT_STOREW`, hence one input datum: an
      N-word chunk costs N instances of this budget. -/
  maxInputInstances : ℕ
  /-- The `StepLayout` window bound: `StepLayout.dLt`. A property of the chips being run rather
      than of OpenVM — a fused APC advances by its whole basic block, not by one instruction's
      `timestamp_delta`. -/
  maxWindow : ℕ
  /-- The most bus interactions a guest chip may carry. -/
  maxInteractions : ℕ
  /-- No timestamp overflow on the *whole* execution bridge — guest instances and input-chip
      instances together, since both now sit on it (`InputRead.pcFrom`/`pcTo`). Strictly more
      than `Host.noTimeOverflow` (which only needs the guest term); `openVmHost` derives that
      weaker fact from this one. -/
  windowOk : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p
  budgetOk : maxInteractions * maxInstances + 1 < p
  /-- An input-chip instance's own clock advance fits the window too. Pinned rather than
      per-witness, since `inputStepWindow` is a constant (`inputHostChip`). -/
  inputWindowOk : inputStepWindow < maxWindow
  /-- The rank window fits in the field: a timestamp below the ceiling, shifted by the maximum
      lookback, is still an honest natural. This is OpenVM's own `2 ^ (timestamp_max_bits + 1) < p`
      — the condition that caps `timestamp_max_bits` at `29` for BabyBear, and exactly the headroom
      `AssertLtSubAir` already needs. -/
  rankWindowOk : openVmRankBound < p

/-- A concrete OpenVM `Host`: `defaultBusMap`'s four stateless lookup tables (default bus ids),
    memory initialization (all-zero) and finalization, the output chip, a `HINT_STOREW` input chip
    that peeks register `P.ptrReg` — all sharing `openVmMemBusId`, `defaultBusMap`'s
    memory bus — and the connector, which seeds and terminates the execution bridge.

    No `memBusId`/`busMap` parameters: every chip below is already pinned to `defaultBusMap`'s own
    numbering (the same way `pcLookupHostChip`'s default `busId` is), so a free `memBusId` would
    only be able to disagree with it, not vary it — `openVmGuestRules defaultBusMap openVmMemBusId`
    already reads bus `openVmMemBusId` as `.memory` (`defaultBusMap`'s `1 ↦ some .memory` arm).

    Pair with a `Guest p` of guest chips to get a `Vm p`, or feed straight into
    `CanEffect`/`vmEquivalent`. -/
noncomputable def openVmHost (P : OpenVmParams p) : Host p where
  maxInstances := P.maxInstances
  maxWindow := P.maxWindow
  maxLookback := openVmTimestampBound
  maxInteractions := P.maxInteractions
  legalGuest c :=
    c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
      openVmTimestampBound P.maxInteractions
  chips :=
    [ pcLookupHostChip, bitwiseLookupHostChip, variableRangeCheckerHostChip,
      tupleRangeCheckerHostChip, memoryInitHostChip,
      memoryFinalizeHostChip, outputHostChip,
      inputHostChip P.ptrReg P.maxInputInstances, connectorHostChip ]
  inputChips := [⟨7, by simp⟩]
  getInputChunk := fun _ => inputChunkOf P.ptrReg openVmExecBusId openVmMemBusId
  getInputTime := fun _ => inputTimeOf P.ptrReg openVmExecBusId openVmMemBusId
  outputChip := ⟨6, by simp⟩
  getOutput := outputArrayOf openVmMemBusId
  noTimeOverflow := by
    have h := P.windowOk
    calc (P.maxInstances + 1) * (P.maxWindow + 1)
        ≤ (P.maxInstances + P.maxInputInstances + 1) * (P.maxWindow + 1) :=
          Nat.mul_le_mul_right _ (by omega)
      _ < p := h
  noMultOverflow := P.budgetOk

/-- `openVmHost`'s one input chip. `Host.inputChips` is a list — a VM may pull input through
    several chip types — but this host models only `HINT_STOREW`, so the list is this singleton
    (`openVmHost_inputChips`). -/
def openVmInputChip (P : OpenVmParams p) : Fin (openVmHost P).chips.length :=
  ⟨7, by simp [openVmHost]⟩

@[simp] theorem openVmHost_inputChips (P : OpenVmParams p) :
    (openVmHost P).inputChips = [openVmInputChip P] := rfl

end ApcOptimizer.OpenVM
