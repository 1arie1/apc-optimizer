import ApcOptimizer.VmSpec.Theorems
import ApcOptimizer.VmSpec.Implementation.Validation

set_option autoImplicit false

/-! **Auditing `Circuit.legalGuest` against real OpenVM circuit shapes.**

    A memory send in OpenVM carries byte-valued limbs for exactly one of two reasons, and the file
    checks that `Circuit.statefulSendsMaintain` accepts both.

    **Read-echo.** Every OpenVM memory access receives the cell's previous record (multiplicity
    `-1`, `[address space, pointer, four data limbs, previous timestamp]`) and sends the *same
    data* back at a fresh timestamp (`+1`). The sent limbs are bytes only because the received ones
    were; no algebraic constraint and no lookup bounds them. `readEchoChip` is that shape in
    isolation, and it is where the rank hypothesis earns its keep — the send at `t₁` discharges its
    obligation from the receive at `t₀`, and only because `t₀ < t₁`.

    That last inequality is *derived here, not assumed*, and the derivation is the point.
    Legality here is stated against `openVmGuestRules`, so what a stateful send has to produce is
    `openVmPayloadOk` — the byte condition, written out — rather than anything about a
    `BusSemantics`.

    `MemoryOfflineChecker` does not constrain `prev_timestamp < timestamp` directly: it attaches an
    `AssertLtSubAir`, which range-checks the limbs of `timestamp - prev_timestamp - 1` — two limbs
    of 17 and 12 bits, at the default `timestamp_max_bits = 29`. `readEchoChip` carries exactly
    that gadget (`assertLtLoLookup`, `assertLtHiLookup`, `assertLtConstraint`), and a small
    difference orders the two timestamps *only* inside OpenVM's rank window
    (`openVmRankBound`) — otherwise `t₁` may simply have wrapped. So the derivation consumes all
    three of `Circuit.statefulSendsMaintain`'s hypotheses. `staleEchoChip_not_legalGuest` drops the
    gadget and shows the chip is then rejected, so none of this is decorative.

    **Fresh write.** A value the chip computes and writes is byte-valued because of a
    bitwise-lookup range check — OpenVM's own `op = 1, x = y` idiom, since `xor x x = 0` holds for
    any byte. `freshWriteChip` has no stateful traffic below its send's rank at all, so what
    carries it is `Circuit.statelessAccepted` (`freshWriteChip_legalGuest`).

    Neither hypothesis is circular: the rank one is the induction hypothesis of
    `maintains_of_stateful_active`, and the lookup one is `statelessAccepted_of_sinks`, which uses
    no stateful clause. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- The rank OpenVM gives a seven-field memory record: its timestamp. -/
theorem openVmRank_mem (ptr d0 d1 d2 d3 ts : ZMod p) :
    openVmRank openVmMemBusId (1, [1, ptr, d0, d1, d2, d3, ts]) = ts.val := by
  simp [openVmRank]

/-- `openVmPayloadOk` on a register record is exactly "the data limbs are bytes". Both directions
    are used below: a receive hands one over, a send has to produce one. -/
theorem openVmPayloadOk_mem_iff [Fact (1 < p)] (ptr d0 d1 d2 d3 ts : ZMod p) :
    openVmPayloadOk (p := p) defaultBusMap (1, [1, ptr, d0, d1, d2, d3, ts]) ↔
      (isByte d0 ∧ isByte d1 ∧ isByte d2 ∧ isByte d3) := by
  simp only [openVmPayloadOk, defaultBusMap, memoryPayload?]
  constructor
  · intro h
    have h' := h (Or.inl (ZMod.val_one p))
    exact ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩
  · rintro ⟨h0, h1, h2, h3⟩ - d hd
    simp at hd
    rcases hd with rfl | rfl | rfl | rfl <;> assumption

--------- The read-echo shape ---------

/-- The receive half of a memory access: the cell's previous record, at address space `1`
    (registers). The data limb `x` is a free variable — no algebraic constraint mentions it,
    exactly as for a register the circuit reads and passes on. -/
def readEchoRecv (x : Variable) (ptr t₀ : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const (-1)
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t₀]

/-- The send half: the same data limbs, at a fresh timestamp. -/
def readEchoSend (x : Variable) (ptr t₁ : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const 1
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t₁]

/-- `AssertLtSubAir`'s low limb, range-checked to the variable range checker's own
    `range_max_bits = 17`. The width is written as a `ℕ` cast because that is what
    `accepts` reads back out of the payload. -/
def assertLtLoLookup (lo : Variable) : BusInteraction (Expression p) where
  busId := 3
  multiplicity := .const 1
  payload := [.var lo, .const ((17 : ℕ) : ZMod p)]

/-- The high limb, carrying the remaining `29 - 17 = 12` bits of `openVmTimestampBits`. -/
def assertLtHiLookup (hi : Variable) : BusInteraction (Expression p) where
  busId := 3
  multiplicity := .const 1
  payload := [.var hi, .const ((12 : ℕ) : ZMod p)]

/-- `AssertLtSubAir`'s one algebraic constraint, `t₁ - t₀ - 1 = lo + 2 ^ 17 * hi`. Together with
    the two range checks this is *all* OpenVM says about the two timestamps. -/
def assertLtConstraint (lo hi : Variable) (t₀ t₁ : ZMod p) : Expression p :=
  .add (.const (t₁ - t₀ - 1))
    (.mul (.const (-1)) (.add (.var lo) (.mul (.const ((2 ^ 17 : ℕ) : ZMod p)) (.var hi))))

/-- The chip: one memory access, with the timestamp comparison OpenVM attaches to it. -/
def readEchoChip (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) : Circuit p where
  algebraicConstraints := [assertLtConstraint lo hi t₀ t₁]
  busInteractions :=
    [readEchoRecv x ptr t₀, readEchoSend x ptr t₁, assertLtLoLookup lo, assertLtHiLookup hi]

/-- Only the two range checks are stateless, and both are sent with multiplicity `1`. -/
theorem readEchoChip_statelessSendOnly (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [readEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl
  · simp [readEchoRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The two memory multiplicities are literally `-1` and `1`. -/
theorem readEchoChip_statefulPolarity (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [readEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- The limb bounds the two range checks buy, read straight out of `accepts` — for *any* circuit
    `c` carrying the two lookups, not just `readEchoChip` itself, so `stepChip` (which wraps the
    same access in an execution-bridge step) can reuse it verbatim. -/
theorem readEcho_limbs [Fact (1 < p)] (hp : 17 < p) {c : Circuit p} (lo hi : Variable)
    (hmemLo : assertLtLoLookup lo ∈ c.busInteractions)
    (hmemHi : assertLtHiLookup hi ∈ c.busInteractions)
    {asg : ChipAssignment p}
    (hacc : c.statelessAccepted (openVmGuestRules defaultBusMap openVmMemBusId) asg) :
    (asg lo).val < 2 ^ 17 ∧ (asg hi).val < 2 ^ 12 := by
  have hlo := hacc (assertLtLoLookup lo) hmemLo rfl one_ne_zero
  have hhi := hacc (assertLtHiLookup hi) hmemHi rfl one_ne_zero
  replace hlo : (((17 : ℕ) : ZMod p)).val ≤ 17 ∧ (asg lo).val < 2 ^ (((17 : ℕ) : ZMod p)).val := hlo
  replace hhi : (((12 : ℕ) : ZMod p)).val ≤ 17 ∧ (asg hi).val < 2 ^ (((12 : ℕ) : ZMod p)).val := hhi
  rw [ZMod.val_natCast_of_lt hp] at hlo
  rw [ZMod.val_natCast_of_lt (by omega)] at hhi
  exact ⟨hlo.2, hhi.2⟩

/-- The limb bounds, specialized to `readEchoChip` itself. -/
theorem readEchoChip_limbs [Fact (1 < p)] (hp : 17 < p) (x lo hi : Variable) (ptr t₀ t₁ : ZMod p)
    {asg : ChipAssignment p}
    (hacc : (readEchoChip x lo hi ptr t₀ t₁).statelessAccepted
      (openVmGuestRules defaultBusMap openVmMemBusId) asg) :
    (asg lo).val < 2 ^ 17 ∧ (asg hi).val < 2 ^ 12 :=
  readEcho_limbs hp lo hi (by simp [readEchoChip]) (by simp [readEchoChip]) hacc

/-- **The timestamps really do increase.** Everything OpenVM checks, and nothing more: the two
    range checks bound the limbs, the algebraic constraint ties them to `t₁ - t₀ - 1`, and the VM's
    rank window bounds `t₀`. Drop that last piece and the conclusion is false — a small difference
    says nothing once `t₁` may have wrapped, which is exactly why `AssertLtSubAir` caps
    `max_bits` at 29 for a 31-bit field.

    Stated against any circuit `c` carrying the access and its gadget, not just `readEchoChip`
    itself, so `stepChip` can reuse it. -/
theorem readEcho_timestamps_increase (hp : 2 ^ 30 < p) {c : Circuit p} (x lo hi : Variable)
    (ptr t₀ t₁ : ZMod p)
    (hmemCon : assertLtConstraint lo hi t₀ t₁ ∈ c.algebraicConstraints)
    (hmemRecv : readEchoRecv x ptr t₀ ∈ c.busInteractions)
    {asg : ChipAssignment p}
    (halg : c.satisfiesAlgebraic asg)
    (hlo : (asg lo).val < 2 ^ 17) (hhi : (asg hi).val < 2 ^ 12)
    (hranks : c.ranksBounded (openVmRank openVmMemBusId) openVmRankBound asg) :
    t₀.val < t₁.val := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  -- `t₁ = t₀ + 1 + (lo + 2 ^ 17 * hi)`, the constraint rearranged.
  have hcon : t₁ = t₀ + 1 + (asg lo + ((2 ^ 17 : ℕ) : ZMod p) * asg hi) := by
    have h := halg (assertLtConstraint lo hi t₀ t₁) hmemCon
    show t₁ = _
    replace h : (t₁ - t₀ - 1) + (-1) * (asg lo + ((2 ^ 17 : ℕ) : ZMod p) * asg hi) = 0 := h
    linear_combination h
  -- The same equation over `ℕ`, which is where the wraparound question lives.
  set n : ℕ := (asg lo).val + 2 ^ 17 * (asg hi).val with hn
  have hnlt : n < 2 ^ 29 := by rw [hn]; omega
  have hncast : ((n : ℕ) : ZMod p) = asg lo + ((2 ^ 17 : ℕ) : ZMod p) * asg hi := by
    rw [hn]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  -- `t₀` is in the window: the chip actively receives at it.
  have ht₀ : t₀.val < 2 ^ 29 := by
    have hb := hranks (readEchoRecv x ptr t₀) hmemRecv
      (by exact neg_ne_zero.mpr one_ne_zero)
    rw [show (((readEchoRecv x ptr t₀).eval asg).busId,
      ((readEchoRecv x ptr t₀).eval asg).payload)
        = ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, t₀]) from rfl, openVmRank_mem] at hb
    simpa [openVmRankBound, openVmTimestampBits] using hb
  -- No wraparound, so the field equation is a natural-number equation.
  have hcast : ((t₀.val + 1 + n : ℕ) : ZMod p) = t₁ := by
    push_cast [hncast, ZMod.natCast_val, ZMod.cast_id]
    linear_combination -hcon
  have hval : t₁.val = t₀.val + 1 + n := by
    rw [← hcast, ZMod.val_natCast_of_lt (by omega)]
  omega

/-- The timestamp-ordering fact, specialized to `readEchoChip` itself. -/
theorem readEchoChip_timestamps_increase (hp : 2 ^ 30 < p) (x lo hi : Variable)
    (ptr t₀ t₁ : ZMod p) {asg : ChipAssignment p}
    (halg : (readEchoChip x lo hi ptr t₀ t₁).satisfiesAlgebraic asg)
    (hlo : (asg lo).val < 2 ^ 17) (hhi : (asg hi).val < 2 ^ 12)
    (hranks : (readEchoChip x lo hi ptr t₀ t₁).ranksBounded (openVmRank openVmMemBusId) openVmRankBound asg) :
    t₀.val < t₁.val :=
  readEcho_timestamps_increase hp x lo hi ptr t₀ t₁ (by simp [readEchoChip])
    (by simp [readEchoChip]) halg hlo hhi hranks

/-- **The read-echo discharges its obligation from its own receive.** This is the case
    `Circuit.statefulSendsMaintain`'s rank hypothesis exists for: nothing algebraic bounds `x`, and
    the send is byte-valued purely because the strictly-earlier receive was. -/
theorem readEchoChip_statefulSendsMaintain (hp : 2 ^ 30 < p) (x lo hi : Variable)
    (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statefulSendsMaintain
      (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) openVmRankBound := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  intro asg halg hacc hranks bi hbi hst hmult hlow
  simp only [readEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  obtain ⟨hlo, hhi⟩ := readEchoChip_limbs (by omega) x lo hi ptr t₀ t₁ hacc
  have hts : t₀.val < t₁.val :=
    readEchoChip_timestamps_increase hp x lo hi ptr t₀ t₁ halg hlo hhi hranks
  rcases hbi with rfl | rfl | rfl | rfl
  · -- The receive: `hmult` claims `-1 = 1`, which needs `p ∣ 2`.
    exfalso
    replace hmult : (-1 : ZMod p) = 1 := hmult
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -hmult
    have hv : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_natCast_of_lt (by omega)
    rw [h2, ZMod.val_zero] at hv
    omega
  · -- The send: the receive is active, on the memory bus, at a strictly smaller rank.
    have hrecv : readEchoRecv x ptr t₀ ∈ (readEchoChip x lo hi ptr t₀ t₁).busInteractions := by
      simp [readEchoChip]
    have hlt : openVmRank openVmMemBusId (((readEchoRecv x ptr t₀).eval asg).busId,
        ((readEchoRecv x ptr t₀).eval asg).payload) <
        openVmRank openVmMemBusId (((readEchoSend x ptr t₁).eval asg).busId,
          ((readEchoSend x ptr t₁).eval asg).payload) := by
      show openVmRank openVmMemBusId (1, [1, ptr, asg x, 0, 0, 0, t₀]) <
        openVmRank openVmMemBusId (1, [1, ptr, asg x, 0, 0, 0, t₁])
      rw [openVmRank_mem, openVmRank_mem]
      exact hts
    have hx : isByte (asg x) :=
      ((openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 t₀).mp
        (hlow (readEchoRecv x ptr t₀) hrecv rfl (by exact neg_ne_zero.mpr one_ne_zero) hlt)).1
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, t₁])
    exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 t₁).mpr
      ⟨hx, isByte_zero, isByte_zero, isByte_zero⟩
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- **Hence the read-echo chip meets `Circuit.legalGuest`'s bus-facing conditions** —
    unconditionally, with the timestamp ordering derived from the gadget rather than hypothesized.

    Not literally a `Circuit.legalGuest` instance: that structure's fourth field,
    `advancesClock`, needs an execution-bridge step this bare access doesn't wrap itself in —
    `readEchoChip` is deliberately the memory access *in isolation* (see the module docstring).
    `stepChip_legalGuest` below is the genuine, full example; this is the lemma it's built from. -/
theorem readEchoChip_legalGuest (hp : 2 ^ 30 < p) (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) ∧
      (readEchoChip x lo hi ptr t₀ t₁).statefulPolarity (openVmGuestRules defaultBusMap openVmMemBusId) ∧
      (readEchoChip x lo hi ptr t₀ t₁).statefulSendsMaintain
        (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) openVmRankBound :=
  ⟨readEchoChip_statelessSendOnly x lo hi ptr t₀ t₁,
    readEchoChip_statefulPolarity x lo hi ptr t₀ t₁,
    readEchoChip_statefulSendsMaintain hp x lo hi ptr t₀ t₁⟩

--------- The execution-bridge step ---------

/-- The execution-bridge receive: the instruction's incoming state `(pc, t)` (whitepaper §4.5,
    `ExecutionBus::execute` receives `prev_state`). -/
def bridgeRecv (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const (-1)
  payload := [.const pc, .const t]

/-- The execution-bridge send: the outgoing state. -/
def bridgeSend (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const 1
  payload := [.const pc, .const t]

/-- A whole instruction executor: `readEchoChip`'s memory access wrapped in the execution-bridge
    step it belongs to. Timestamps are laid out as OpenVM lays them out — the step runs from `base`
    to `base + 3`, and the access reads at `base + 1` and writes at `base + 2`, strictly inside
    (whitepaper §4.2). This is the shape `Circuit.advancesClock` describes, and the chip below is
    the check that the predicate is satisfiable by a realistic one. -/
def stepChip (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) : Circuit p where
  algebraicConstraints := [assertLtConstraint lo hi (base + 1) (base + 2)]
  busInteractions :=
    [bridgeRecv pcFrom base, bridgeSend pcTo (base + 3),
      readEchoRecv x ptr (base + 1), readEchoSend x ptr (base + 2),
      assertLtLoLookup lo, assertLtHiLookup hi]

/-- **`Circuit.advancesClock` accepts a realistic instruction executor.** One bridge receive at
    `base`, one send three ticks later, and both memory accesses strictly between — with the
    offsets given as naturals, so nothing here compares field elements. -/
theorem stepChip_advancesClock (hp : 3 < p) {maxWindow : ℕ} (hw : 3 < maxWindow)
    (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    Circuit.advancesClock (stepChip x lo hi pcFrom pcTo ptr base)
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow := by
  have hcast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by push_cast; ring
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 3 < p by omega)
    rw [hcast3, h, ZMod.val_zero] at hv
    omega
  refine fun asg _ => ⟨pcFrom, pcTo, base, 3, by omega, hw, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      openVmGuestRules, h3]
  · simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      openVmGuestRules, h3]
  · rintro ⟨mb, ml⟩ hbus hr hs
    simp only [openVmGuestRules] at hbus
    subst hbus
    simp only [ne_eq, Prod.mk.injEq, true_and, hcast3, openVmGuestRules] at hr hs
    simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      Ne.symm hr, Ne.symm hs]
  · intro bi hbi _ _
    simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [bridgeRecv, openVmGuestRules] at *
    · simp [bridgeSend, openVmGuestRules] at *
    · exact ⟨1, by omega, by omega, by
        simp [readEchoRecv, openVmGuestRules, BusInteraction.eval, Expression.eval,
          openVmMemTimestamp]⟩
    · exact ⟨2, by omega, by omega, by
        simp [readEchoSend, openVmGuestRules, BusInteraction.eval, Expression.eval,
          openVmMemTimestamp]⟩
    · simp [assertLtLoLookup, openVmGuestRules] at *
    · simp [assertLtHiLookup, openVmGuestRules] at *

/-- Only the two range checks are stateless; the bridge pair and the memory access are both
    stateful. -/
theorem stepChip_statelessSendOnly (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [bridgeRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [bridgeSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- Every stateful multiplicity — both bridge messages, both memory ones — is literally `-1` or
    `1`. -/
theorem stepChip_statefulPolarity (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- **`stepChip`'s sends all discharge their obligation.** The bridge send is on the execution
    bridge, where `openVmPayloadOk` is trivially `True`; the memory send is exactly
    `readEchoChip`'s case, reusing `readEcho_limbs`/`readEcho_timestamps_increase` against
    `stepChip`'s own membership facts instead of duplicating the derivation. -/
theorem stepChip_statefulSendsMaintain (hp : 2 ^ 30 < p) (x lo hi : Variable)
    (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).statefulSendsMaintain
      (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) openVmRankBound := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  intro asg halg hacc hranks bi hbi hst hmult hlow
  have hmemLo : assertLtLoLookup lo ∈ (stepChip x lo hi pcFrom pcTo ptr base).busInteractions := by
    simp [stepChip]
  have hmemHi : assertLtHiLookup hi ∈ (stepChip x lo hi pcFrom pcTo ptr base).busInteractions := by
    simp [stepChip]
  obtain ⟨hlo, hhi⟩ := readEcho_limbs (by omega) lo hi hmemLo hmemHi hacc
  have hmemCon : assertLtConstraint lo hi (base + 1) (base + 2) ∈
      (stepChip x lo hi pcFrom pcTo ptr base).algebraicConstraints := by simp [stepChip]
  have hmemRecv : readEchoRecv x ptr (base + 1) ∈
      (stepChip x lo hi pcFrom pcTo ptr base).busInteractions := by simp [stepChip]
  have hts : (base + 1).val < (base + 2).val :=
    readEcho_timestamps_increase hp x lo hi ptr (base + 1) (base + 2) hmemCon hmemRecv halg hlo
      hhi hranks
  simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bridgeRecv: a receive, `hmult` claims `-1 = 1`.
    exfalso
    replace hmult : (-1 : ZMod p) = 1 := hmult
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -hmult
    have hv : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_natCast_of_lt (by omega)
    rw [h2, ZMod.val_zero] at hv
    omega
  · -- bridgeSend: the execution bridge accepts everything.
    simp [openVmGuestRules, openVmPayloadOk, defaultBusMap, bridgeSend, BusInteraction.eval,
      Expression.eval]
  · -- readEchoRecv: a receive, same trick.
    exfalso
    replace hmult : (-1 : ZMod p) = 1 := hmult
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -hmult
    have hv : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_natCast_of_lt (by omega)
    rw [h2, ZMod.val_zero] at hv
    omega
  · -- readEchoSend: the receive is active, on the memory bus, at a strictly smaller rank.
    have hlt : openVmRank openVmMemBusId (((readEchoRecv x ptr (base + 1)).eval asg).busId,
        ((readEchoRecv x ptr (base + 1)).eval asg).payload) <
        openVmRank openVmMemBusId (((readEchoSend x ptr (base + 2)).eval asg).busId,
          ((readEchoSend x ptr (base + 2)).eval asg).payload) := by
      show openVmRank openVmMemBusId (1, [1, ptr, asg x, 0, 0, 0, base + 1]) <
        openVmRank openVmMemBusId (1, [1, ptr, asg x, 0, 0, 0, base + 2])
      rw [openVmRank_mem, openVmRank_mem]
      exact hts
    have hx : isByte (asg x) :=
      ((openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 1)).mp
        (hlow (readEchoRecv x ptr (base + 1)) hmemRecv rfl
          (by exact neg_ne_zero.mpr one_ne_zero) hlt)).1
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 2])
    exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 2)).mpr
      ⟨hx, isByte_zero, isByte_zero, isByte_zero⟩
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- **The full example `Circuit.legalGuest` exists for: a realistic instruction executor.**
    `stepChip` is `readEchoChip`'s memory access wrapped in the execution-bridge step OpenVM
    requires around it, and it satisfies all four conditions — this is the file's answer to
    "is `Circuit.legalGuest` satisfiable by anything a real VM would actually run". -/
theorem stepChip_legalGuest (hp : 2 ^ 30 < p) {maxWindow : ℕ} (hw : 3 < maxWindow)
    (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).legalGuest (openVmGuestRules defaultBusMap openVmMemBusId)
      (openVmRank openVmMemBusId) openVmRankBound maxWindow where
  sendOnly := stepChip_statelessSendOnly x lo hi pcFrom pcTo ptr base
  polarity := stepChip_statefulPolarity x lo hi pcFrom pcTo ptr base
  sendsMaintain := stepChip_statefulSendsMaintain hp x lo hi pcFrom pcTo ptr base
  advancesClock := stepChip_advancesClock (by omega) hw x lo hi pcFrom pcTo ptr base

/-- The same access with `AssertLtSubAir` removed: the word is handed back at the timestamp it was
    found at. -/
def staleEchoChip (x : Variable) (ptr t : ZMod p) : Circuit p where
  algebraicConstraints := []
  busInteractions := [readEchoRecv x ptr t, readEchoSend x ptr t]

/-- **And the gadget is doing real work.** Strip it out and the chip is rejected: with the two
    timestamps equal the rank hypothesis is vacuous, so nothing establishes that the limb is a
    byte — and indeed nothing in the circuit does. -/
theorem staleEchoChip_not_legalGuest (hp : 256 < p) {maxWindow : ℕ} (x : Variable) (ptr t : ZMod p)
    (ht : t.val < openVmRankBound) :
    ¬ (staleEchoChip x ptr t).legalGuest (openVmGuestRules defaultBusMap openVmMemBusId)
        (openVmRank openVmMemBusId) openVmRankBound maxWindow := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  intro h
  set asg : ChipAssignment p := fun _ => ((256 : ℕ) : ZMod p) with hasg
  have hsend : readEchoSend x ptr t ∈ (staleEchoChip x ptr t).busInteractions := by
    simp [staleEchoChip]
  -- Receive and send sit at the same rank, so nothing is below the send's — the rank hypothesis
  -- is vacuous, and the chip has no lookup to fall back on.
  have hlow : (staleEchoChip x ptr t).lowerRanksMaintain
      (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) asg
      (openVmRank openVmMemBusId (((readEchoSend x ptr t).eval asg).busId,
        ((readEchoSend x ptr t).eval asg).payload)) := by
    intro bj hbj _ _ hlt
    exfalso
    revert hlt
    simp only [staleEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbj
    rcases hbj with rfl | rfl <;> exact lt_irrefl _
  have hranks : (staleEchoChip x ptr t).ranksBounded (openVmRank openVmMemBusId) openVmRankBound asg := by
    intro bi hbi _
    simp only [staleEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl <;>
      · show openVmRank openVmMemBusId ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, t]) < openVmRankBound
        rw [openVmRank_mem]
        exact ht
  have key := h.sendsMaintain asg (by intro c hc; simp [staleEchoChip] at hc)
    (by intro bj hbj hstj _
        simp only [staleEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbj
        rcases hbj with rfl | rfl
        · simp [readEchoRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
            OpenVmBusType.isStateful] at hstj
        · simp [readEchoSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
            OpenVmBusType.isStateful] at hstj)
    hranks _ hsend rfl rfl hlow
  have hbyte : isByte (asg x) := ((openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 t).mp key).1
  replace hbyte : (((256 : ℕ) : ZMod p)).val < 256 := hbyte
  rw [ZMod.val_natCast_of_lt hp] at hbyte
  omega

--------- The remaining gap: values justified by a lookup ---------

/-- The range check: the bitwise bus with `op = 1` and `x = y` is OpenVM's own idiom for
    range-checking a single limb (`xor x x = 0` holds for any byte). -/
def freshWriteLookup (x : Variable) : BusInteraction (Expression p) where
  busId := 6
  multiplicity := .const 1
  payload := [.var x, .var x, .const 0, .const 1]

/-- The write itself. -/
def freshWriteSend (x : Variable) (ptr t : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const 1
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t]

/-- The chip: range-check a limb, then write it. -/
def freshWriteChip (x : Variable) (ptr t : ZMod p) : Circuit p where
  algebraicConstraints := []
  busInteractions := [freshWriteLookup x, freshWriteSend x ptr t]

/-- Only the lookup is stateless, and it is sent with multiplicity `1`. -/
theorem freshWriteChip_statelessSendOnly (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [freshWriteChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl
  · exact Or.inr rfl
  · simp [freshWriteSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- Only the write is stateful, and it is sent with multiplicity `1`. -/
theorem freshWriteChip_statefulPolarity (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [freshWriteChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl
  · simp [freshWriteLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr (Or.inl rfl)

/-- **The fresh write discharges its obligation from its own range check.** The chip has no
    stateful traffic below the send's rank, so `Circuit.lowerRanksMaintain` gives nothing; what
    carries it is `Circuit.statelessAccepted` on the bitwise lookup, whose `op = 1` case is
    exactly `isByte x`. -/
theorem freshWriteChip_statefulSendsMaintain (hp : 256 < p) (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statefulSendsMaintain (openVmGuestRules defaultBusMap openVmMemBusId)
      (openVmRank openVmMemBusId) openVmRankBound := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  intro asg _ hacc _ bi hbi hst _ _
  simp only [freshWriteChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl
  · simp [freshWriteLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · have hlook : freshWriteLookup x ∈ (freshWriteChip x ptr t).busInteractions := by
      simp [freshWriteChip]
    have hacc' := hacc (freshWriteLookup x) hlook rfl one_ne_zero
    replace hacc' : (match ((1 : ZMod p)).val with
      | 0 => isByte (asg x) ∧ isByte (asg x) ∧ ((0 : ZMod p)).val = 0
      | 1 => isByte (asg x) ∧ isByte (asg x) ∧
               ((0 : ZMod p)).val = Nat.xor (asg x).val (asg x).val
      | _ => False) := hacc'
    rw [ZMod.val_one p] at hacc'
    have hx : isByte (asg x) := hacc'.1
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, t])
    exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 t).mpr
      ⟨hx, isByte_zero, isByte_zero, isByte_zero⟩

/-- **So the lookup-justified write meets the same bus-facing conditions too.** With
    `readEchoChip_legalGuest` this covers both shapes an OpenVM memory send has — bare, not
    wrapped in a bridge step, for the same reason (see `readEchoChip_legalGuest`). -/
theorem freshWriteChip_legalGuest (hp : 256 < p) (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) ∧
      (freshWriteChip x ptr t).statefulPolarity (openVmGuestRules defaultBusMap openVmMemBusId) ∧
      (freshWriteChip x ptr t).statefulSendsMaintain
        (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) openVmRankBound :=
  ⟨freshWriteChip_statelessSendOnly x ptr t, freshWriteChip_statefulPolarity x ptr t,
    freshWriteChip_statefulSendsMaintain hp x ptr t⟩

end ApcOptimizer.OpenVM
