import ApcOptimizer.VmSpec.Implementation.Chain
import ApcOptimizer.VmSpec.Implementation.OpenVmConnection

set_option autoImplicit false

/-! **`Host.pinsRanks` for `openVmHost`**: every timestamp in a satisfying run is inside OpenVM's
    rank window. Nothing here is audited.

    The run's execution-bridge traffic is read as a `VmChain.Chain` (`Chain.lean`): one arc per
    realized guest instance, consuming the `(pc, t)` it receives and producing the `(pc', t + d)`
    it sends — `Circuit.advancesClock`, which `openVmHost.legalGuest` requires; one arc per
    realized input-chip instance, doing exactly the same (`InputRead.pcFrom`/`pcTo`/`d` — the
    input chip is an instruction executor too, whitepaper §4.5); plus one arc for the connector,
    which produces `(pc₀, 1)` and consumes the segment's final state. Bus balance on bus `0` is
    exactly the chain's `balanced` field, once the multiplicities are counted as naturals rather
    than field elements.

    The chain then places every instance at a known distance before the connector, so its start
    timestamp is `1 + T` for an honest natural `T` and the whole instruction fits below the final
    timestamp — which `ConnectorBoundary.finalTimestampBounded` range-checks. Every memory access
    of a *guest* instance sits strictly inside its own step (`Circuit.advancesClock` again), so it
    inherits the bound; nothing here claims the same for an input-chip instance's own memory
    accesses (see the lower tier's own note in `agent-docs/vm-spec-audit.md`), since
    `Host.pinsRanks` only bounds guest ranks.

    The one arithmetic input is `OpenVmParams.windowOk` — a field of the host's own configuration,
    not a hypothesis of the theorem below: a run too long to fit in the field could wrap, and then
    "the timestamp went up" would stop meaning anything. `Chain.time_injOn`
    (`openVmHost_inputTime_injOn`, at the bottom) is the other thing this same chain gives for
    free: two different input-chip instances can never land on the same clock reading, which is
    what makes `VmAssignment.orderedInputInstances`' sort by `Host.getInputTime` a genuine order
    rather than one with possible ties. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

--------- One instance's clock witness ---------

/-- The witness `Circuit.advancesClock` supplies for one instance, packaged as data so that a
    whole assignment's worth of witnesses can be chosen at once. -/
structure ClockStep (p : ℕ) (c : Circuit p) (asg : ChipAssignment p)
    (execBusId memBusId maxWindow : ℕ) where
  /-- The `pc` the instruction starts at. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p
  /-- The timestamp it starts at. -/
  base : ZMod p
  /-- How far it advances the clock. -/
  d : ℕ
  dPos : 0 < d
  dLt : d < maxWindow
  recv : c.allEffects asg (execBusId, [pcFrom, base]) = -1
  send : c.allEffects asg (execBusId, [pcTo, base + (d : ZMod p)]) = 1
  other : ∀ m : BusMessage p, m.1 = execBusId → m ≠ (execBusId, [pcFrom, base]) →
    m ≠ (execBusId, [pcTo, base + (d : ZMod p)]) → c.allEffects asg m = 0
  mem : ∀ bi ∈ c.busInteractions, bi.busId = memBusId → (bi.eval asg).multiplicity ≠ 0 →
    ∃ δ : ℕ, 0 < δ ∧ δ < d ∧
      openVmMemTimestamp ((bi.eval asg).busId, (bi.eval asg).payload) = base + (δ : ZMod p)

theorem clockStep_nonempty {c : Circuit p} {asg : ChipAssignment p} {r : GuestBusRules p}
    {maxWindow : ℕ}
    (h : Circuit.advancesClock c r maxWindow) (hsat : c.satisfiesAlgebraic asg)
    (hget : r.getTimestamp = openVmMemTimestamp := by rfl) :
    Nonempty (ClockStep p c asg r.execBusId r.memBusId maxWindow) := by
  obtain ⟨pcFrom, pcTo, base, d, h1, h2, h3, h4, h5, h6⟩ := h asg hsat
  rw [hget] at h6
  exact ⟨⟨pcFrom, pcTo, base, d, h1, h2, h3, h4, h5, h6⟩⟩

--------- Guest nets as sums over instances ---------

/-- `(l.map f).sum` as a `Finset` sum over positions — what turns `GuestAssignment.busEffect`'s
    lists into a sum over a `Fintype` of instances. -/
theorem list_map_sum_eq_sum_fin {α β : Type} [AddCommMonoid β] (l : List α) (f : α → β) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih]; simp [Fin.sum_univ_succ]

/-- The guests' net contribution to a message, indexed by instance rather than by chip type. -/
theorem guestNet_eq_sum_inst {G : Guest p} (gA : GuestAssignment p G)
    (m : BusMessage p) :
    gA.busEffect m = ∑ x : ((s : Fin G.length) × Fin (gA s).length),
      (G.get x.1).allEffects ((gA x.1).get x.2) m := by
  conv_rhs => rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  exact Finset.sum_congr rfl (fun s _ => list_map_sum_eq_sum_fin (gA s) _)

--------- The connector is alone on the execution bridge ---------

/-- The connector's contribution, message by message: it produces its initial state and consumes
    its final one. -/
theorem connector_busStateOf (r : ConnectorBoundary p) (m : BusMessage p) :
    busStateOf (r.interactions 0) m
      = (if ((0 : Nat), [r.initialPc, (1 : ZMod p)]) = m then (1 : ZMod p) else 0)
        - (if ((0 : Nat), [r.finalPc, r.finalTimestamp]) = m then (1 : ZMod p) else 0) := by
  simp only [busStateOf, ConnectorBoundary.interactions, List.filter_cons, List.filter_nil]
  by_cases h1 : ((0 : Nat), [r.initialPc, (1 : ZMod p)]) = m <;>
    by_cases h2 : ((0 : Nat), [r.finalPc, r.finalTimestamp]) = m <;>
    simp [h1, h2]

/-- `busStateOf` distributes over list append: filtering, mapping and summing all do. -/
theorem busStateOf_append (l1 l2 : List (BusInteraction (ZMod p))) (m : BusMessage p) :
    busStateOf (l1 ++ l2) m = busStateOf l1 m + busStateOf l2 m := by
  simp [busStateOf, List.filter_append, List.map_append, List.sum_append]

/-- A list none of whose entries carry `m`'s bus id contributes nothing to `m`. -/
theorem busStateOf_eq_zero_of_busId_ne {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : ∀ e ∈ l, e.busId ≠ m.1) : busStateOf l m = 0 := by
  simp only [busStateOf]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  exact absurd (congrArg Prod.fst (of_decide_eq_true hy2)) (h y hy1)

/-- **An `InputRead`'s contribution, restricted to the execution bridge**: `-1` at the state it
    consumes, `1` at the one it produces, `0` elsewhere — every other interaction it describes is
    on the memory bus, never the bridge (`InputRead.interactions_busId`). Mirrors
    `connector_busStateOf`, since an input-chip instance shares that same bus
    (`InputRead.pcFrom`/`pcTo`/`d`, whitepaper §4.5). -/
theorem inputRead_busStateOf_execBus (r : InputRead p) (ptrReg countReg : Nat) (m : BusMessage p)
    (hm : m.1 = 0) :
    busStateOf (r.interactions ptrReg countReg 0 1) m
      = (if ((0 : Nat), [r.pcTo, r.base + (r.d : ZMod p)]) = m then (1 : ZMod p) else 0)
        - (if ((0 : Nat), [r.pcFrom, r.base]) = m then (1 : ZMod p) else 0) := by
  rw [InputRead.interactions, busStateOf_append, busStateOf_append]
  have hz1 : busStateOf
      [ { busId := 1, multiplicity := (-1 : ZMod p),
            payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime] },
        { busId := 1, multiplicity := 1,
            payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base] },
        { busId := 1, multiplicity := (-1 : ZMod p),
            payload := [1, (countReg : ZMod p)] ++ r.countLimbs.toList ++ [r.countTime] },
        { busId := 1, multiplicity := 1,
            payload := [1, (countReg : ZMod p)] ++ r.countLimbs.toList ++ [r.base + 1] } ] m
      = 0 := by
    refine busStateOf_eq_zero_of_busId_ne (fun e he => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [hm]
  have hz2 : busStateOf
      (((List.range r.count.val).zip (r.bytes.zip (r.oldWords.zip r.wordTimes))).flatMap
        (fun (i, b, old, t) =>
          [ { busId := 1, multiplicity := (-1 : ZMod p),
              payload := [2, r.ptr + (i : ZMod p)] ++ old.toList ++ [t] },
            { busId := 1, multiplicity := 1,
              payload := [2, r.ptr + (i : ZMod p), b, 0, 0, 0, r.base + 2 + (i : ZMod p)] } ])) m
      = 0 := by
    refine busStateOf_eq_zero_of_busId_ne (fun e he => ?_)
    obtain ⟨⟨i, b, old, t⟩, -, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [hm]
  rw [hz1, hz2, add_zero, add_zero]
  simp only [busStateOf, List.filter_cons, List.filter_nil]
  by_cases h1 : ((0 : Nat), [r.pcFrom, r.base]) = m <;>
    by_cases h2 : ((0 : Nat), [r.pcTo, r.base + (r.d : ZMod p)]) = m <;>
    simp [h1, h2]

/-- **Only the connector and the input chip touch the execution bridge.** The four lookup chips
    pin their bus id to a lookup bus and the four other memory-bus chips to memory, so on bus `0`
    the host's whole net is the connector's plus every realized input-chip instance's own bridge
    step (`InputRead.pcFrom`/`pcTo`/`d`) — the input chip is an instruction executor like any
    other guest, just one the host runs instead of the trace's own program. The connector runs at
    most once, so there is a single witness to name; a segment that leaves it out nets nothing on
    the bridge, which is what the degenerate boundary (start and end state equal) describes, so
    the walk below need not know which case it is in. -/
theorem openVmHost_bridge_isolated (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)}
    (hlegal : hA.satisfies) :
    ∃ (r : ConnectorBoundary p) (iR : Fin (hA (openVmHost P).inputChip).length → InputRead p),
      (∀ i, (iR i).d < P.maxWindow) ∧
      (∀ i, (hA (openVmHost P).inputChip).get i
          = busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1)) ∧
      (∀ i, (openVmHost P).getInputTime ((hA (openVmHost P).inputChip).get i) = (iR i).base) ∧
      ∀ m : BusMessage p, m.1 = 0 →
        hA.busEffect m = busStateOf (r.interactions 0) m +
          ∑ i, busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1) m := by
  classical
  -- The connector's single instance.
  have hconnIdx : (openVmHost P).chips.length = 9 :=
    rfl
  set k : Fin (openVmHost P).chips.length :=
    ⟨8, by rw [hconnIdx]; omega⟩ with hk
  have hlen : (hA k).length ≤ 1 := hlegal.withinBound k
  obtain ⟨r, hr⟩ : ∃ r : ConnectorBoundary p, ∀ m : BusMessage p,
      ((hA k).map (fun effect => effect m)).sum = busStateOf (r.interactions 0) m := by
    match hc : hA k, hlen with
    | [], _ =>
      -- `windowOk` is what says the field is not the degenerate one, so `1` is a real timestamp.
      have hp1 : 1 < p :=
        lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
          P.windowOk
      haveI : NeZero p := ⟨by omega⟩
      haveI : Fact (1 < p) := ⟨hp1⟩
      refine ⟨⟨0, 0, 1, ?_⟩, fun m => ?_⟩
      · rw [ZMod.val_one]
        norm_num [openVmRankBound, openVmTimestampBits]
      · simp [connector_busStateOf]
    | [c], _ =>
      obtain ⟨r, hr⟩ : (connectorHostChip (p := p) 0).canProduce c :=
        hlegal.producible k c (by rw [hc]; exact List.mem_singleton_self c)
      exact ⟨r, fun m => by rw [hr]; simp⟩
  -- The input chip's own instances, each pinned to an `InputRead` witness.
  set j : Fin (openVmHost P).chips.length := (openVmHost P).inputChip with hj
  have hchoice : ∀ i : Fin (hA j).length,
      ∃ r : InputRead p, r.d < P.maxWindow ∧
        (hA j).get i = busStateOf (r.interactions P.ptrReg P.countReg 0 1) :=
    fun i => hlegal.producible j ((hA j).get i) (List.get_mem (hA j) i)
  set iR : Fin (hA j).length → InputRead p := fun i => (hchoice i).choose with hiRdef
  have hiRlt : ∀ i, (iR i).d < P.maxWindow := fun i => (hchoice i).choose_spec.1
  have hiReq : ∀ i, (hA j).get i = busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1) :=
    fun i => (hchoice i).choose_spec.2
  have hiRtime : ∀ i, (openVmHost P).getInputTime ((hA j).get i) = (iR i).base := by
    intro i
    show inputTimeOf P.ptrReg P.countReg P.maxWindow 0 1 ((hA j).get i) = (iR i).base
    rw [inputTimeOf, dif_pos (hchoice i)]
  refine ⟨r, iR, hiRlt, hiReq, hiRtime, fun m hm => ?_⟩
  have hj_ne_k : j ≠ k := by
    intro h
    have hjv : (j : ℕ) = 7 := rfl
    have hkv : (k : ℕ) = 8 := by rw [hk]
    rw [h, hkv] at hjv
    omega
  -- Every other chip leaves bus `0` alone.
  have hzero :
      ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 8 → (t : ℕ) ≠ 7 → ∀ c' ∈ hA t, c' m = 0 := by
    intro t ht ht7 c' hc'
    have hleg := hlegal.producible t c' hc'
    by_contra hne
    fin_cases t
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; simp only [openVmMemBusId]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; simp only [openVmMemBusId]; omega)
    · obtain ⟨r', hr'⟩ := hleg
      rw [hr'] at hne
      obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hne
      exact absurd ((congrArg Prod.fst heq).symm.trans
        (OutputRead.interactions_busId r' 1 msg hmsg)) (by rw [hm]; omega)
    · exact absurd rfl ht7
    · exact absurd rfl ht
  have hz : ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 8 → (t : ℕ) ≠ 7 → ((hA t).map (fun effect => effect m)).sum = 0 := by
    intro t ht ht7
    refine List.sum_eq_zero (fun v hv => ?_)
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hv
    exact hzero t ht ht7 c' hc'
  have hnet : hA.busEffect m
      = ∑ t : Fin (openVmHost P).chips.length,
        ((hA t).map (fun effect => effect m)).sum := rfl
  have hsum9 : (∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum)
      = ∑ t ∈ ({j, k} : Finset (Fin (openVmHost P).chips.length)),
          ((hA t).map (fun effect => effect m)).sum := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact hz t (fun h => ht.2 (Fin.ext h)) (fun h => ht.1 (Fin.ext h))
  have hinput : ((hA j).map (fun effect => effect m)).sum
      = ∑ i : Fin (hA j).length, busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1) m := by
    rw [list_map_sum_eq_sum_fin]
    exact Finset.sum_congr rfl (fun i _ => by rw [hiReq i])
  rw [hnet, hsum9, Finset.sum_pair hj_ne_k, hinput, hr]
  ring

--------- The bridge as a chain ---------

section Bridge

variable {G : Guest p} {maxWindow : ℕ}

/-- The arcs of a run's execution bridge: one per realized guest instance, one per realized
    input-chip instance — an input-chip instance is an instruction executor sharing the same bus
    (`InputRead.pcFrom`/`pcTo`/`d`, whitepaper §4.5) — plus the connector (`none`). -/
abbrev BridgeArc (gA : GuestAssignment p G) (n : ℕ) : Type :=
  Option (((s : Fin G.length) × Fin (gA s).length) ⊕ Fin n)

variable (gA : GuestAssignment p G) {n : ℕ}
  (S : ∀ x : ((s : Fin G.length) × Fin (gA s).length),
      ClockStep p (G.get x.1) ((gA x.1).get x.2) 0 1 maxWindow)
  (iR : Fin n → InputRead p) (ptrReg countReg : Nat)
  (r : ConnectorBoundary p)

/-- The bridge state an arc consumes: an instruction's incoming `(pc, t)` (guest or input-chip
    instance alike), or, for the connector, the segment's final state. -/
def bridgeSrc : BridgeArc gA n → BusMessage p
  | none => (0, [r.finalPc, r.finalTimestamp])
  | some (.inl x) => (0, [(S x).pcFrom, (S x).base])
  | some (.inr i) => (0, [(iR i).pcFrom, (iR i).base])

/-- The bridge state an arc produces: an instruction's outgoing `(pc, t + d)`, or, for the
    connector, the segment's initial state at timestamp `1`. -/
def bridgeDst : BridgeArc gA n → BusMessage p
  | none => (0, [r.initialPc, 1])
  | some (.inl x) => (0, [(S x).pcTo, (S x).base + ((S x).d : ZMod p)])
  | some (.inr i) => (0, [(iR i).pcTo, (iR i).base + ((iR i).d : ZMod p)])

/-- How far an arc advances the clock; the connector does not. -/
def bridgeAdv : BridgeArc gA n → ℕ
  | none => 0
  | some (.inl x) => (S x).d
  | some (.inr i) => (iR i).d

theorem bridgeSrc_busId (e : BridgeArc gA n) : (bridgeSrc gA S iR r e).1 = 0 := by
  cases e with
  | none => rfl
  | some e' => cases e' <;> rfl

theorem bridgeDst_busId (e : BridgeArc gA n) : (bridgeDst gA S iR r e).1 = 0 := by
  cases e with
  | none => rfl
  | some e' => cases e' <;> rfl

/-- The arcs are the guest instances, the input-chip instances, and one. -/
theorem card_bridgeArc :
    Fintype.card (BridgeArc gA n) = (∑ s : Fin G.length, (gA s).length) + n + 1 := by
  rw [Fintype.card_option, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  simp

/-- A run with at least one guest or input-chip instance is long enough that `p` cannot be tiny —
    which is all the case analysis below needs of it. -/
theorem bridge_p_large {maxInstances maxInputInstances : ℕ}
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) (hw : 2 ≤ maxWindow)
    (hge : 1 ≤ maxInstances + maxInputInstances) : 6 < p := by
  calc 6 = (1 + 1) * (2 + 1) := by norm_num
    _ ≤ (maxInstances + maxInputInstances + 1) * (maxWindow + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ < p := hp

/-- An instruction never consumes and produces the same bridge state: it would have to net both
    `-1` and `1` there. -/
theorem bridge_src_ne_dst (hp6 : 6 < p) (x : (s : Fin G.length) × Fin (gA s).length) :
    bridgeSrc gA S iR r (some (.inl x)) ≠ bridgeDst gA S iR r (some (.inl x)) := by
  intro h
  have h' : ((0 : Nat), [(S x).pcFrom, (S x).base])
      = ((0 : Nat), [(S x).pcTo, (S x).base + ((S x).d : ZMod p)]) := h
  have hrecv := (S x).recv
  rw [h', (S x).send] at hrecv
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have h1 : (1 : ZMod p) + 1 = 0 := eq_neg_iff_add_eq_zero.mp hrecv
    push_cast
    rw [← one_add_one_eq_two]
    exact h1
  exact absurd (VmChain.natCast_eq_zero_of_lt (by omega) h2) (by omega)

/-- **Bus balance on the execution bridge, counted honestly.** Every bridge state is consumed
    exactly as often as it is produced.

    `VmSat` only gives an equation in `ZMod p`; what makes it an equation between *counts* is the
    instance budget, which keeps both counts below `p`. Off bus `0` there is nothing to say: no arc
    touches another bus. -/
theorem bridge_balanced {maxInstances maxInputInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg countReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) (m : BusMessage p) :
    (Finset.univ.filter fun e => bridgeSrc gA S iR r e = m).card
      = (Finset.univ.filter fun e => bridgeDst gA S iR r e = m).card := by
  classical
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  by_cases hm : m.1 = 0
  swap
  · have h1 : (Finset.univ.filter fun e => bridgeSrc gA S iR r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeSrc_busId gA S iR r e
    have h2 : (Finset.univ.filter fun e => bridgeDst gA S iR r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeDst_busId gA S iR r e
    rw [h1, h2]
  -- The field equation, arc by arc.
  have hsplit : ∑ e : BridgeArc gA n,
      ((if bridgeDst gA S iR r e = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S iR r e = m then (1 : ZMod p) else 0)) = 0 := by
    have hsome : ∀ x, (if bridgeDst gA S iR r (some (.inl x)) = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S iR r (some (.inl x)) = m then (1 : ZMod p) else 0)
        = (G.get x.1).allEffects ((gA x.1).get x.2) m := by
      intro x
      have hge : 1 ≤ maxInstances + maxInputInstances :=
        le_trans (le_trans x.2.pos
          (Finset.single_le_sum (f := fun s => (gA s).length) (fun s _ => Nat.zero_le _)
            (Finset.mem_univ x.1))) (le_trans hcount (Nat.le_add_right _ _))
      have hp6 := bridge_p_large (maxWindow := maxWindow) hp
        (by have := (S x).dPos; have := (S x).dLt; omega) hge
      have hne := bridge_src_ne_dst gA S iR r hp6 x
      by_cases hd : bridgeDst gA S iR r (some (.inl x)) = m
      · have hs : bridgeSrc gA S iR r (some (.inl x)) ≠ m := fun h => hne (h.trans hd.symm)
        rw [if_pos hd, if_neg hs, sub_zero, ← hd]
        exact ((S x).send).symm
      · by_cases hs : bridgeSrc gA S iR r (some (.inl x)) = m
        · rw [if_neg hd, if_pos hs, zero_sub, ← hs]
          exact ((S x).recv).symm
        · rw [if_neg hd, if_neg hs, sub_zero]
          exact ((S x).other m hm (fun h => hs h.symm) (fun h => hd h.symm)).symm
    have hsome_input : ∀ i : Fin n,
        (if bridgeDst gA S iR r (some (.inr i)) = m then (1 : ZMod p) else 0)
          - (if bridgeSrc gA S iR r (some (.inr i)) = m then (1 : ZMod p) else 0)
          = busStateOf ((iR i).interactions ptrReg countReg 0 1) m :=
      fun i => (inputRead_busStateOf_execBus (iR i) ptrReg countReg m hm).symm
    have hnone : (if bridgeDst gA S iR r none = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S iR r none = m then (1 : ZMod p) else 0)
        = busStateOf (r.interactions 0) m := (connector_busStateOf r m).symm
    rw [Fintype.sum_option, Fintype.sum_sum_type, hnone,
      Finset.sum_congr rfl (fun x _ => hsome x), Finset.sum_congr rfl (fun i _ => hsome_input i),
      ← guestNet_eq_sum_inst]
    linear_combination hbal m hm
  -- Both counts are below `p`, so it is an equation between naturals.
  have hcard : ∀ f : BridgeArc gA n → BusMessage p,
      ((Finset.univ.filter fun e => f e = m).card : ZMod p)
        = ∑ e : BridgeArc gA n, (if f e = m then (1 : ZMod p) else 0) := by
    intro f
    rw [Finset.card_filter]
    push_cast
    simp
  have hbound : ∀ f : BridgeArc gA n → BusMessage p,
      (Finset.univ.filter fun e => f e = m).card < p := by
    intro f
    refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
    rw [Finset.card_univ, card_bridgeArc]
    calc (∑ s : Fin G.length, (gA s).length) + n + 1 ≤ maxInstances + maxInputInstances + 1 := by
          omega
      _ ≤ (maxInstances + maxInputInstances + 1) * (maxWindow + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
      _ < p := hp
  have heq : ((Finset.univ.filter fun e => bridgeSrc gA S iR r e = m).card : ZMod p)
      = ((Finset.univ.filter fun e => bridgeDst gA S iR r e = m).card : ZMod p) := by
    rw [hcard, hcard, Finset.sum_sub_distrib] at *
    exact (sub_eq_zero.mp hsplit).symm
  have h1 := ZMod.val_cast_of_lt (hbound (bridgeSrc gA S iR r))
  rw [heq, ZMod.val_cast_of_lt (hbound (bridgeDst gA S iR r))] at h1
  exact h1.symm

theorem bridge_advPos : ∀ e : BridgeArc gA n, e ≠ none → 0 < bridgeAdv gA S iR e := by
  intro e h
  cases e with
  | none => exact absurd rfl h
  | some e' =>
    cases e' with
    | inl x => exact (S x).dPos
    | inr i => exact (iR i).dPos

theorem bridge_advTime : ∀ e : BridgeArc gA n, e ≠ none →
    openVmBridgeTimestamp (bridgeDst gA S iR r e)
      = openVmBridgeTimestamp (bridgeSrc gA S iR r e) + ((bridgeAdv gA S iR e : ℕ) : ZMod p) := by
  intro e h
  cases e with
  | none => exact absurd rfl h
  | some e' =>
    cases e' with
    | inl x => rfl
    | inr i => rfl

/-- The run advances the clock by at most one maxWindow per instance, guest or input-chip. -/
theorem bridge_total_le {maxInstances maxInputInstances : ℕ}
    (hIlt : ∀ i : Fin n, (iR i).d < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances) :
    (∑ e : BridgeArc gA n, bridgeAdv gA S iR e) ≤ (maxInstances + maxInputInstances) * maxWindow := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  have hnone : bridgeAdv gA S iR none = 0 := rfl
  have hsome : ∑ x : ((s : Fin G.length) × Fin (gA s).length), bridgeAdv gA S iR (some (.inl x))
      ≤ (∑ s : Fin G.length, (gA s).length) * maxWindow := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ maxWindow (fun x _ => le_of_lt (S x).dLt)) ?_
    rw [smul_eq_mul, Finset.card_univ, Fintype.card_sigma]
    simp
  have hinput : ∑ i : Fin n, bridgeAdv gA S iR (some (.inr i)) ≤ n * maxWindow := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ maxWindow (fun i _ => le_of_lt (hIlt i))) ?_
    rw [smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  calc bridgeAdv gA S iR none
        + (∑ x : ((s : Fin G.length) × Fin (gA s).length), bridgeAdv gA S iR (some (.inl x))
          + ∑ i : Fin n, bridgeAdv gA S iR (some (.inr i)))
      = (∑ x : ((s : Fin G.length) × Fin (gA s).length), bridgeAdv gA S iR (some (.inl x)))
          + ∑ i : Fin n, bridgeAdv gA S iR (some (.inr i)) := by rw [hnone]; ring
    _ ≤ (∑ s : Fin G.length, (gA s).length) * maxWindow + n * maxWindow :=
        Nat.add_le_add hsome hinput
    _ ≤ maxInstances * maxWindow + maxInputInstances * maxWindow :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hcount) (Nat.mul_le_mul_right _ hcountI)
    _ = (maxInstances + maxInputInstances) * maxWindow := by ring

theorem bridge_totalLt {maxInstances maxInputInstances : ℕ}
    (hIlt : ∀ i : Fin n, (iR i).d < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    (∑ e : BridgeArc gA n, bridgeAdv gA S iR e) < p := by
  have hring : (maxInstances + maxInputInstances + 1) * (maxWindow + 1)
      = (maxInstances + maxInputInstances) * maxWindow
        + (maxInstances + maxInputInstances + maxWindow + 1) := by ring
  refine lt_of_le_of_lt (bridge_total_le gA S iR hIlt hcount hcountI)
    (lt_of_lt_of_le ?_ (le_of_lt hp))
  rw [hring]
  exact Nat.lt_add_of_pos_right (by omega)

/-- **A run's execution bridge, read as a `VmChain.Chain`.** -/
def bridgeChain {maxInstances maxInputInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg countReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : ∀ i : Fin n, (iR i).d < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    VmChain.Chain p (BridgeArc gA n) (BusMessage p) where
  src := bridgeSrc gA S iR r
  dst := bridgeDst gA S iR r
  time := openVmBridgeTimestamp
  conn := none
  adv := bridgeAdv gA S iR
  balanced := bridge_balanced gA S iR ptrReg countReg r hbal hcount hcountI hp
  advPos := bridge_advPos gA S iR
  advTime := bridge_advTime gA S iR r
  advConn := rfl
  totalLt := bridge_totalLt gA S iR hIlt hcount hcountI hp

/-- **Every instance starts at an honest natural timestamp, and finishes below the connector's.**
    The connector's final timestamp is the one OpenVM range-checks
    (`ConnectorBoundary.finalTimestampBounded`), so this is what carries that single check to every
    instruction in the run. -/
theorem bridge_chain_bound {maxInstances maxInputInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg countReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : ∀ i : Fin n, (iR i).d < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p)
    (x : (s : Fin G.length) × Fin (gA s).length) :
    ∃ T : ℕ, (S x).base = ((1 + T : ℕ) : ZMod p) ∧
      1 + T + (S x).d ≤ r.finalTimestamp.val := by
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, (∑ e : BridgeArc gA n, bridgeAdv gA S iR e) = N := ⟨_, rfl⟩
  have htot : N ≤ (maxInstances + maxInputInstances) * maxWindow :=
    hN ▸ bridge_total_le gA S iR hIlt hcount hcountI
  have h1N : 1 + N < p := by
    have hp' := hp
    rw [show (maxInstances + maxInputInstances + 1) * (maxWindow + 1)
      = (maxInstances + maxInputInstances) * maxWindow
        + (maxInstances + maxInputInstances + maxWindow + 1) from by ring] at hp'
    obtain ⟨M, hM⟩ : ∃ M, (maxInstances + maxInputInstances) * maxWindow = M := ⟨_, rfl⟩
    rw [hM] at hp' htot
    omega
  obtain ⟨T, hT1, hT2⟩ :=
    (bridgeChain gA S iR ptrReg countReg r hbal hIlt hcount hcountI hp).arc_position
      (some (.inl x)) (Option.some_ne_none _)
  have hT1' : T + (S x).d ≤ ∑ e : BridgeArc gA n, bridgeAdv gA S iR e := hT1
  rw [hN] at hT1'
  have hT2' : (S x).base = 1 + (T : ZMod p) := hT2
  have hconn : r.finalTimestamp = 1 + ((N : ℕ) : ZMod p) := by
    have h' : r.finalTimestamp = 1 + ((∑ e : BridgeArc gA n, bridgeAdv gA S iR e : ℕ) : ZMod p) :=
      (bridgeChain gA S iR ptrReg countReg r hbal hIlt hcount hcountI hp).time_conn
    rwa [hN] at h'
  have hcast : (1 : ZMod p) + ((N : ℕ) : ZMod p) = ((1 + N : ℕ) : ZMod p) := by push_cast; ring
  have hval : r.finalTimestamp.val = 1 + N := by
    rw [hconn, hcast, ZMod.val_cast_of_lt h1N]
  refine ⟨T, ?_, by omega⟩
  rw [hT2']
  push_cast
  ring

end Bridge

--------- The rank window ---------

/-- **`openVmHost` keeps its runs inside the rank window** — with no hypotheses left.

    The last undischarged assumption of the VM-level soundness theorem. The arithmetic it needs is
    `OpenVmParams.windowOk`, already discharged when `P` was built: `P.maxInstances` instances
    advancing the clock by less than `P.maxWindow` each cannot wrap `ZMod p`. Everything else
    comes from the VM — `Circuit.advancesClock`, required of every legal guest, and the
    connector's range-checked final timestamp. -/
theorem openVmHost_pinsRanks (P : OpenVmParams p) :
    (openVmHost P).pinsRanks
      (openVmRankModel openVmMemBusId) := by
  classical
  have hp := P.windowOk
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  intro G hGuests a hsat t asg hasg bi hbi hmult
  show openVmRank openVmMemBusId ((bi.eval asg).busId, (bi.eval asg).payload) < openVmRankBound
  by_cases hbus : bi.busId = 1
  swap
  · have hne : ¬ ((bi.eval asg).busId, (bi.eval asg).payload).1 = 1 := hbus
    simp only [openVmRank, hne, if_false]
    exact Nat.two_pow_pos _
  -- The instance we are bounding, as an index into the assignment.
  obtain ⟨j, rfl⟩ := List.get_of_mem hasg
  -- A clock witness for every instance, chosen once.
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 P.maxWindow) :=
    fun x => clockStep_nonempty
      (openVmHost_advancesClock_unpack P _
        (hGuests _ (List.get_mem G x.1)))
      (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
  have S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 P.maxWindow :=
    fun x => Classical.choice (hNonempty x)
  -- The connector, the input-chip instances' own witnesses, and the bridge's balance equation.
  obtain ⟨r, iR, hiRlt, -, -, hrnet⟩ :=
    openVmHost_bridge_isolated P hsat.satisfiesHost
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m +
        (∑ i, busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rw [busEffect_apply, hrnet m hm] at hb
    linear_combination hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ P.maxInstances :=
    hsat.withinBudget
  have hcountI : (a.hostAssignment (openVmHost P).inputChip).length ≤ P.maxInputInstances :=
    hsat.satisfiesHost.withinBound (openVmHost P).inputChip
  obtain ⟨T, hbase, hfit⟩ :=
    bridge_chain_bound a.guestAssignments S iR P.ptrReg P.countReg r hbal hiRlt hcount hcountI hp
      ⟨t, j⟩
  -- The memory access sits strictly inside this instruction's own step.
  obtain ⟨δ, hδpos, hδlt, hδeq⟩ := (S ⟨t, j⟩).mem bi hbi hbus hmult
  have hlt : 1 + T + δ < p := by
    have := ZMod.val_lt r.finalTimestamp
    omega
  set asg := (a.guestAssignments t).get j with hasgdef
  have hts : openVmMemTimestamp ((bi.eval asg).busId, (bi.eval asg).payload)
      = ((1 + T + δ : ℕ) : ZMod p) := by
    rw [hδeq, hbase]
    push_cast
    ring
  have hrank : openVmRank openVmMemBusId ((bi.eval asg).busId, (bi.eval asg).payload)
      = (openVmMemTimestamp ((bi.eval asg).busId, (bi.eval asg).payload)).val := by
    simp only [openVmRank, openVmMemTimestamp]
    rw [if_pos (show ((bi.eval asg).busId, (bi.eval asg).payload).1 = 1 from hbus)]
  rw [hrank, hts, ZMod.val_cast_of_lt hlt]
  have := r.finalTimestampBounded
  omega

/-- **`openVmHost`'s input-chip instances run at pairwise distinct times.** Closes `A2`'s residual
    gap (`agent-docs/vm-spec-audit.md`): nothing previously forced two input-chip instances to
    distinct timestamps, so a `VmAssignment.orderedInputInstances` tie could still swap which
    chunk is read first. Now that the input chip shares the execution bridge with every guest
    instruction (`InputRead.pcFrom`/`pcTo`/`d`), two different realized instances are two
    different non-connector arcs of the very same `VmChain.Chain` — and `Chain.time_injOn`
    already rules out two different arcs sharing a clock reading. -/
theorem openVmHost_inputTime_injOn (P : OpenVmParams p)
    {G : Guest p} (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a) :
    Set.InjOn (fun i => (openVmHost P).getInputTime
        ((a.hostAssignment (openVmHost P).inputChip).get i))
      (Set.univ : Set (Fin (a.hostAssignment (openVmHost P).inputChip).length)) := by
  classical
  have hp := P.windowOk
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 P.maxWindow) :=
    fun x => clockStep_nonempty
      (openVmHost_advancesClock_unpack P _
        (hGuests _ (List.get_mem G x.1)))
      (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
  have S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 P.maxWindow :=
    fun x => Classical.choice (hNonempty x)
  obtain ⟨r, iR, hiRlt, -, hiRtime, hrnet⟩ :=
    openVmHost_bridge_isolated P hsat.satisfiesHost
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m +
        (∑ i, busStateOf ((iR i).interactions P.ptrReg P.countReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rw [busEffect_apply, hrnet m hm] at hb
    linear_combination hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ P.maxInstances :=
    hsat.withinBudget
  have hcountI : (a.hostAssignment (openVmHost P).inputChip).length ≤ P.maxInputInstances :=
    hsat.satisfiesHost.withinBound (openVmHost P).inputChip
  set C := bridgeChain a.guestAssignments S iR P.ptrReg P.countReg r hbal hiRlt hcount hcountI hp
    with hCdef
  rintro i1 - i2 - heq
  have hne_conn1 : (some (.inr i1) : BridgeArc a.guestAssignments _) ≠ C.conn :=
    Option.some_ne_none _
  have hne_conn2 : (some (.inr i2) : BridgeArc a.guestAssignments _) ≠ C.conn :=
    Option.some_ne_none _
  have htime : C.time (C.src (some (.inr i1))) = C.time (C.src (some (.inr i2))) := by
    show (iR i1).base = (iR i2).base
    rw [← hiRtime i1, ← hiRtime i2]
    exact heq
  have hres := C.time_injOn hne_conn1 hne_conn2 htime
  simpa using hres

end ApcOptimizer.OpenVM
