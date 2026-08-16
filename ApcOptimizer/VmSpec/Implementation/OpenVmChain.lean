import ApcOptimizer.VmSpec.Implementation.Chain
import ApcOptimizer.VmSpec.Implementation.OpenVmConnection

set_option autoImplicit false

/-! **`Host.pinsRanks` for `openVmHost`**: every timestamp in a satisfying run is inside OpenVM's
    rank window. Nothing here is audited.

    The run's execution-bridge traffic is read as a `VmChain.Chain` (`Chain.lean`): one arc per
    realized guest instance, consuming the `(pc, t)` it receives and producing the `(pc', t + d)`
    it sends — `Circuit.advancesClock`, which `openVmHost.legalGuest` requires — plus one arc for
    the connector, which produces `(pc₀, 1)` and consumes the segment's final state. Bus balance
    on bus `0` is exactly the chain's `balanced` field, once the multiplicities are counted as
    naturals rather than field elements.

    The chain then places every instance at a known distance before the connector, so its start
    timestamp is `1 + T` for an honest natural `T` and the whole instruction fits below the final
    timestamp — which `ConnectorBoundary.finalTimestampBounded` range-checks. Every memory access
    of the instance sits strictly inside its own step (`Circuit.advancesClock` again), so it
    inherits the bound.

    The one arithmetic premise is `(maxInstances + 1) * (maxWindow + 1) < p`: a run too long to fit
    in the field could wrap, and then "the timestamp went up" would stop meaning anything. -/

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

theorem clockStep_nonempty {c : Circuit p} {asg : ChipAssignment p}
    {execBusId memBusId maxWindow : ℕ}
    (h : Circuit.advancesClock c execBusId memBusId maxWindow) (hsat : c.satisfiesAlgebraic asg) :
    Nonempty (ClockStep p c asg execBusId memBusId maxWindow) := by
  obtain ⟨pcFrom, pcTo, base, d, h1, h2, h3, h4, h5, h6⟩ := h asg hsat
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

/-- **Only the connector touches the execution bridge.** The four lookup chips pin their bus id to
    a lookup bus and the four memory-bus chips to memory, so on bus `0` the host's whole net is the
    connector's — and the connector is a singleton, so there is exactly one witness to name. -/
theorem openVmHost_bridge_isolated (maxInstances ptrReg countReg maxWindow : ℕ)
    {hA : HostAssignment p (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1)}
    (hlegal : hA.satisfies) :
    ∃ r : ConnectorBoundary p, ∀ m : BusMessage p, m.1 = 0 →
      hA.busEffect m = busStateOf (r.interactions 0) m := by
  classical
  -- The connector's single instance.
  have hconnIdx : (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).chips.length = 9 :=
    rfl
  set k : Fin (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).chips.length :=
    ⟨8, by rw [hconnIdx]; omega⟩ with hk
  have hlen : (hA k).length = 1 := hlegal.2 _ trivial
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  have hcan := hlegal.1 k c (by rw [hc]; exact List.mem_singleton_self c)
  obtain ⟨r, hr⟩ : (connectorHostChip (p := p) 0).canProduce c := hcan
  refine ⟨r, fun m hm => ?_⟩
  -- Every other chip leaves bus `0` alone.
  have hzero :
      ∀ t : Fin (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).chips.length,
      (t : ℕ) ≠ 8 → ∀ c' ∈ hA t, c' m = 0 := by
    intro t ht c' hc'
    have hleg := hlegal.1 t c' hc'
    by_contra hne
    fin_cases t
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · obtain ⟨r', hr'⟩ := hleg
      rw [hr'] at hne
      obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hne
      exact absurd ((congrArg Prod.fst heq).symm.trans
        (OutputRead.interactions_busId r' 1 msg hmsg)) (by rw [hm]; omega)
    · obtain ⟨r', hr'⟩ := hleg
      rw [hr'] at hne
      obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hne
      exact absurd ((congrArg Prod.fst heq).symm.trans
        (InputRead.interactions_busId r' ptrReg countReg 1 msg hmsg)) (by rw [hm]; omega)
    · exact absurd rfl ht
  have hz : ∀ t : Fin (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).chips.length,
      (t : ℕ) ≠ 8 → ((hA t).map (fun effect => effect m)).sum = 0 := by
    intro t ht
    refine List.sum_eq_zero (fun v hv => ?_)
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hv
    exact hzero t ht c' hc'
  have hnet : hA.busEffect m
      = ∑ t : Fin (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).chips.length,
        ((hA t).map (fun effect => effect m)).sum := rfl
  rw [hnet, Finset.sum_eq_single k (fun t _ ht => hz t (fun h => ht (Fin.ext h)))
    (fun h => absurd (Finset.mem_univ k) h), hc, hr]
  simp

--------- The bridge as a chain ---------

section Bridge

variable {G : Guest p} {maxWindow : ℕ}

/-- The arcs of a run's execution bridge: one per realized guest instance, plus the connector
    (`none`). -/
abbrev BridgeArc (gA : GuestAssignment p G) : Type :=
  Option ((s : Fin G.length) × Fin (gA s).length)

variable (gA : GuestAssignment p G)
  (S : ∀ x : ((s : Fin G.length) × Fin (gA s).length),
      ClockStep p (G.get x.1) ((gA x.1).get x.2) 0 1 maxWindow)
  (r : ConnectorBoundary p)

/-- The bridge state an arc consumes: an instruction's incoming `(pc, t)`, or, for the connector,
    the segment's final state. -/
def bridgeSrc : BridgeArc gA → BusMessage p
  | none => (0, [r.finalPc, r.finalTimestamp])
  | some x => (0, [(S x).pcFrom, (S x).base])

/-- The bridge state an arc produces: an instruction's outgoing `(pc, t + d)`, or, for the
    connector, the segment's initial state at timestamp `1`. -/
def bridgeDst : BridgeArc gA → BusMessage p
  | none => (0, [r.initialPc, 1])
  | some x => (0, [(S x).pcTo, (S x).base + ((S x).d : ZMod p)])

/-- How far an arc advances the clock; the connector does not. -/
def bridgeAdv : BridgeArc gA → ℕ
  | none => 0
  | some x => (S x).d

theorem bridgeSrc_busId (e : BridgeArc gA) : (bridgeSrc gA S r e).1 = 0 := by cases e <;> rfl

theorem bridgeDst_busId (e : BridgeArc gA) : (bridgeDst gA S r e).1 = 0 := by cases e <;> rfl

/-- The arcs are the instances plus one. -/
theorem card_bridgeArc : Fintype.card (BridgeArc gA) = (∑ s : Fin G.length, (gA s).length) + 1 := by
  rw [Fintype.card_option, Fintype.card_sigma]
  simp

/-- A run with at least one instance is long enough that `p` cannot be tiny — which is all the
    case analysis below needs of it. -/
theorem bridge_p_large {maxInstances : ℕ}
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p) (hw : 2 ≤ maxWindow)
    (x : (s : Fin G.length) × Fin (gA s).length) : 6 < p := by
  have h1 : 1 ≤ maxInstances := by
    refine le_trans (le_trans x.2.pos ?_) hcount
    exact Finset.single_le_sum (f := fun s => (gA s).length) (fun s _ => Nat.zero_le _)
      (Finset.mem_univ x.1)
  calc 6 = (1 + 1) * (2 + 1) := by norm_num
    _ ≤ (maxInstances + 1) * (maxWindow + 1) := Nat.mul_le_mul (by omega) (by omega)
    _ < p := hp

/-- An instruction never consumes and produces the same bridge state: it would have to net both
    `-1` and `1` there. -/
theorem bridge_src_ne_dst (hp6 : 6 < p) (x : (s : Fin G.length) × Fin (gA s).length) :
    bridgeSrc gA S r (some x) ≠ bridgeDst gA S r (some x) := by
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
theorem bridge_balanced {maxInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 → gA.busEffect m + busStateOf (r.interactions 0) m = 0)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p) (m : BusMessage p) :
    (Finset.univ.filter fun e => bridgeSrc gA S r e = m).card
      = (Finset.univ.filter fun e => bridgeDst gA S r e = m).card := by
  classical
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  by_cases hm : m.1 = 0
  swap
  · have h1 : (Finset.univ.filter fun e => bridgeSrc gA S r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeSrc_busId gA S r e
    have h2 : (Finset.univ.filter fun e => bridgeDst gA S r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeDst_busId gA S r e
    rw [h1, h2]
  -- The field equation, arc by arc.
  have hsplit : ∑ e : BridgeArc gA,
      ((if bridgeDst gA S r e = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S r e = m then (1 : ZMod p) else 0)) = 0 := by
    have hsome : ∀ x, (if bridgeDst gA S r (some x) = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S r (some x) = m then (1 : ZMod p) else 0)
        = (G.get x.1).allEffects ((gA x.1).get x.2) m := by
      intro x
      have hp6 := bridge_p_large gA hcount hp (by have := (S x).dPos; have := (S x).dLt; omega) x
      have hne := bridge_src_ne_dst gA S r hp6 x
      by_cases hd : bridgeDst gA S r (some x) = m
      · have hs : bridgeSrc gA S r (some x) ≠ m := fun h => hne (h.trans hd.symm)
        rw [if_pos hd, if_neg hs, sub_zero, ← hd]
        exact ((S x).send).symm
      · by_cases hs : bridgeSrc gA S r (some x) = m
        · rw [if_neg hd, if_pos hs, zero_sub, ← hs]
          exact ((S x).recv).symm
        · rw [if_neg hd, if_neg hs, sub_zero]
          exact ((S x).other m hm (fun h => hs h.symm) (fun h => hd h.symm)).symm
    have hnone : (if bridgeDst gA S r none = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S r none = m then (1 : ZMod p) else 0)
        = busStateOf (r.interactions 0) m := (connector_busStateOf r m).symm
    rw [Fintype.sum_option, hnone, Finset.sum_congr rfl (fun x _ => hsome x),
      ← guestNet_eq_sum_inst, add_comm]
    exact hbal m hm
  -- Both counts are below `p`, so it is an equation between naturals.
  have hcard : ∀ f : BridgeArc gA → BusMessage p,
      ((Finset.univ.filter fun e => f e = m).card : ZMod p)
        = ∑ e : BridgeArc gA, (if f e = m then (1 : ZMod p) else 0) := by
    intro f
    rw [Finset.card_filter]
    push_cast
    simp
  have hbound : ∀ f : BridgeArc gA → BusMessage p,
      (Finset.univ.filter fun e => f e = m).card < p := by
    intro f
    refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
    rw [Finset.card_univ, card_bridgeArc]
    calc (∑ s : Fin G.length, (gA s).length) + 1 ≤ maxInstances + 1 := by omega
      _ ≤ (maxInstances + 1) * (maxWindow + 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ < p := hp
  have heq : ((Finset.univ.filter fun e => bridgeSrc gA S r e = m).card : ZMod p)
      = ((Finset.univ.filter fun e => bridgeDst gA S r e = m).card : ZMod p) := by
    rw [hcard, hcard, Finset.sum_sub_distrib] at *
    exact (sub_eq_zero.mp hsplit).symm
  have h1 := ZMod.val_cast_of_lt (hbound (bridgeSrc gA S r))
  rw [heq, ZMod.val_cast_of_lt (hbound (bridgeDst gA S r))] at h1
  exact h1.symm

theorem bridge_advPos : ∀ e : BridgeArc gA, e ≠ none → 0 < bridgeAdv gA S e := by
  rintro (_ | x) h
  · exact absurd rfl h
  · exact (S x).dPos

theorem bridge_advTime : ∀ e : BridgeArc gA, e ≠ none →
    openVmBridgeTimestamp (bridgeDst gA S r e)
      = openVmBridgeTimestamp (bridgeSrc gA S r e) + ((bridgeAdv gA S e : ℕ) : ZMod p) := by
  rintro (_ | x) h
  · exact absurd rfl h
  · rfl

/-- The run advances the clock by at most one maxWindow per instance. -/
theorem bridge_total_le {maxInstances : ℕ}
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances) :
    (∑ e : BridgeArc gA, bridgeAdv gA S e) ≤ maxInstances * maxWindow := by
  rw [Fintype.sum_option]
  have hsome : ∑ x : ((s : Fin G.length) × Fin (gA s).length), bridgeAdv gA S (some x)
      ≤ (∑ s : Fin G.length, (gA s).length) * maxWindow := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ maxWindow (fun x _ => le_of_lt (S x).dLt)) ?_
    rw [smul_eq_mul, Finset.card_univ, Fintype.card_sigma]
    simp
  have : bridgeAdv gA S none = 0 := rfl
  rw [this, Nat.zero_add]
  exact le_trans hsome (Nat.mul_le_mul_right maxWindow hcount)

theorem bridge_totalLt {maxInstances : ℕ}
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p) :
    (∑ e : BridgeArc gA, bridgeAdv gA S e) < p := by
  have hring : (maxInstances + 1) * (maxWindow + 1)
      = maxInstances * maxWindow + (maxInstances + maxWindow + 1) := by ring
  refine lt_of_le_of_lt (bridge_total_le gA S hcount) (lt_of_lt_of_le ?_ (le_of_lt hp))
  rw [hring]
  exact Nat.lt_add_of_pos_right (by omega)

/-- **A run's execution bridge, read as a `VmChain.Chain`.** -/
def bridgeChain {maxInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 → gA.busEffect m + busStateOf (r.interactions 0) m = 0)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p) :
    VmChain.Chain p (BridgeArc gA) (BusMessage p) where
  src := bridgeSrc gA S r
  dst := bridgeDst gA S r
  time := openVmBridgeTimestamp
  conn := none
  adv := bridgeAdv gA S
  balanced := bridge_balanced gA S r hbal hcount hp
  advPos := bridge_advPos gA S
  advTime := bridge_advTime gA S r
  advConn := rfl
  totalLt := bridge_totalLt gA S hcount hp

/-- **Every instance starts at an honest natural timestamp, and finishes below the connector's.**
    The connector's final timestamp is the one OpenVM range-checks
    (`ConnectorBoundary.finalTimestampBounded`), so this is what carries that single check to every
    instruction in the run. -/
theorem bridge_chain_bound {maxInstances : ℕ}
    (hbal : ∀ m : BusMessage p, m.1 = 0 → gA.busEffect m + busStateOf (r.interactions 0) m = 0)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p)
    (x : (s : Fin G.length) × Fin (gA s).length) :
    ∃ T : ℕ, (S x).base = ((1 + T : ℕ) : ZMod p) ∧
      1 + T + (S x).d ≤ r.finalTimestamp.val := by
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, (∑ e : BridgeArc gA, bridgeAdv gA S e) = N := ⟨_, rfl⟩
  have htot : N ≤ maxInstances * maxWindow := hN ▸ bridge_total_le gA S hcount
  have h1N : 1 + N < p := by
    have hp' := hp
    rw [show (maxInstances + 1) * (maxWindow + 1)
      = maxInstances * maxWindow + (maxInstances + maxWindow + 1) from by ring] at hp'
    obtain ⟨M, hM⟩ : ∃ M, maxInstances * maxWindow = M := ⟨_, rfl⟩
    rw [hM] at hp' htot
    omega
  obtain ⟨T, hT1, hT2⟩ :=
    (bridgeChain gA S r hbal hcount hp).arc_position (some x) (Option.some_ne_none x)
  have hT1' : T + (S x).d ≤ ∑ e : BridgeArc gA, bridgeAdv gA S e := hT1
  rw [hN] at hT1'
  have hT2' : (S x).base = 1 + (T : ZMod p) := hT2
  have hconn : r.finalTimestamp = 1 + ((N : ℕ) : ZMod p) := by
    have h' : r.finalTimestamp = 1 + ((∑ e : BridgeArc gA, bridgeAdv gA S e : ℕ) : ZMod p) :=
      (bridgeChain gA S r hbal hcount hp).time_conn
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

/-- **`openVmHost` keeps its runs inside the rank window**, given that a run fits in the field.

    The last undischarged assumption of the VM-level soundness theorem. The one premise is
    arithmetic: `maxInstances` instances advancing the clock by less than `maxWindow` each cannot
    wrap `ZMod p`. Everything else comes from the VM — `Circuit.advancesClock`, required of every
    legal guest, and the connector's range-checked final timestamp. -/
theorem openVmHost_pinsRanks (maxInstances ptrReg countReg maxWindow : ℕ)
    (hp : (maxInstances + 1) * (maxWindow + 1) < p) :
    (openVmHost (p := p) maxInstances ptrReg countReg maxWindow 1).pinsRanks
      (openVmRankModel 1) := by
  classical
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  intro G L hGuests _hSize _hBudget a hsat t asg hasg bi hbi hmult
  show openVmRank 1 ((bi.eval asg).busId, (bi.eval asg).payload) < openVmRankBound
  by_cases hbus : bi.busId = 1
  swap
  · have hne : ¬ ((bi.eval asg).busId, (bi.eval asg).payload).1 = 1 := hbus
    simp only [openVmRank, hne, if_false]
    exact Nat.two_pow_pos _
  -- The instance we are bounding, as an index into the assignment.
  obtain ⟨j, rfl⟩ := List.get_of_mem hasg
  -- A clock witness for every instance, chosen once.
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 maxWindow) :=
    fun x => clockStep_nonempty
      (openVmHost_advancesClock_unpack maxInstances ptrReg countReg maxWindow _
        (hGuests _ (List.get_mem G x.1)))
      (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
  have S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      ClockStep p (G.get x.1) ((a.guestAssignments x.1).get x.2) 0 1 maxWindow :=
    fun x => Classical.choice (hNonempty x)
  -- The connector, and the bridge's balance equation.
  obtain ⟨r, hrnet⟩ :=
    openVmHost_bridge_isolated maxInstances ptrReg countReg maxWindow hsat.satisfiesHost
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rwa [busEffect_apply, hrnet m hm] at hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ maxInstances :=
    hsat.withinBudget
  obtain ⟨T, hbase, hfit⟩ :=
    bridge_chain_bound a.guestAssignments S r hbal hcount hp ⟨t, j⟩
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
  have hrank : openVmRank 1 ((bi.eval asg).busId, (bi.eval asg).payload)
      = (openVmMemTimestamp ((bi.eval asg).busId, (bi.eval asg).payload)).val := by
    simp only [openVmRank, openVmMemTimestamp]
    rw [if_pos (show ((bi.eval asg).busId, (bi.eval asg).payload).1 = 1 from hbus)]
  rw [hrank, hts, ZMod.val_cast_of_lt hlt]
  have := r.finalTimestampBounded
  omega

end ApcOptimizer.OpenVM
