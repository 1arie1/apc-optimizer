import ApcOptimizer.Implementation.InterfaceEncoding.Transfer
import ApcOptimizer.Sp1Semantics

set_option autoImplicit false

/-! Proof machinery for the removal-tolerant (internal-pairs) layer of
`ApcOptimizer/InterfaceEncoding.lean`. Not part of the audited surface.

Everything here rests on one observation: `flipMult` is an involution that preserves the bus,
the payload and hence the address projection, and negates the multiplicity — so it fixes the
`Circuit.sideEffects` key of a message, and *swaps* `sendsAt` with `recvsAt`. -/

namespace ApcOptimizer.Interface

variable {p : ℕ}

/-! ## `flipMult` -/

/-- The bus, the payload, and hence the address projection are `rfl`-preserved; only the
    multiplicity moves. -/
@[simp] theorem flipMult_multiplicity (m : BusInteraction (ZMod p)) :
    (flipMult m).multiplicity = -m.multiplicity := rfl

/-! ## Side effects: internally-balanced traffic nets to zero on every key -/

theorem netMult_append (L L' : List (BusInteraction (ZMod p))) (key : BusMessage p) :
    netMult (L ++ L') key = netMult L key + netMult L' key := by
  unfold netMult
  rw [List.filter_append, List.map_append, List.sum_append]

theorem netMult_map_flipMult (S : List (BusInteraction (ZMod p))) (key : BusMessage p) :
    netMult (S.map flipMult) key = -netMult S key := by
  unfold netMult
  induction S with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons]
    -- `flipMult` fixes the key, so the two filters agree on the head by `rfl`
    by_cases hk : (hd.busId, hd.payload) = key
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hk),
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hk),
        List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, flipMult_multiplicity,
        neg_add]
    · rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact hk),
        List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact hk), ih]

theorem netMult_eq_zero_of_internallyBalanced {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) (key : BusMessage p) : netMult D key = 0 := by
  obtain ⟨S, hS⟩ := h
  rw [netMult_perm hS key, netMult_append, netMult_map_flipMult, add_neg_cancel]

/-- Dropping internal pairs leaves the side effects untouched: they record the *net*
    multiplicity per tuple, and a cancelling pair nets to zero on the one key it touches. -/
theorem sideEffects_eq_of_interfaceMatchUpTo {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatchUpTo bs A B a b) :
    A.sideEffects bs a = B.sideEffects bs b := by
  obtain ⟨D, hD, hperm⟩ := h
  funext key
  rw [sideEffects_eq_netMult, sideEffects_eq_netMult, netMult_perm hperm key, netMult_append,
    netMult_eq_zero_of_internallyBalanced hD, add_zero]

/-! ## The memory discipline: internally-balanced traffic has equal send and receive payloads -/

theorem recvsAt_add (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M N : Multiset (BusInteraction (ZMod p))) :
    recvsAt shape addr (M + N) = recvsAt shape addr M + recvsAt shape addr N :=
  Multiset.filter_add _ _ _

theorem sendsAt_add (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M N : Multiset (BusInteraction (ZMod p))) :
    sendsAt shape addr (M + N) = sendsAt shape addr M + sendsAt shape addr N :=
  Multiset.filter_add _ _ _

/-- `flipMult` carries the sends onto the receives: it preserves the address and negates the
    multiplicity, which is exactly the difference between the two filters. -/
theorem recvsAt_map_flipMult (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (X : Multiset (BusInteraction (ZMod p))) :
    recvsAt shape addr (X.map flipMult) = (sendsAt shape addr X).map flipMult := by
  unfold recvsAt sendsAt
  refine Multiset.induction_on X (by simp) fun m X ih => ?_
  rw [Multiset.map_cons, Multiset.filter_cons, Multiset.filter_cons, Multiset.map_add, ih]
  congr 1
  have hiff : ((flipMult m).multiplicity = -shape.setNewMult ∧
      shape.address (flipMult m) = addr)
      ↔ (m.multiplicity = shape.setNewMult ∧ shape.address m = addr) :=
    ⟨fun h => ⟨neg_inj.mp h.1, h.2⟩, fun h => ⟨by rw [flipMult_multiplicity, h.1], h.2⟩⟩
  by_cases hs : m.multiplicity = shape.setNewMult ∧ shape.address m = addr
  · rw [if_pos (hiff.mpr hs), if_pos hs, Multiset.map_singleton]
  · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs, Multiset.map_zero]

/-- The mirror image of `recvsAt_map_flipMult`. -/
theorem sendsAt_map_flipMult (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (X : Multiset (BusInteraction (ZMod p))) :
    sendsAt shape addr (X.map flipMult) = (recvsAt shape addr X).map flipMult := by
  unfold recvsAt sendsAt
  refine Multiset.induction_on X (by simp) fun m X ih => ?_
  rw [Multiset.map_cons, Multiset.filter_cons, Multiset.filter_cons, Multiset.map_add, ih]
  congr 1
  have hiff : ((flipMult m).multiplicity = shape.setNewMult ∧
      shape.address (flipMult m) = addr)
      ↔ (m.multiplicity = -shape.setNewMult ∧ shape.address m = addr) :=
    ⟨fun h => ⟨by rw [← neg_neg m.multiplicity, ← flipMult_multiplicity, h.1], h.2⟩,
      fun h => ⟨by rw [flipMult_multiplicity, h.1, neg_neg], h.2⟩⟩
  by_cases hr : m.multiplicity = -shape.setNewMult ∧ shape.address m = addr
  · rw [if_pos (hiff.mpr hr), if_pos hr, Multiset.map_singleton]
  · rw [if_neg (fun h => hr (hiff.mp h)), if_neg hr, Multiset.map_zero]

/-- The heart of the layer: on internally-balanced traffic the receives and the sends carry
    the same payloads, whichever side of a cancelling pair the shape's polarity calls a send.
    Each pair contributes its payload once to each side. -/
theorem recvsAt_payload_eq_sendsAt_payload_of_internallyBalanced (shape : MemoryBusShape)
    (addr : List (Option (ZMod p))) {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) :
    (recvsAt shape addr ↑D).map BusInteraction.payload
      = (sendsAt shape addr ↑D).map BusInteraction.payload := by
  obtain ⟨S, hS⟩ := h
  have hcoe : (↑(S ++ S.map flipMult) : Multiset (BusInteraction (ZMod p)))
      = ↑S + (↑S : Multiset (BusInteraction (ZMod p))).map flipMult := by
    rw [Multiset.map_coe, ← Multiset.coe_add]
  rw [Multiset.coe_eq_coe.mpr hS, hcoe, recvsAt_add, sendsAt_add, recvsAt_map_flipMult,
    sendsAt_map_flipMult, Multiset.map_add, Multiset.map_add, Multiset.map_map,
    Multiset.map_map]
  simp only [Function.comp_def]
  exact add_comm _ _

theorem multiset_add_sub_add_right {α : Type _} [DecidableEq α] (a b c : Multiset α) :
    a + c - (b + c) = a - b := by
  ext x
  simp only [Multiset.count_sub, Multiset.count_add]
  omega

/-- Internally-balanced traffic leaves the per-address excess exactly as it was: it adds the
    same payload multiset to the receives and to the sends, and the excess is their truncated
    difference. -/
theorem excessAt_add_of_internallyBalanced (shape : MemoryBusShape)
    (addr : List (Option (ZMod p))) (M : Multiset (BusInteraction (ZMod p)))
    {D : List (BusInteraction (ZMod p))} (h : InternallyBalanced D) :
    excessAt shape addr (M + (↑D : Multiset (BusInteraction (ZMod p))))
      = excessAt shape addr M := by
  unfold excessAt
  rw [recvsAt_add, sendsAt_add, Multiset.map_add, Multiset.map_add,
    recvsAt_payload_eq_sendsAt_payload_of_internallyBalanced shape addr h,
    multiset_add_sub_add_right]

theorem admissibleMemoryBusM_add_iff {shape : MemoryBusShape}
    {M : Multiset (BusInteraction (ZMod p))} {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) :
    admissibleMemoryBusM shape (M + (↑D : Multiset (BusInteraction (ZMod p))))
      ↔ admissibleMemoryBusM shape M := by
  unfold admissibleMemoryBusM
  exact forall_congr' fun addr => by
    rw [excessAt_add_of_internallyBalanced shape addr M h]

theorem entryKeyed_add_iff {shape : MemoryBusShape} {slot : Nat} {key : ZMod p}
    {M : Multiset (BusInteraction (ZMod p))} {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) :
    entryKeyed shape slot key (M + (↑D : Multiset (BusInteraction (ZMod p))))
      ↔ entryKeyed shape slot key M := by
  unfold entryKeyed
  exact forall_congr' fun addr => forall_congr' fun P => by
    rw [excessAt_add_of_internallyBalanced shape addr M h]

/-! ## Closure: no environment can see internal pairs -/

/-- The semantic counterpart of `excessAt_add_of_internallyBalanced`, and a full `↔` where the
    rely gets only one direction: a cancelling pair adds the same payload to both sides of the
    closure equation, which cancels. -/
theorem closes_add_iff {shape : MemoryBusShape} {E : MemEnv p}
    {M : Multiset (BusInteraction (ZMod p))} {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) :
    Closes shape E (M + (↑D : Multiset (BusInteraction (ZMod p)))) ↔ Closes shape E M := by
  unfold Closes
  refine forall_congr' fun addr => ?_
  rw [recvsAt_add, sendsAt_add, Multiset.map_add, Multiset.map_add,
    recvsAt_payload_eq_sendsAt_payload_of_internallyBalanced shape addr h]
  set c := (sendsAt shape addr ↑D).map BusInteraction.payload
  set R := (recvsAt shape addr M).map BusInteraction.payload
  set S := (sendsAt shape addr M).map BusInteraction.payload
  constructor
  · intro heq
    have : R + E.exitMS addr + c = S + E.entryMS addr + c := by
      rw [add_right_comm R, add_right_comm S]; exact heq
    exact add_right_cancel this
  · intro heq
    rw [add_right_comm R, add_right_comm S, heq]

/-! ## Stability of the balance under filtering -/

theorem filter_map_flipMult (q : BusInteraction (ZMod p) → Bool)
    (hq : ∀ m, q (flipMult m) = q m) (S : List (BusInteraction (ZMod p))) :
    (S.map flipMult).filter q = (S.filter q).map flipMult := by
  induction S with
  | nil => simp
  | cons m S ih =>
    rw [List.map_cons]
    by_cases hqm : q m
    · rw [List.filter_cons_of_pos (by rw [hq]; exact hqm), List.filter_cons_of_pos hqm,
        List.map_cons, ih]
    · rw [List.filter_cons_of_neg (by rw [hq]; simpa using hqm),
        List.filter_cons_of_neg (by simpa using hqm), ih]

/-- Selecting a bus keeps a cancelling collection cancelling: `flipMult` preserves the bus. -/
theorem InternallyBalanced.filter {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) (q : BusInteraction (ZMod p) → Bool)
    (hq : ∀ m, q (flipMult m) = q m) : InternallyBalanced (D.filter q) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S.filter q, ?_⟩
  have hsplit : (S ++ S.map flipMult).filter q = S.filter q ++ (S.filter q).map flipMult := by
    rw [List.filter_append, filter_map_flipMult q hq]
  rw [← hsplit]
  exact hS.filter q

/-- Per bus, the traffic of the two runs differs by the cancelling traffic restricted to that
    bus — which is still cancelling. -/
theorem busTraffic_add_of_interfaceMatchUpTo {bs : BusSemantics p} {A B : Circuit p}
    {a b : Variable → ZMod p} (h : InterfaceMatchUpTo bs A B a b) (busId : Nat) :
    ∃ D : List (BusInteraction (ZMod p)), InternallyBalanced D ∧
      busTraffic A bs busId a = busTraffic B bs busId b + ↑D := by
  obtain ⟨D, hD, hperm⟩ := h
  refine ⟨D.filter (fun m => m.busId = busId), hD.filter _ fun _ => rfl, ?_⟩
  unfold busTraffic
  rw [Multiset.coe_eq_coe.mpr (hperm.filter _), List.filter_append, Multiset.coe_add]

/-! ## The VM relies survive the removal -/

/-- Selecting one bus is `flipMult`-blind, so it keeps a cancelling collection cancelling. -/
theorem internallyBalanced_filter_busId {D : List (BusInteraction (ZMod p))}
    (h : InternallyBalanced D) (busId : Nat) :
    InternallyBalanced (D.filter (fun m => m.busId = busId)) :=
  h.filter _ fun _ => rfl

/-- A per-bus multiset rely holds of `L` once it holds of `L ++ D`: the coercion splits and
    the cancelling traffic is invisible to the per-address excess. -/
theorem coe_filter_append (L D : List (BusInteraction (ZMod p))) (busId : Nat) :
    (↑((L ++ D).filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p)))
      = ↑(L.filter (fun m => m.busId = busId))
        + ↑(D.filter (fun m => m.busId = busId)) := by
  rw [List.filter_append, Multiset.coe_add]

theorem openVmAdmissible_drop (busMap : OpenVM.BusMap) (entryPc : Option (ZMod p)) :
    AdmissibleDropInvariant (OpenVM.openVmBusSemantics p busMap entryPc) := by
  intro L D hD h
  obtain ⟨hmem, hts, hkey, hx0⟩ := h
  refine ⟨fun busId shape hshape => ?_, fun busId tsField hf => ?_,
    fun busId slot key shape hshape hkeyof => ?_, fun m hm => hx0 m (List.mem_append_left _ hm)⟩
  · exact (admissibleMemoryBusM_add_iff (internallyBalanced_filter_busId hD busId)).mp
      (coe_filter_append L D busId ▸ hmem busId shape hshape)
  · exact fun m hm => hts busId tsField hf m
      (by rw [List.filter_append]; exact List.mem_append_left _ hm)
  · exact (entryKeyed_add_iff (internallyBalanced_filter_busId hD busId)).mp
      (coe_filter_append L D busId ▸ hkey busId slot key shape hshape hkeyof)

theorem sp1Admissible_drop (busMap : SP1.BusMap) :
    AdmissibleDropInvariant (SP1.sp1BusSemantics p busMap) := by
  intro L D hD h
  obtain ⟨hmem, hx0⟩ := h
  refine ⟨fun busId shape hshape => ?_, fun m hm => hx0 m (List.mem_append_left _ hm)⟩
  exact (admissibleMemoryBusM_add_iff (internallyBalanced_filter_busId hD busId)).mp
    (coe_filter_append L D busId ▸ hmem busId shape hshape)

end ApcOptimizer.Interface
