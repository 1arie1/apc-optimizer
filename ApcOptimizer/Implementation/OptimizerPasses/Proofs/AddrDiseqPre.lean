import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqPre
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # The prepared certificate tests equal the originals

Each `*P` test of `AddrDiseqPre.lean`, applied to `denseAddrPrep`-prepared records, equals the
original certificate from `AddrDiseq.lean` / `BusPairCancelCheck.lean`; call sites rewrite their
scan hypotheses back through these. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The zipped prepared slot lists are the pairwise map over the shape's address fields. -/
theorem denseAddrPrep_slots_zip (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    ((denseAddrPrep shape T S).slots).zip ((denseAddrPrep shape T m).slots)
      = shape.addressFields.map (fun slot =>
          ((S.payload[slot]?).map (denseSlotPrep T), (m.payload[slot]?).map (denseSlotPrep T))) := by
  simp [denseAddrPrep, List.zip_map']

theorem denseSlotsAny_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseSlotPre p → DenseSlotPre p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseSlotPrep T e) (denseSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseSlotsAny f (fields.map (fun slot => (S.payload[slot]?).map (denseSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseSlotPrep T)))
        = fields.any (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.any_cons]
      rw [← denseSlotsAny_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseSlotPrep T e) (denseSlotPrep T e') || _) = (g e e' || _)
              rw [hfg]

theorem denseSlotsAll_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseSlotPre p → DenseSlotPre p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseSlotPrep T e) (denseSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseSlotsAll f (fields.map (fun slot => (S.payload[slot]?).map (denseSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseSlotPrep T)))
        = fields.all (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.all_cons]
      rw [← denseSlotsAll_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseSlotPrep T e) (denseSlotPrep T e') && _) = (g e e' && _)
              rw [hfg]

theorem denseAddrConstsNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrConstsNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrConstsNeq shape S m :=
  denseSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields

theorem denseAddrConstsEqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrConstsEqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrConstsEq shape S m :=
  denseSlotsAll_eq T S m _ _ (fun _ _ => rfl) shape.addressFields

theorem denseAddrAffineNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrAffineNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrAffineNeq shape S m :=
  denseSlotsAny_eq T S m _ _ (fun e e' => by
    unfold denseSlotPrep denseKeyDiffNZ
    cases denseLinearize e <;> cases denseLinearize e' <;> rfl) shape.addressFields

theorem denseAddrTwoRootNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrTwoRootNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrTwoRootNeq shape T S m :=
  denseSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields

theorem denseDiffSumP_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p)) :
    ∀ fs : List Nat,
      denseDiffSumP (fs.map (fun slot =>
          ((S.payload[slot]?).map (denseSlotPrep T), (m.payload[slot]?).map (denseSlotPrep T))))
        = denseDiffSumOver S m fs := by
  intro fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [List.map_cons, denseDiffSumP, ih, denseDiffSumOver]
      cases denseDiffSumOver S m fs
      · rfl
      · cases S.payload[f]? <;> cases m.payload[f]? <;> rfl

theorem denseAddrNonzeroNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (S m : BusInteraction (DenseExpr p)) :
    denseAddrNonzeroNeqP nw (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrNonzeroNeq shape nw S m := by
  unfold denseAddrNonzeroNeqP denseAddrNonzeroNeq
  rw [denseAddrPrep_slots_zip, List.sublists_map, List.any_map]
  refine congrArg _ (funext fun fs => ?_)
  simp only [Function.comp_apply]
  rw [denseDiffSumP_eq]
  rfl

theorem denseMidRefutedP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    denseMidRefutedP ops T.get.nonzero busId (denseAddrPrep shape T.get.tworoot S)
        (denseAddrPrep shape T.get.tworoot m)
      = denseMidRefuted ops shape T busId S m := by
  unfold denseMidRefutedP denseMidRefuted
  rw [denseAddrConstsNeqP_eq, denseAddrAffineNeqP_eq, denseAddrTwoRootNeqP_eq,
    denseAddrNonzeroNeqP_eq]
  rfl

theorem densePreRefutedP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape)
        (denseAddrPrep shape T.get.tworoot S) (denseAddrPrep shape T.get.tworoot m)
      = densePreRefuted ops shape T busId S m := by
  unfold densePreRefutedP densePreRefuted
  rw [denseMidRefutedP_eq]
  rfl

theorem denseProvRecvP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    denseProvRecvP busId (denseGetPreviousMult ops shape) (denseAddrPrep shape T S)
        (denseAddrPrep shape T m)
      = denseProvRecv ops shape busId S m := by
  unfold denseProvRecvP denseProvRecv
  rw [denseAddrConstsEqP_eq]
  rfl

/-! ## Off-bus records

A prepared record for a position on another bus is only ever asked for its `busId`: the mid and pre
tests answer `true` on their first arm and `denseProvRecvP` answers `false`. That is what lets one
prepared array serve every memory bus, with a bus-id-only stub off all of them
(`denseAddrPrepAll`). -/

theorem denseMidRefutedP_offBus (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (a b : DenseAddrPre p) (h : b.busId ≠ busId) : denseMidRefutedP ops nw busId a b = true := by
  unfold denseMidRefutedP
  rw [decide_eq_true h]
  simp

theorem densePreRefutedP_offBus (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (setMult : ZMod p) (a b : DenseAddrPre p) (h : b.busId ≠ busId) :
    densePreRefutedP ops nw busId setMult a b = true := by
  unfold densePreRefutedP
  rw [denseMidRefutedP_offBus ops nw busId a b h]
  simp

theorem denseProvRecvP_offBus (busId : Nat) (getPrevMult : ZMod p) (a b : DenseAddrPre p)
    (h : b.busId ≠ busId) : denseProvRecvP busId getPrevMult a b = false := by
  unfold denseProvRecvP
  rw [decide_eq_false h]
  simp

theorem denseProvRecv_offBus (ops : DenseZModOps p) (shape : MemoryBusShape) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) (h : m.busId ≠ busId) :
    denseProvRecv ops shape busId S m = false := by
  unfold denseProvRecv
  rw [decide_eq_false h]
  simp

end ApcOptimizer.Dense
