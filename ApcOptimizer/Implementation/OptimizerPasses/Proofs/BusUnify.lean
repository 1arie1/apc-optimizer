import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.AddrDiseq
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-! # Soundness for the dense `busUnify` pass

`DensePassCorrect` for `denseBusUnifyF` (`BusUnify.lean`), lifted through `DenseVerifiedPassW.of`.
`busUnify` only adds constraints, so soundness is a constraint superset
(`DensePassCorrect.denseAddConstraints`); the substance is real-trace completeness — every
admissible satisfying assignment already fulfils the added slot equalities. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small value-level helpers -/

/-- A dense constant-folded expression evaluates to its recognized constant. -/
private theorem denseConstValueEval (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  grind [DenseExpr.constValue?, DenseExpr.eval]

/-- `denseEqExpr e₂ e₁` evaluates to `e₂ − e₁`. -/
theorem denseEqExpr_eval (e2 e1 : DenseExpr p) (denv : VarId → ZMod p) :
    (denseEqExpr e2 e1).eval denv = e2.eval denv - e1.eval denv := by
  show e2.eval denv + (-1) * e1.eval denv = _
  ring

/-- Both entries of equal-under-`denv` payloads evaluate equally. -/
theorem densePayloadSlot_eval_eq (P Q : List (DenseExpr p)) (denv : VarId → ZMod p)
    (h : P.map (fun e => e.eval denv) = Q.map (fun e => e.eval denv)) (i : Nat) :
    ((P[i]?).getD (.const 0)).eval denv = ((Q[i]?).getD (.const 0)).eval denv := by
  have hi := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map] at hi
  cases hP : P[i]? <;> cases hQ : Q[i]? <;> rw [hP, hQ] at hi <;> simp_all

/-! ## The constant-address (dis)equality certificates -/

theorem denseAddrConstsEq_sound (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p))
    (h : denseAddrConstsEq shape S S' = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) = shape.address (denseBIEval S' denv) := by
  unfold MemoryBusShape.address
  apply List.map_congr_left
  intro slot hslot
  have hs := List.all_eq_true.mp h slot hslot
  show (S.payload.map (fun e => e.eval denv))[slot]?
    = (S'.payload.map (fun e => e.eval denv))[slot]?
  grind [denseConstValueEval]

theorem denseAddrConstsNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (h : denseAddrConstsNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  grind [denseAddrConstsNeq, denseConstValueEval, denseAddr_slot_neq]

/-! ## The load-bearing fact application -/

/-- Filtering evaluated dense messages by bus id equals evaluating the bus-filtered interactions
    (`denseBIEval` preserves `busId`). -/
theorem dense_map_eval_filter_busId (l : List (BusInteraction (DenseExpr p))) (busId : Nat)
    (denv : VarId → ZMod p) :
    (l.map (fun bi => denseBIEval bi denv)).filter (fun m => m.busId = busId)
    = (l.filter (fun bi => bi.busId = busId)).map (fun bi => denseBIEval bi denv) := by
  induction l with
  | nil => rfl
  | cons bi rest ih =>
    have hbid : (denseBIEval bi denv).busId = bi.busId := rfl
    simp only [List.map_cons, List.filter_cons, hbid]
    by_cases h : bi.busId = busId
    · simp [h, ih]
    · simp [h, ih]

/-- The load-bearing `BusFacts` use: `facts.admissible_sound` delivers `admissibleMemoryBus`, whose
    `.consecutive` forces a consecutive same-address send→receive pair to carry equal payloads. -/
theorem denseConsecutivePayloadEq (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p)
    (hadm : d.admissible bs denv)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre mid post : List (BusInteraction (DenseExpr p)))
    (S R : BusInteraction (DenseExpr p))
    (hsplit : d.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hS : (denseBIEval S denv).multiplicity = shape.setNewMult)
    (hR : (denseBIEval R denv).multiplicity = -shape.setNewMult)
    (haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv))
    (hmid : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
        shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False) :
    (denseBIEval S denv).payload = (denseBIEval R denv).payload := by
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hb := facts.admissible_sound (d.busInteractions.map (fun bi => denseBIEval bi denv)) hadm'
    busId shape hshape
  rw [dense_map_eval_filter_busId, hsplit, List.map_append, List.map_cons, List.map_append,
    List.map_cons] at hb
  exact admissibleMemoryBus.consecutive shape _ hp1 hb
    (pre.map (fun bi => denseBIEval bi denv)) (mid.map (fun bi => denseBIEval bi denv))
    (post.map (fun bi => denseBIEval bi denv)) (denseBIEval S denv) (denseBIEval R denv) rfl hS hR
    haddr
    (by
      intro m hm hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
      exact hmid m0 hm0 hmne hmaddr)

/-! ## Recovering the split equation from a candidate's positions -/

theorem dense_split_of_positions
    {L pre restAfter seen post : List (BusInteraction (DenseExpr p))}
    {S R : BusInteraction (DenseExpr p)} {i j : Nat}
    (hi : pre.length = i) (hsplit : L = pre ++ S :: restAfter)
    (hj : seen.length = j) (hnow : L = seen ++ R :: post) (hlt : i < j) :
    L = pre ++ S :: restAfter.take (j - i - 1) ++ R :: post := by
  have hRA : restAfter = L.drop (i + 1) := by
    have h1 : L = (pre ++ [S]) ++ restAfter := by rw [hsplit]; simp
    rw [h1, List.drop_left' (by simp [hi])]
  have hRp : R :: post = L.drop j := by rw [hnow, List.drop_left' (by simp [hj])]
  have hdrop : restAfter.drop (j - i - 1) = R :: post := by
    rw [hRA, List.drop_drop, hRp]; congr 1; omega
  have hn : L = pre ++ S :: (restAfter.take (j - i - 1) ++ R :: post) := by
    rw [← hdrop, List.take_append_drop]; exact hsplit
  simpa [List.append_assoc] using hn

/-- Every var of an entailed slot equality comes from the send's or receive's payload. -/
theorem denseMemEqConstraints_vars (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p))
    {c : DenseExpr p} (hc : c ∈ denseMemEqConstraints shape S Rt) {z : VarId} (hz : z ∈ c.vars) :
    (∃ e ∈ Rt.payload, z ∈ e.vars) ∨ (∃ e ∈ S.payload, z ∈ e.vars) := by
  grind [denseMemEqConstraints, denseEqExpr, DenseExpr.vars, List.mem_of_getElem?]

/-- A var of a bus interaction's payload occurs in `d`. -/
theorem DenseConstraintSystem.mem_occ_of_payload {d : DenseConstraintSystem p}
    {bi : BusInteraction (DenseExpr p)} {e : DenseExpr p} {z : VarId}
    (hbi : bi ∈ d.busInteractions) (he : e ∈ bi.payload) (hz : z ∈ e.vars) : z ∈ d.occ :=
  DenseConstraintSystem.mem_occ_of_bi hbi (by
    simp only [denseBIVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hz⟩)

/-! ## Prepared records: the slot-wise bridges

`denseBUPrep` stores, per address slot, exactly what the certificates of `AddrDiseq.lean` read
(`cval = constValue?`, `lin = denseLinearize`, `reds = densePtrReductions`), so the three arms that
kept the original test are equal to it slot for slot. The affine and two-root arms are *not* — they
compare canonical term keys — and get their own semantic lemmas below. -/

theorem denseBUSlotsAny_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseBUSlot p → DenseBUSlot p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseBUSlotPrep T e) (denseBUSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseBUSlotsAny f (fields.map (fun slot => (S.payload[slot]?).map (denseBUSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseBUSlotPrep T)))
        = fields.any (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.any_cons]
      rw [← denseBUSlotsAny_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseBUSlotPrep T e) (denseBUSlotPrep T e') || _) = (g e e' || _)
              rw [hfg]

theorem denseBUSlotsAll_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseBUSlot p → DenseBUSlot p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseBUSlotPrep T e) (denseBUSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseBUSlotsAll f (fields.map (fun slot => (S.payload[slot]?).map (denseBUSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseBUSlotPrep T)))
        = fields.all (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.all_cons]
      rw [← denseBUSlotsAll_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseBUSlotPrep T e) (denseBUSlotPrep T e') && _) = (g e e' && _)
              rw [hfg]

/-- The hash gate on the structural compare is transparent: equal expressions hash equally. -/
private theorem denseBU_bHash_gate (e e' : DenseExpr p) :
    (e.bHash == e'.bHash && decide (e = e')) = decide (e = e') := by
  by_cases h : e = e'
  · subst h; simp
  · simp [h]

theorem denseBUConstsEq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseBUConstsEq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrConstsEq shape S m :=
  denseBUSlotsAll_eq T S m _ _ (fun e e' => by
    show ((e.bHash == e'.bHash && decide (e = e')) || _) = (decide (e = e') || _)
    rw [denseBU_bHash_gate]; rfl) shape.addressFields

theorem denseBUConstsNeq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseBUConstsNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrConstsNeq shape S m :=
  denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields

theorem denseBUPrep_slots_zip (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    ((denseBUPrep shape T S).slots).zip ((denseBUPrep shape T m).slots)
      = shape.addressFields.map (fun slot =>
          ((S.payload[slot]?).map (denseBUSlotPrep T), (m.payload[slot]?).map (denseBUSlotPrep T))) := by
  simp [denseBUPrep, denseBUOfSlots, List.zip_map']

theorem denseBUDiffSum_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p)) :
    ∀ fs : List Nat,
      denseBUDiffSum (fs.map (fun slot =>
          ((S.payload[slot]?).map (denseBUSlotPrep T), (m.payload[slot]?).map (denseBUSlotPrep T))))
        = denseDiffSumOver S m fs := by
  intro fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [List.map_cons, denseBUDiffSum, ih, denseDiffSumOver]
      cases denseDiffSumOver S m fs
      · rfl
      · cases S.payload[f]? <;> cases m.payload[f]? <;> rfl

theorem denseBUNonzeroNeq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (S m : BusInteraction (DenseExpr p)) :
    denseBUNonzeroNeq nw (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrNonzeroNeq shape nw S m := by
  unfold denseBUNonzeroNeq denseAddrNonzeroNeq
  rw [denseBUPrep_slots_zip, List.sublists_map, List.any_map]
  refine congrArg _ (funext fun fs => ?_)
  simp only [Function.comp_apply]
  rw [denseBUDiffSum_eq]
  rfl

/-! ## Canonical term keys

`denseConstDiffNZ a b` holds when `a − b` has no terms and a nonzero constant. The engine decides
that by comparing `denseBUTermKey` — the merged, zero-dropped, *sorted* term list — so equal keys
mean the two forms' normalized terms are permutations of each other, hence evaluate equally, and
the whole difference is the (differing) constants. Only this direction is needed: the engine may
refute less than `denseConstDiffNZ` would, never more. -/

theorem denseBUTermKey_perm (a b : DenseLinExpr p) (h : denseBUTermKey a = denseBUTermKey b) :
    a.norm.terms.Perm b.norm.terms := by
  have ha := List.mergeSort_perm a.norm.terms (fun x y => decide (x.1.index ≤ y.1.index))
  have hb := List.mergeSort_perm b.norm.terms (fun x y => decide (x.1.index ≤ y.1.index))
  unfold denseBUTermKey at h
  rw [h] at ha
  exact ha.symm.trans hb

/-- A linear form's value is its constant plus the sum over its *normalized* terms. -/
private theorem denseBU_eval_norm (a : DenseLinExpr p) (denv : VarId → ZMod p) :
    a.eval denv = a.const + (a.norm.terms.map (fun t => t.2 * denv t.1)).sum := by
  rw [← DenseLinExpr.norm_eval a denv]; rfl

/-- Equal canonical keys and different constants force different values — the engine's replacement
    for `denseConstDiffNZ_sound`. -/
theorem denseBUKeyNeq_sound (a b : DenseLinExpr p) (hk : denseBUTermKey a = denseBUTermKey b)
    (hc : a.const ≠ b.const) (denv : VarId → ZMod p) : a.eval denv ≠ b.eval denv := by
  have hsum : (a.norm.terms.map (fun t => t.2 * denv t.1)).sum
      = (b.norm.terms.map (fun t => t.2 * denv t.1)).sum :=
    ((denseBUTermKey_perm a b hk).map _).sum_eq
  intro heq
  rw [denseBU_eval_norm a denv, denseBU_eval_norm b denv, hsum] at heq
  exact hc (add_right_cancel heq)

/-! ## The affine and two-root arms -/

theorem denseBUAffineNeq_sound (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p))
    (h : denseBUAffineNeq (denseBUPrep shape T S) (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  rw [show denseBUAffineNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = shape.addressFields.any (fun slot =>
          match S.payload[slot]?, m.payload[slot]? with
          | some e, some e' =>
            denseBUAffineNeqSlot (denseBUSlotPrep T e) (denseBUSlotPrep T e')
          | _, _ => false) from
    denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields] at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : m.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      unfold denseBUAffineNeqSlot denseBUSlotPrep at hcond
      cases hL : denseLinearize e with
      | none => simp [hL] at hcond
      | some L =>
        cases hL' : denseLinearize e' with
        | none => simp [hL, hL'] at hcond
        | some L' =>
          simp only [hL, hL', Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨_, hkey⟩, hconst⟩ := hcond
          refine denseAddr_slot_neq shape S m denv hslot hSp hbp ?_
          rw [denseLinearize_eval e L hL denv, denseLinearize_eval e' L' hL' denv]
          exact denseBUKeyNeq_sound L L' hkey hconst denv

/-- Both branch forms of a reduction differ by a constant, so they share a canonical key. -/
theorem densePtrBranchesOf_key (k : ZMod p) (A : DenseLinExpr p) (δ cx : ZMod p)
    (rest : DenseLinExpr p) :
    denseBUTermKey (densePtrBranchesOf k A δ cx rest).2
      = denseBUTermKey (densePtrBranchesOf k A δ cx rest).1 := by
  unfold denseBUTermKey densePtrBranchesOf DenseLinExpr.norm DenseLinExpr.add DenseLinExpr.scale
  simp

theorem densePtrReductions_key {T : DenseTwoRootMap p} {E : DenseExpr p} {b1 b2 : DenseLinExpr p}
    (h : (b1, b2) ∈ densePtrReductions T E) : denseBUTermKey b2 = denseBUTermKey b1 := by
  unfold densePtrReductions at h
  cases hL : denseLinearize E with
  | none => rw [hL] at h; simp at h
  | some L =>
    rw [hL, List.mem_filterMap] at h
    obtain ⟨v, _, hmatch⟩ := h
    cases htm : T.map[v]? with
    | none => rw [htm] at hmatch; simp at hmatch
    | some kAδ =>
      obtain ⟨k, A, δ⟩ := kAδ
      rw [htm] at hmatch
      simp only [Option.some.injEq] at hmatch
      rw [show b1 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).1 from
            (congrArg Prod.fst hmatch).symm,
          show b2 = (densePtrBranchesOf k A δ (L.coeff v) (L.others v)).2 from
            (congrArg Prod.snd hmatch).symm]
      exact densePtrBranchesOf_key k A δ (L.coeff v) (L.others v)

/-- A stored reduction entry comes from an actual `densePtrReductions` pair, with the stored key
    the canonical key of both its branches and the stored constants their constants. -/
theorem denseBUSlot_reds_mem {T : DenseTwoRootMap p} {e : DenseExpr p}
    {r : UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p} (h : r ∈ (denseBUSlotPrep T e).reds) :
    ∃ b1 b2, (b1, b2) ∈ densePtrReductions T e ∧ r.2.1 = denseBUTermKey b1 ∧
      r.2.2.1 = b1.const ∧ r.2.2.2 = b2.const := by
  simp only [denseBUSlotPrep, List.mem_map] at h
  obtain ⟨⟨b1, b2⟩, hmem, rfl⟩ := h
  exact ⟨b1, b2, hmem, rfl, rfl, rfl⟩

theorem denseBUTwoRootNeq_sound {dcs : List (DenseExpr p)} (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (S m : BusInteraction (DenseExpr p))
    (h : denseBUTwoRootNeq (denseBUPrep shape T S) (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  rw [show denseBUTwoRootNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = shape.addressFields.any (fun slot =>
          match S.payload[slot]?, m.payload[slot]? with
          | some e, some e' =>
            denseBUTwoRootNeqSlot (denseBUSlotPrep T e) (denseBUSlotPrep T e')
          | _, _ => false) from
    denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields] at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : m.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      unfold denseBUTwoRootNeqSlot at hcond
      obtain ⟨ra, hra, hinner⟩ := List.any_eq_true.1 hcond
      obtain ⟨rb, hrb, hchk⟩ := List.any_eq_true.1 hinner
      obtain ⟨a1, a2, hared, hakey, hac1, hac2⟩ := denseBUSlot_reds_mem hra
      obtain ⟨b1, b2, hbred, hbkey, hbc1, hbc2⟩ := denseBUSlot_reds_mem hrb
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
      obtain ⟨⟨⟨_, hkeq⟩, h11, h12⟩, h21, h22⟩ := hchk
      have hka : denseBUTermKey a2 = denseBUTermKey a1 := densePtrReductions_key hared
      have hkb : denseBUTermKey b2 = denseBUTermKey b1 := densePtrReductions_key hbred
      have hkab : denseBUTermKey a1 = denseBUTermKey b1 := by rw [← hakey, ← hbkey]; exact hkeq
      have hev := densePtrReductions_sound T hT e a1 a2 hared denv hcon
      have hev' := densePtrReductions_sound T hT e' b1 b2 hbred denv hcon
      refine denseAddr_slot_neq shape S m denv hslot hSp hbp ?_
      rcases hev with ha | ha <;> rcases hev' with hb | hb <;> rw [ha, hb]
      · exact denseBUKeyNeq_sound a1 b1 hkab (by rw [← hac1, ← hbc1]; exact h11) denv
      · exact denseBUKeyNeq_sound a1 b2 (by rw [hkab, ← hkb]) (by rw [← hac1, ← hbc2]; exact h12) denv
      · exact denseBUKeyNeq_sound a2 b1 (by rw [hka, hkab]) (by rw [← hac2, ← hbc1]; exact h21) denv
      · exact denseBUKeyNeq_sound a2 b2 (by rw [hka, hkab, ← hkb])
          (by rw [← hac2, ← hbc2]; exact h22) denv

/-! ## The verifier -/

theorem denseBUWits_eq (d : DenseConstraintSystem p) :
    denseBUWits d = DenseNonzeroWits.build d.algebraicConstraints := rfl

/-- One verified `mid` position: the message is inactive or provably at a different address. -/
theorem denseBUMidOk_sound (d : DenseConstraintSystem p) (reg : VarRegistry)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints) (S m : BusInteraction (DenseExpr p))
    (hScov : denseBICovered reg S) (hmcov : denseBICovered reg m)
    (h : denseBUMidOk denseZModOps (denseBUWits d) (denseBUPrep shape T S)
      (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0) :
    (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
  intro hmne hmaddr
  unfold denseBUMidOk at h
  rcases (Bool.or_eq_true _ _).mp h with hcond | hz
  · rcases (Bool.or_eq_true _ _).mp hcond with hcond_a | hnz
    · rcases (Bool.or_eq_true _ _).mp hcond_a with hcond2 | h2r
      · rcases (Bool.or_eq_true _ _).mp hcond2 with hneq | haff
        · exact denseAddrConstsNeq_sound shape S m
            (by rw [← denseBUConstsNeq_eq shape T S m]; exact hneq) denv hmaddr.symm
        · exact denseBUAffineNeq_sound shape T S m haff denv hmaddr.symm
      · exact denseBUTwoRootNeq_sound shape T hT S m h2r denv hcon hmaddr.symm
    · refine denseAddrNonzeroNeq_sound reg shape d.algebraicConstraints hcov.1 S m hScov hmcov
        ?_ denv hcon hmaddr.symm
      rw [← denseBUNonzeroNeq_eq shape T (DenseNonzeroWits.build d.algebraicConstraints) S m,
        ← denseBUWits_eq d]
      exact hnz
  · refine hmne (denseConstValueEval m.multiplicity 0 ?_ denv)
    have := of_decide_eq_true hz
    simpa [denseBUPrep, denseBUOfSlots, denseMultConst, denseZModOps, zmodZeroP_eq] using this

/-- Every position strictly between the candidate's endpoints passes `denseBUMidOk`. -/
theorem denseBUMidScan_sound (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (arr : Array (DenseBUPre p)) (a : DenseBUPre p) (j : Nat) :
    ∀ (fuel q : Nat), denseBUMidScan ops nw arr a j fuel q = true →
      ∀ (r : Nat) (b : DenseBUPre p), q ≤ r → r < j → r < q + fuel → arr[r]? = some b →
        denseBUMidOk ops nw a b = true := by
  intro fuel
  induction fuel with
  | zero => intro q _ r _ _ _ hlt _; omega
  | succ fuel ih =>
    intro q h r b hqr hrj hrf hb
    rw [denseBUMidScan] at h
    split at h
    · omega
    · rename_i hqj
      split at h
      · rename_i hq
        rcases Nat.eq_or_lt_of_le hqr with rfl | hlt
        · rw [hb] at hq; exact absurd hq (by simp)
        · exact absurd hq (by
            intro hq0
            have : q < arr.size := by
              by_contra hc
              have : arr[r]? = none := by
                simp only [Array.getElem?_eq_none_iff]; omega
              rw [hb] at this; exact absurd this (by simp)
            simp [Array.getElem?_eq_getElem this] at hq0)
      · rename_i bq hq
        split at h
        · rename_i hok
          rcases Nat.eq_or_lt_of_le hqr with rfl | hlt
          · rw [hb] at hq; injection hq with hq; subst hq; exact hok
          · exact ih (q + 1) h r b (by omega) hrj (by omega) hb
        · exact absurd h (by simp)

/-! ## Positions back to a list split -/

private theorem dense_list_at {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l = l.take i ++ x :: l.drop (i + 1) ∧ (l.take i).length = i := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨?_, by simp [Nat.min_eq_left hi.le]⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi, hx]

private theorem dense_mem_mid {α : Type} {l : List α} {i j : Nat} {x : α}
    (h : x ∈ (l.drop (i + 1)).take (j - i - 1)) : ∃ q, i < q ∧ q < j ∧ l[q]? = some x := by
  obtain ⟨t, ht⟩ := List.getElem?_of_mem h
  rw [List.getElem?_take] at ht
  split at ht
  · rename_i htlt
    rw [List.getElem?_drop] at ht
    exact ⟨i + 1 + t, by omega, by omega, ht⟩
  · exact absurd ht (by simp)

/-! ## The verified pair -/

theorem denseBUPrep_mult (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bi : BusInteraction (DenseExpr p)) :
    (denseBUPrep shape T bi).mult = denseMultConst bi := rfl

private theorem dense_arr_get {α β : Type} (l : List α) (f : α → β) {k : Nat} {x : α}
    (h : l[k]? = some x) : (l.toArray.map f)[k]? = some (f x) := by
  simp [h]

/-- The engine's verifier entails the reference `denseCheckPair`'s conclusion: the pair's payloads
    agree, so every slot equality it emits vanishes. -/
theorem denseBUCheckPair_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (bisL : List (BusInteraction (DenseExpr p)))
    (hbis : bisL = d.busInteractions.filter (fun bi => bi.busId = busId))
    (i j : Nat) (S R : BusInteraction (DenseExpr p))
    (hS : bisL[i]? = some S) (hR : bisL[j]? = some R)
    (hchk : denseBUCheckPair denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) (bisL.toArray.map (denseBUPrep shape T)) i j
      = true)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseMemEqConstraints shape S R, c.eval denv = 0 := by
  have hai := dense_arr_get bisL (denseBUPrep shape T) hS
  have haj := dense_arr_get bisL (denseBUPrep shape T) hR
  unfold denseBUCheckPair at hchk
  rw [hai, haj] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨hij, hSm⟩, hRm⟩, haddrEq⟩, hscan⟩ := hchk
  rw [denseBUPrep_mult, denseSetNewMult_eq] at hSm
  rw [denseBUPrep_mult, denseGetPreviousMult_eq] at hRm
  -- the split the fact application needs
  obtain ⟨hsplitS, hlenS⟩ := dense_list_at hS
  obtain ⟨hsplitR, hlenR⟩ := dense_list_at hR
  have hsplit : bisL = bisL.take i ++ S :: (bisL.drop (i + 1)).take (j - i - 1)
      ++ R :: bisL.drop (j + 1) :=
    dense_split_of_positions hlenS hsplitS hlenR hsplitR hij
  subst hbis
  set bisL := d.busInteractions.filter (fun bi => bi.busId = busId) with hbisL
  set mid := (bisL.drop (i + 1)).take (j - i - 1) with hmid
  have hmemfilter : ∀ x ∈ bisL.take i ++ S :: mid ++ R :: bisL.drop (j + 1),
      x ∈ d.busInteractions := by
    intro x hx; rw [← hsplit] at hx; exact List.mem_of_mem_filter hx
  have hScov : denseBICovered reg S := hcov.2 S (hmemfilter S (by simp))
  have hRcov : denseBICovered reg R := hcov.2 R (hmemfilter R (by simp))
  have hSev : (denseBIEval S denv).multiplicity = shape.setNewMult :=
    denseConstValueEval S.multiplicity shape.setNewMult hSm denv
  have hRev : (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    denseConstValueEval R.multiplicity (-shape.setNewMult) hRm denv
  have haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) :=
    denseAddrConstsEq_sound shape S R (by
      rw [← denseBUConstsEq_eq shape T S R]; exact haddrEq) denv
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  have hmidall : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
    intro m hm
    obtain ⟨q, hiq, hqj, hq⟩ := dense_mem_mid hm
    have hmcov : denseBICovered reg m := hcov.2 m (hmemfilter m (by simp [hm]))
    refine denseBUMidOk_sound d reg hcov shape T hT S m hScov hmcov ?_ denv hcon
    exact denseBUMidScan_sound _ _ _ _ _ (j - i) (i + 1) hscan q _ (by omega) hqj (by omega)
      (dense_arr_get bisL (denseBUPrep shape T) hq)
  have hpay : (denseBIEval S denv).payload = (denseBIEval R denv).payload :=
    denseConsecutivePayloadEq d bs facts hp1 denv hadm busId shape hshape (bisL.take i) mid
      (bisL.drop (j + 1)) S R hsplit hSev hRev haddr hmidall
  intro c hc
  unfold denseMemEqConstraints at hc
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hc
  rw [denseEqExpr_eval]
  have hPQ : R.payload.map (fun e => e.eval denv) = S.payload.map (fun e => e.eval denv) := hpay.symm
  rw [densePayloadSlot_eval_eq R.payload S.payload denv hPQ t, sub_self]

/-! ## From the emitted equalities back to a verified pair

The sweep, the scatter and the candidate order carry no obligation: `denseBUCheckPair` re-derives
`i < j` and both endpoints from the array itself, so all the collector has to expose is *which*
pair produced an equality. -/

theorem denseBUCollect_mem (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (shape : MemoryBusShape)
    (bis : Array (BusInteraction (DenseExpr p))) (arr : Array (DenseBUPre p)) :
    ∀ (cands : List (Nat × Nat)) (c : DenseExpr p),
      c ∈ denseBUCollect ops nw setMult prevMult shape bis arr cands →
      ∃ i j S R, denseBUCheckPair ops nw setMult prevMult arr i j = true ∧
        bis[i]? = some S ∧ bis[j]? = some R ∧ c ∈ denseMemEqConstraints shape S R
  | [], c, hc => by simp [denseBUCollect] at hc
  | (i, j) :: rest, c, hc => by
      rw [denseBUCollect] at hc
      split at hc
      · rename_i hchk
        split at hc
        · rename_i S R hSi hRj
          rcases List.mem_append.1 hc with h | h
          · exact ⟨i, j, S, R, hchk, hSi, hRj, h⟩
          · exact denseBUCollect_mem ops nw setMult prevMult shape bis arr rest c h
        · exact denseBUCollect_mem ops nw setMult prevMult shape bis arr rest c hc
      · exact denseBUCollect_mem ops nw setMult prevMult shape bis arr rest c hc

theorem denseBUForBus_mem (ops : DenseZModOps p) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (shape : MemoryBusShape) (bisL : List (BusInteraction (DenseExpr p))) (c : DenseExpr p)
    (hc : c ∈ denseBUForBus ops T nw shape bisL) :
    ∃ i j S R,
      denseBUCheckPair ops nw (denseSetNewMult ops shape) (denseGetPreviousMult ops shape)
        (bisL.toArray.map (denseBUPrep shape T)) i j = true ∧
      bisL[i]? = some S ∧ bisL[j]? = some R ∧ c ∈ denseMemEqConstraints shape S R := by
  obtain ⟨i, j, S, R, hchk, hSi, hRj, hmem⟩ :=
    denseBUCollect_mem ops nw _ _ shape bisL.toArray _ _ c hc
  exact ⟨i, j, S, R, hchk, by simpa using hSi, by simpa using hRj, hmem⟩

/-- Each entry of the bus split is a declared memory bus with exactly its interactions. -/
theorem denseBUBusLists_mem {memShape : Nat → Option MemoryBusShape}
    {bis : List (BusInteraction (DenseExpr p))} {e : Nat × MemoryBusShape ×
      List (BusInteraction (DenseExpr p))} (h : e ∈ denseBUBusLists memShape bis) :
    memShape e.1 = some e.2.1 ∧ e.2.2 = bis.filter (fun bi => bi.busId = e.1) := by
  unfold denseBUBusLists at h
  obtain ⟨busId, _, hmap⟩ := List.mem_filterMap.1 h
  cases hms : memShape busId with
  | none => rw [hms] at hmap; exact absurd hmap (by simp)
  | some shape =>
    rw [hms] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    subst hmap
    exact ⟨hms, rfl⟩

/-- The structure of an emitted equality: a declared bus, a split of that bus's interaction list,
    and the verifier's verdict on the pair. -/
theorem denseBUEqs_mem (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    {c : DenseExpr p} (hc : c ∈ denseBUEqs facts.memShape d) :
    ∃ busId shape i j S R,
      facts.memShape busId = some shape ∧
      (d.busInteractions.filter (fun bi => bi.busId = busId))[i]? = some S ∧
      (d.busInteractions.filter (fun bi => bi.busId = busId))[j]? = some R ∧
      denseBUCheckPair denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape)
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).toArray.map
          (denseBUPrep shape (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)))
          i j = true ∧
      c ∈ denseMemEqConstraints shape S R := by
  rw [show denseBUEqs facts.memShape d
      = (if (denseBUBusLists facts.memShape d.busInteractions).isEmpty then []
         else denseBUEqsOf (denseBUBusLists facts.memShape d.busInteractions) d) from rfl] at hc
  split at hc
  · simp at hc
  · rw [show denseBUEqsOf (denseBUBusLists facts.memShape d.busInteractions) d
        = ((denseBUBusLists facts.memShape d.busInteractions).map (fun sl =>
            denseBUForBus denseZModOps
              (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
              (denseBUWits d) sl.2.1 sl.2.2)).flatten from rfl,
      List.mem_flatten] at hc
    obtain ⟨l, hl, hcl⟩ := hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hms, hfilter⟩ := denseBUBusLists_mem he
    obtain ⟨i, j, S, R, hchk, hSi, hRj, hmem⟩ := denseBUForBus_mem _ _ _ _ _ c hcl
    rw [hfilter] at hSi hRj hchk
    exact ⟨e.1, e.2.1, i, j, S, R, hms, hSi, hRj, hchk, hmem⟩

/-! ## The two-root table is sound

Every entry the build inserts is a `denseTwoRootOf?` decomposition of an actual constraint, which
is all `DenseTwoRootMap.Sound` asserts — scoping the build to fewer variables and fewer constraints
only removes entries. -/

theorem denseBUAddTwoRoot_sound {dcs : List (DenseExpr p)} (hp : Nat.Prime p)
    (avars : Std.HashSet VarId) {c : DenseExpr p} (hc : c ∈ dcs) (T : DenseTwoRootMap p)
    (hT : T.Sound dcs) : (denseBUAddTwoRoot avars T c).Sound dcs := by
  unfold denseBUAddTwoRoot
  split
  · rename_i f1 f2
    split
    · rename_i l1 l2 hl1 hl2
      refine List.foldlRecOn _ _ hT ?_
      intro T' hT' v _
      split
      · split
        · rename_i k A δ htr
          split
          · exact hT'.insertEntry ⟨hp, by assumption, _, hc, by
              simp only [denseTwoRootOf?, hl1, hl2] ; exact htr⟩
          · exact hT'
        · exact hT'
      · exact hT'
    · exact hT
  · exact hT

theorem denseBUTwoRootMap_sound (avars : Std.HashSet VarId) (cs dcs : List (DenseExpr p))
    (hsub : ∀ c ∈ cs, c ∈ dcs) : (denseBUTwoRootMap avars cs).Sound dcs := by
  unfold denseBUTwoRootMap
  split
  · rename_i hp
    refine List.foldlRecOn _ _ (DenseTwoRootMap.empty_sound dcs) ?_
    intro T hT c hc
    exact denseBUAddTwoRoot_sound hp avars (hsub c hc) T hT
  · exact DenseTwoRootMap.empty_sound dcs

theorem denseBUTable_sound
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) :
    (denseBUTable busLists d).Sound d.algebraicConstraints :=
  denseBUTwoRootMap_sound _ _ _ (fun _ h => List.mem_of_mem_filter h)

/-! ## The appended constraints -/

theorem denseBUFilterNew_subset (d : DenseConstraintSystem p) (eqs : List (DenseExpr p))
    {c : DenseExpr p} (h : c ∈ denseBUFilterNew d eqs) : c ∈ eqs :=
  List.mem_of_mem_filter h

theorem denseBusUnifyNewCs_subset (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) {c : DenseExpr p} (h : c ∈ denseBusUnifyNewCs bs facts d) :
    c ∈ denseBUEqs facts.memShape d := by
  rw [show denseBusUnifyNewCs bs facts d
      = (if (denseBUEqs facts.memShape d).isEmpty then []
         else denseBUFilterNew d (denseBUEqs facts.memShape d)) from rfl] at h
  split at h
  · simp at h
  · exact denseBUFilterNew_subset d _ h

/-- The two interactions of an emitted equality are interactions of `d`. -/
private theorem dense_mem_of_filter_get {d : DenseConstraintSystem p} {busId i : Nat}
    {S : BusInteraction (DenseExpr p)}
    (h : (d.busInteractions.filter (fun bi => bi.busId = busId))[i]? = some S) :
    S ∈ d.busInteractions :=
  List.mem_of_mem_filter (List.mem_of_getElem? h)

/-! ## The pass transform: correctness and coverage

The two obligations below are what the engine has to deliver. Both go through the same three
steps, none of which is done yet:

1. **Bus split.** `denseBUBusLists facts.memShape d.busInteractions` holds, at each entry, a bus's
   `d.busInteractions.filter (·.busId = busId)` as an array (one pass, first-occurrence order).
2. **Candidate split.** A pair `(i, j) ∈ denseBUCands (denseBUSweep …) …` satisfies `i < j` and
   both index that array, so `dense_split_of_positions` recomposes the bus list — the sweep's
   verdicts play no part.
3. **Verifier agreement.** `denseBUCheckPair ops nw setMult prevMult arr i j = true` implies
   `denseCheckPair shape T nw arr[i] mid arr[j] = true` for that `mid`: the prepared records carry
   exactly the data the certificates read (`cval = constValue?`, `lin = denseLinearize`,
   `reds = densePtrReductions`), one `*P_eq`-style lemma per arm, plus `a = b → a.bHash = b.bHash`
   for the hash gate in `denseBUConstsEq`. Then `denseCheckPair_sound` applies verbatim.
-/

theorem denseBusUnifyNewCs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusUnifyNewCs bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨busId, shape, i, j, S, R, _, hSi, hRj, _, hmem⟩ :=
    denseBUEqs_mem bs facts d (denseBusUnifyNewCs_subset bs facts d hc)
  rcases denseMemEqConstraints_vars shape S R hmem hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
  · exact DenseConstraintSystem.mem_occ_of_payload (dense_mem_of_filter_get hRj) he hze
  · exact DenseConstraintSystem.mem_occ_of_payload (dense_mem_of_filter_get hSi) he hze

theorem denseBusUnifyNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (hp1 : (1 : ZMod p) ≠ 0)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusUnifyNewCs bs facts d, c.eval denv = 0 := by
  intro c hc
  obtain ⟨busId, shape, i, j, S, R, hms, hSi, hRj, hchk, hmem⟩ :=
    denseBUEqs_mem bs facts d (denseBusUnifyNewCs_subset bs facts d hc)
  exact denseBUCheckPair_sound d bs facts hp1 reg hcov _
    (denseBUTable_sound (denseBUBusLists facts.memShape d.busInteractions) d) busId shape hms
    _ rfl i j S R hSi hRj hchk denv hadm hsat c hmem

/-- The `let`-bound body, unfolded (definitionally). -/
theorem denseBusUnifyF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusUnifyF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusUnifyNewCs bs facts d).isEmpty then d
         else { d with algebraicConstraints :=
                  d.algebraicConstraints ++ denseBusUnifyNewCs bs facts d })
       else d) := rfl

theorem denseBusUnifyF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBusUnifyF bs facts d).CoveredBy reg := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 _hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseBusUnifyNewCs_vars bs facts d e h i hi)
  · exact hcov

theorem denseBusUnifyF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBusUnifyF bs facts d) [] bs := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 _hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseBusUnifyNewCs bs facts d)
      (denseBusUnifyNewCs_vars bs facts d)
      (fun denv hadm hsat => denseBusUnifyNewCs_sound bs facts reg d hcov hp1 denv hadm hsat)
  · exact DensePassCorrect.refl reg.isInput d bs

/-! ## The dense `busUnify` pass -/

/-- The dense `busUnify` pass (see `denseBusUnifyF`). -/
def denseBusUnifyPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseBusUnifyF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusUnifyF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusUnifyF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
