import ApcOptimizer.Implementation.OptimizerPasses.ZeroRegister
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable

set_option autoImplicit false

/-! # Dense fixed-zero-register pinning: correctness proof and wiring

`DensePassCorrect` proof for `ZeroRegister.lean` via `DensePassCorrect.denseAddConstraints`
(appending `data_i = 0` for every active fixed-zero memory message), lifted through
`DenseVerifiedPassW.of`. The entailment needs only admissibility (`facts.zeroCell_sound`); the
candidate collection `denseCollectZeroCells` carries its entailment proof alongside the data. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Every expression `denseCellZeroExprs` returns evaluates to `0` on an admissible assignment
    (`zeroCell_sound`). Needs only admissibility. -/
theorem denseCellZeroExprs_eval_zero (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ d.busInteractions)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (c : DenseExpr p)
    (hc : c ∈ denseCellZeroExprs bs facts bi) : c.eval denv = 0 := by
  unfold denseCellZeroExprs at hc
  split at hc
  · exact absurd hc (by simp)
  · rename_i addrReq dataSlots hzc
    split at hc
    · exact absurd hc (by simp)
    · rename_i cval hconst
      split at hc
      · rename_i hcond
        rw [Bool.and_eq_true] at hcond
        obtain ⟨hcne, haddrall⟩ := hcond
        have hcne' : cval ≠ 0 := of_decide_eq_true hcne
        rw [List.mem_map] at hc
        obtain ⟨slot, hslot, rfl⟩ := hc
        have hmem : denseBIEval bi denv ∈ d.busInteractions.map (fun b => denseBIEval b denv) :=
          List.mem_map.2 ⟨bi, hbi, rfl⟩
        have hadm' : bs.admissible ((d.busInteractions.map (fun b => denseBIEval b denv)).filter
            (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
        have hbusId : (denseBIEval bi denv).busId = bi.busId := rfl
        have hmult : (denseBIEval bi denv).multiplicity = cval :=
          bi.multiplicity.constValue?_sound cval hconst denv
        have hmne : (denseBIEval bi denv).multiplicity ≠ 0 := by rw [hmult]; exact hcne'
        have haddr : ∀ ar ∈ addrReq, (denseBIEval bi denv).payload[ar.1]? = some ar.2 := by
          intro ar har
          have hpay : bi.payload[ar.1]? = some (DenseExpr.const ar.2) :=
            of_decide_eq_true (List.all_eq_true.1 haddrall ar har)
          show (bi.payload.map (fun e => e.eval denv))[ar.1]? = some ar.2
          rw [List.getElem?_map, hpay]; rfl
        cases hpsl : bi.payload[slot]? with
        | none => simp [DenseExpr.eval]
        | some e =>
          rw [Option.getD_some]
          have hget : (denseBIEval bi denv).payload[slot]? = some (e.eval denv) := by
            show (bi.payload.map (fun e => e.eval denv))[slot]? = some (e.eval denv)
            rw [List.getElem?_map, hpsl]; rfl
          exact facts.zeroCell_sound (d.busInteractions.map (fun b => denseBIEval b denv)) hadm'
            bi.busId addrReq dataSlots hzc (denseBIEval bi denv) hmem hbusId hmne haddr slot hslot
            (e.eval denv) hget
      · exact absurd hc (by simp)

/-- Collect every interaction's fixed-zero data-limb expressions, carrying the proof that each
    evaluates to `0` on an admissible assignment. -/
def denseCollectZeroCells (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs) :
    (pending : List (BusInteraction (DenseExpr p))) →
    (∀ bi ∈ pending, bi ∈ d.busInteractions) →
    { out : List (DenseExpr p) //
        ∀ denv, d.admissible bs denv → ∀ c ∈ out, c.eval denv = 0 }
  | [], _ => ⟨[], fun _ _ _ h => absurd h (by simp)⟩
  | bi :: rest, hmem =>
    let ⟨acc, hacc⟩ := denseCollectZeroCells d bs facts rest
      (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
    ⟨denseCellZeroExprs bs facts bi ++ acc, by
      intro denv hadm c hc
      rcases List.mem_append.1 hc with h | h
      · exact denseCellZeroExprs_eval_zero d bs facts bi (hmem bi (List.mem_cons_self ..))
          denv hadm c h
      · exact hacc denv hadm c h⟩

/-- Membership in the collected list means membership in some pending interaction's cell
    expressions. -/
theorem denseCollectZeroCells_eq (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) :
    ∀ (pending : List (BusInteraction (DenseExpr p))) (h : ∀ bi ∈ pending, bi ∈ d.busInteractions),
      (denseCollectZeroCells d bs facts pending h).1
        = pending.flatMap (denseCellZeroExprs bs facts)
  | [], _ => rfl
  | bi :: rest, h => by
    show denseCellZeroExprs bs facts bi ++ (denseCollectZeroCells d bs facts rest _).1 = _
    rw [denseCollectZeroCells_eq d bs facts rest, List.flatMap_cons]

/-- Every variable of a cell expression is a variable of its interaction: the expression is a
    payload slot (or the constant `0`, which has none). -/
theorem denseCellZeroExprs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (c : DenseExpr p)
    (hc : c ∈ denseCellZeroExprs bs facts bi) : ∀ z ∈ c.vars, z ∈ denseBIVars bi := by
  intro z hz
  unfold denseCellZeroExprs at hc
  split at hc
  · exact absurd hc (by simp)
  · split at hc
    · exact absurd hc (by simp)
    · split at hc
      · rw [List.mem_map] at hc
        obtain ⟨slot, _, rfl⟩ := hc
        cases hpsl : bi.payload[slot]? with
        | none => rw [hpsl] at hz; simp [DenseExpr.vars] at hz
        | some e =>
          rw [hpsl, Option.getD_some] at hz
          exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, List.mem_of_getElem? hpsl, hz⟩)
      · exact absurd hc (by simp)

/-! ## The prepared-table scan equals the collect-then-filter form -/

/-- The prepared address list of a bus id, as `denseZeroCellTable` stores it. -/
private def wrapAddr (addrReq : List (Nat × ZMod p)) : List (Nat × DenseExpr p) :=
  addrReq.map (fun ar => (ar.1, DenseExpr.const ar.2))

/-- Only buses that declare a fixed-zero cell reach the table, with the shape `facts` gives. -/
theorem denseZeroCellTable_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (id : Nat) (zc : DenseZeroCell p)
    (h : (id, zc) ∈ denseZeroCellTable bs facts bis) :
    ∃ addrReq dataSlots, facts.zeroCell id = some (addrReq, dataSlots) ∧
      zc = (wrapAddr addrReq, dataSlots) := by
  rw [denseZeroCellTable, List.mem_filterMap] at h
  obtain ⟨id', _, hf⟩ := h
  cases hzc : facts.zeroCell id' with
  | none => rw [hzc] at hf; exact absurd hf (by simp)
  | some ad =>
    obtain ⟨addrReq, dataSlots⟩ := ad
    rw [hzc] at hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨addrReq, dataSlots, hzc, rfl⟩

/-- The seen-set fold only grows. -/
theorem denseBusIds_mono (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (init : List Nat) (x : Nat), x ∈ init → x ∈ bis.foldl denseBusIdStep init := by
  induction bis with
  | nil => intro _ _ h; exact h
  | cons bi rest ih =>
    intro init x hx
    refine ih (denseBusIdStep init bi) x ?_
    unfold denseBusIdStep
    split
    · exact hx
    · exact List.mem_cons_of_mem _ hx

/-- Every interaction's bus id is in the seen set. -/
theorem denseBusIds_mem (bis : List (BusInteraction (DenseExpr p))) :
    ∀ (init : List Nat) (bi : BusInteraction (DenseExpr p)), bi ∈ bis →
      bi.busId ∈ bis.foldl denseBusIdStep init := by
  induction bis with
  | nil => intro _ _ h; exact absurd h (by simp)
  | cons b rest ih =>
    intro init bi hbi
    rcases List.mem_cons.1 hbi with rfl | hrest
    · refine denseBusIds_mono rest (denseBusIdStep init bi) bi.busId ?_
      unfold denseBusIdStep
      split
      · rename_i hcon; exact List.mem_of_elem_eq_true hcon
      · exact List.mem_cons_self ..
    · exact ih (denseBusIdStep init b) bi hrest

/-- Every bus that declares a fixed-zero cell and carries an interaction is in the table. -/
theorem denseZeroCellTable_complete (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis)
    (addrReq : List (Nat × ZMod p)) (dataSlots : List Nat)
    (hzc : facts.zeroCell bi.busId = some (addrReq, dataSlots)) :
    (bi.busId, (wrapAddr addrReq, dataSlots)) ∈ denseZeroCellTable bs facts bis := by
  rw [denseZeroCellTable, List.mem_filterMap]
  exact ⟨bi.busId, denseBusIds_mem bis [] bi hbi, by rw [hzc]; rfl⟩

/-- The prepared address test is the `zeroCell` address requirement. -/
theorem denseAddrPinned_eq (payload : List (DenseExpr p)) (addrReq : List (Nat × ZMod p)) :
    denseAddrPinned payload (wrapAddr addrReq)
      = addrReq.all (fun ar => decide (payload[ar.1]? = some (DenseExpr.const ar.2))) := by
  induction addrReq with
  | nil => rfl
  | cons ar rest ih =>
    show denseAddrPinned payload ((ar.1, DenseExpr.const ar.2) :: wrapAddr rest) = _
    rw [denseAddrPinned, List.all_cons, ih]
    cases hp : payload[ar.1]? with
    | none => simp
    | some e => simp only [Option.some.injEq]; rfl

/-- Folding the data slots accumulates the kept slot expressions in reverse. Slots outside the
    payload contribute `const 0`, which `keep` rejects (`hkeep`). -/
theorem denseZeroCellEmit_slots (keep : DenseExpr p → Bool)
    (hkeep : keep (DenseExpr.const 0) = false) (payload : List (DenseExpr p)) (slots : List Nat) :
    ∀ acc : List (DenseExpr p),
      slots.foldl (fun a slot =>
          match payload[slot]? with
          | some e => if keep e then e :: a else a
          | none => a) acc
        = ((slots.map (fun slot => (payload[slot]?).getD (DenseExpr.const 0))).filter keep).reverse
            ++ acc := by
  induction slots with
  | nil => intro acc; rfl
  | cons s rest ih =>
    intro acc
    rw [List.map_cons, List.foldl_cons, ih]
    cases hp : payload[s]? with
    | none => simp [hkeep]
    | some e =>
      simp only [Option.getD_some, List.filter_cons]
      cases keep e <;> simp

private theorem not_zmodIsZero_eq (c : ZMod p) : (!zmodIsZero c) = decide (c ≠ 0) := by
  show (!zmodIsZero c) = decide ¬(c = 0)
  rw [zmodIsZero_eq, decide_not]

/-- `denseCellZeroExprs` written in the table's prepared terms. -/
theorem denseCellZeroExprs_of (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (addrReq : List (Nat × ZMod p)) (dataSlots : List Nat)
    (hzc : facts.zeroCell bi.busId = some (addrReq, dataSlots)) :
    denseCellZeroExprs bs facts bi
      = match bi.multiplicity.constValue? with
        | none => []
        | some c =>
          if !zmodIsZero c && denseAddrPinned bi.payload (wrapAddr addrReq) then
            dataSlots.map (fun slot => (bi.payload[slot]?).getD (DenseExpr.const 0))
          else [] := by
  rw [denseCellZeroExprs, hzc, denseAddrPinned_eq]
  cases bi.multiplicity.constValue? with
  | none => rfl
  | some c => dsimp only; rw [not_zmodIsZero_eq]

/-- One interaction's contribution to the sweep is its cell expressions, filtered and reversed. -/
theorem denseZeroCellEmit_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (keep : DenseExpr p → Bool)
    (hkeep : keep (DenseExpr.const 0) = false) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis)
    (acc : List (DenseExpr p)) :
    denseZeroCellEmit (denseZeroCellTable bs facts bis) keep bi acc
      = ((denseCellZeroExprs bs facts bi).filter keep).reverse ++ acc := by
  -- The table entry the sweep finds first is sound, so it carries `facts.zeroCell`'s shape
  -- whichever entry it is; completeness supplies one when the bus declares a cell.
  have key : ∀ tbl : List (Nat × DenseZeroCell p),
      (∀ id zc, (id, zc) ∈ tbl → ∃ addrReq dataSlots,
        facts.zeroCell id = some (addrReq, dataSlots) ∧ zc = (wrapAddr addrReq, dataSlots)) →
      (∀ addrReq dataSlots, facts.zeroCell bi.busId = some (addrReq, dataSlots) →
        (bi.busId, (wrapAddr addrReq, dataSlots)) ∈ tbl) →
      denseZeroCellEmit tbl keep bi acc
        = ((denseCellZeroExprs bs facts bi).filter keep).reverse ++ acc := by
    intro tbl
    induction tbl with
    | nil =>
      intro _ hcomp
      cases hzc : facts.zeroCell bi.busId with
      | none => rw [denseZeroCellEmit, denseCellZeroExprs, hzc]; rfl
      | some ad => exact absurd (hcomp ad.1 ad.2 (by rw [hzc])) (by simp)
    | cons entry rest ih =>
      intro hsound hcomp
      obtain ⟨id, addr, slots⟩ := entry
      show (if bi.busId == id then _ else denseZeroCellEmit rest keep bi acc) = _
      by_cases hid : bi.busId = id
      · subst hid
        obtain ⟨addrReq, dataSlots, hzc, hshape⟩ :=
          hsound bi.busId (addr, slots) (List.mem_cons_self ..)
        simp only [Prod.mk.injEq] at hshape
        obtain ⟨rfl, rfl⟩ := hshape
        rw [if_pos (beq_self_eq_true _), denseCellZeroExprs_of bs facts bi _ _ hzc]
        cases bi.multiplicity.constValue? with
        | none => rw [List.filter_nil, List.reverse_nil, List.nil_append]
        | some c =>
          dsimp only
          by_cases hcond : (!zmodIsZero c && denseAddrPinned bi.payload (wrapAddr addrReq)) = true
          · rw [if_pos hcond, if_pos hcond]
            exact denseZeroCellEmit_slots keep hkeep bi.payload slots acc
          · rw [if_neg hcond, if_neg hcond, List.filter_nil, List.reverse_nil, List.nil_append]
      · rw [if_neg (by simpa using hid)]
        refine ih (fun i z hz => hsound i z (List.mem_cons_of_mem _ hz)) ?_
        intro addrReq dataSlots hzc
        rcases List.mem_cons.1 (hcomp addrReq dataSlots hzc) with heq | hrest
        · exact absurd (congrArg Prod.fst heq) hid
        · exact hrest
  exact key (denseZeroCellTable bs facts bis) (denseZeroCellTable_sound bs facts bis)
    (fun a s h => denseZeroCellTable_complete bs facts bis bi hbi a s h)

/-- The whole sweep accumulates the filtered candidates in reverse. -/
theorem denseZeroCellSweep_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (keep : DenseExpr p → Bool)
    (hkeep : keep (DenseExpr.const 0) = false) :
    ∀ (todo : List (BusInteraction (DenseExpr p))), (∀ bi ∈ todo, bi ∈ bis) →
      ∀ acc : List (DenseExpr p),
        todo.foldl (fun a bi => denseZeroCellEmit (denseZeroCellTable bs facts bis) keep bi a) acc
          = (todo.flatMap (fun bi => (denseCellZeroExprs bs facts bi).filter keep)).reverse ++ acc
  | [], _, _ => rfl
  | bi :: rest, hsub, acc => by
    rw [List.foldl_cons,
      denseZeroCellEmit_eq bs facts bis keep hkeep bi (hsub bi (List.mem_cons_self ..)) acc,
      denseZeroCellSweep_eq bs facts bis keep hkeep rest
        (fun b hb => hsub b (List.mem_cons_of_mem _ hb)),
      List.flatMap_cons, List.reverse_append, List.append_assoc]

/-- The prepared-table scan: one `facts.zeroCell` per distinct bus id, then one allocation-free
    left-to-right sweep emitting the surviving candidates. -/
def denseZeroRegisterNewFast (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  match denseZeroCellTable bs facts d.busInteractions with
  | [] => []
  | tbl =>
    (d.busInteractions.foldl
      (fun acc bi => denseZeroCellEmit tbl (denseZeroPred d.algebraicConstraints) bi acc) []).reverse

/-- The filtered fixed-zero data-limb equalities the pass appends. -/
def denseZeroRegisterNew (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  (denseCollectZeroCells d bs facts d.busInteractions (fun _ h => h)).1.filter
    (denseZeroPred d.algebraicConstraints)

/-- `denseZeroPred` rejects the constant `0`, which is what an out-of-range data slot yields. -/
theorem denseZeroPred_const_zero (cs : List (DenseExpr p)) :
    denseZeroPred cs (DenseExpr.const 0) = false := by
  simp [denseZeroPred, DenseExpr.normalize, DenseExpr.fold, DenseExpr.isConstZero, zmodIsZero]

/-- An empty table means no interaction is on a fixed-zero-cell bus, so the sweep emits nothing. -/
private theorem foldl_emit_nil (keep : DenseExpr p → Bool)
    (todo : List (BusInteraction (DenseExpr p))) (acc : List (DenseExpr p)) :
    todo.foldl (fun a bi => denseZeroCellEmit [] keep bi a) acc = acc := by
  induction todo generalizing acc with
  | nil => rfl
  | cons _ rest ih => exact ih acc

@[csimp] theorem denseZeroRegisterNew_eq_fast :
    @denseZeroRegisterNew = @denseZeroRegisterNewFast := by
  funext q bs facts d
  have hnew : denseZeroRegisterNew bs facts d
      = d.busInteractions.flatMap (fun bi =>
          (denseCellZeroExprs bs facts bi).filter (denseZeroPred d.algebraicConstraints)) := by
    rw [denseZeroRegisterNew, denseCollectZeroCells_eq, List.filter_flatMap]
  have hsweep := denseZeroCellSweep_eq bs facts d.busInteractions
    (denseZeroPred d.algebraicConstraints) (denseZeroPred_const_zero _) d.busInteractions
    (fun _ h => h) []
  rw [List.append_nil] at hsweep
  rw [hnew, denseZeroRegisterNewFast]
  cases htbl : denseZeroCellTable bs facts d.busInteractions with
  | nil =>
    rw [htbl, foldl_emit_nil] at hsweep
    dsimp only
    exact List.reverse_eq_nil_iff.mp hsweep.symm
  | cons e rest =>
    rw [htbl] at hsweep
    dsimp only
    rw [hsweep, List.reverse_reverse]

/-- Every variable of a surviving candidate occurs in `d`: candidates come from interaction
    payloads. -/
theorem denseZeroRegisterNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseZeroRegisterNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  rw [denseZeroRegisterNew, denseCollectZeroCells_eq] at hc
  obtain ⟨bi, hbi, hcbi⟩ := List.mem_flatMap.1 (List.mem_of_mem_filter hc)
  exact DenseConstraintSystem.mem_occ_of_bi hbi (denseCellZeroExprs_vars bs facts bi c hcbi z hz)

/-- Every surviving candidate evaluates to `0` on an admissible assignment. -/
theorem denseZeroRegisterNew_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hadm : d.admissible bs denv) :
    ∀ c ∈ denseZeroRegisterNew bs facts d, c.eval denv = 0 := by
  intro c hc
  exact (denseCollectZeroCells d bs facts d.busInteractions (fun _ h => h)).2 denv hadm c
    (List.mem_of_mem_filter hc)

/-- The dense fixed-zero-register pass: appends `data_i = 0` for every data slot of a memory
    message pinned to a declared fixed-zero cell. -/
def denseZeroRegisterPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofAddConstraints denseZeroRegisterNew denseZeroRegisterNew_vars
    (fun bs facts d denv hadm _ => denseZeroRegisterNew_sound bs facts d denv hadm)

end ApcOptimizer.Dense
