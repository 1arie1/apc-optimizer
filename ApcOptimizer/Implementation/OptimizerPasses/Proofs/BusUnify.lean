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

/-! ## The checked pair and its entailment (dense) -/

/-- `denseCheckPair` entails the slot equalities: the address-disequality certificates rule out
    every `mid` blocker, so `denseConsecutivePayloadEq` forces `S.payload = R.payload` and every
    `denseMemEqConstraints` slot equality vanishes. -/
theorem denseCheckPair_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (pre : List (BusInteraction (DenseExpr p))) (S : BusInteraction (DenseExpr p))
    (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p))
    (post : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions.filter (fun bi => bi.busId = busId) = pre ++ S :: mid ++ R :: post)
    (hchk : denseCheckPair shape T (DenseNonzeroWits.build d.algebraicConstraints) S mid R = true)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseMemEqConstraints shape S R, c.eval denv = 0 := by
  have hmemfilter : ∀ x ∈ pre ++ S :: mid ++ R :: post, x ∈ d.busInteractions := by
    intro x hx; rw [← hsplit] at hx; exact List.mem_of_mem_filter hx
  have hScov : denseBICovered reg S := hcov.2 S (hmemfilter S (by simp))
  have hRcov : denseBICovered reg R := hcov.2 R (hmemfilter R (by simp))
  unfold denseCheckPair at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hSm, hRm⟩, haddrEq⟩, hmidall⟩ := hchk
  have hSm : denseMultConst S = some shape.setNewMult := of_decide_eq_true hSm
  have hRm : denseMultConst R = some (-shape.setNewMult) := of_decide_eq_true hRm
  have hSev : (denseBIEval S denv).multiplicity = shape.setNewMult :=
    denseConstValueEval S.multiplicity shape.setNewMult hSm denv
  have hRev : (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    denseConstValueEval R.multiplicity (-shape.setNewMult) hRm denv
  have haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) :=
    denseAddrConstsEq_sound shape S R haddrEq denv
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  have hmid : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
    intro m hm hmne hmaddr
    have hmcov : denseBICovered reg m := hcov.2 m (hmemfilter m (by simp [hm]))
    rcases (Bool.or_eq_true _ _).mp (List.all_eq_true.mp hmidall m hm) with hcond | hz
    · rcases (Bool.or_eq_true _ _).mp hcond with hcond_a | hnz
      · rcases (Bool.or_eq_true _ _).mp hcond_a with hcond2 | h2r
        · rcases (Bool.or_eq_true _ _).mp hcond2 with hneq | haff
          · exact denseAddrConstsNeq_sound shape S m hneq denv (hmaddr.symm)
          · exact denseAddrAffineNeq_sound reg shape S m hScov hmcov haff denv (hmaddr.symm)
        · exact denseAddrTwoRootNeq_sound reg shape T hT hcov.1 S m hScov hmcov h2r denv hcon
            (hmaddr.symm)
      · exact denseAddrNonzeroNeq_sound reg shape d.algebraicConstraints hcov.1 S m hScov hmcov hnz
          denv hcon (hmaddr.symm)
    · have : (denseBIEval m denv).multiplicity = 0 :=
        denseConstValueEval m.multiplicity 0 (of_decide_eq_true hz) denv
      exact hmne this
  have hpay : (denseBIEval S denv).payload = (denseBIEval R denv).payload :=
    denseConsecutivePayloadEq d bs facts hp1 denv hadm busId shape hshape pre mid post S R
      hsplit hSev hRev haddr hmid
  intro c hc
  unfold denseMemEqConstraints at hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
  rw [denseEqExpr_eval]
  have hPQ : R.payload.map (fun e => e.eval denv) = S.payload.map (fun e => e.eval denv) := hpay.symm
  rw [densePayloadSlot_eval_eq R.payload S.payload denv hPQ i, sub_self]

/-! ## Recovering the split equation from a candidate's positions

The sweep proposes index pairs into one bus's interaction array; `dense_split_of_positions` is the
arithmetic that turns `(i, j)` back into the `pre ++ S :: mid ++ R :: post` decomposition
`denseCheckPair_sound` consumes. -/

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
  sorry

theorem denseBusUnifyNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (hp1 : (1 : ZMod p) ≠ 0)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusUnifyNewCs bs facts d, c.eval denv = 0 := by
  sorry

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
