import ApcOptimizer.Implementation.OptimizerPasses.Encoding
import ApcOptimizer.Implementation.OptimizerPasses.FactPass

set_option autoImplicit false

/-! # Dense measures and coverage/stability at the system level

The dense degree guard and cleanup fixpoint compute measures over the dense system; here we prove
they equal the spec measures on the decoded system, so the dense driver makes the same degree and
stopping decisions. The distinct-variable count matches only because `resolve` is injective on
valid IDs, so this file also carries the system-level coverage predicates and `Extends`-stability
lemmas. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## System-level coverage -/

/-- Every leaf ID of a dense computation method is valid in `r`. -/
def DenseComputationMethod.CoveredBy (r : VarRegistry) : DenseComputationMethod p → Prop
  | .const _ => True
  | .quotientOrZero num den => num.CoveredBy r ∧ den.CoveredBy r
  | .ifEqZero cond thenM elseM => cond.CoveredBy r ∧ thenM.CoveredBy r ∧ elseM.CoveredBy r

/-- Every leaf ID of a dense constraint system is valid in `r`. -/
def DenseConstraintSystem.CoveredBy (r : VarRegistry) (d : DenseConstraintSystem p) : Prop :=
  (∀ e ∈ d.algebraicConstraints, e.CoveredBy r) ∧ (∀ bi ∈ d.busInteractions, denseBICovered r bi)

/-- Every derivation of a dense derivation list has a valid key and a covered method. -/
def DenseDerivations.CoveredBy (r : VarRegistry) (dd : DenseDerivations p) : Prop :=
  ∀ x ∈ dd, r.Valid x.1 ∧ x.2.CoveredBy r

theorem denseBICovered_mono {r r' : VarRegistry} (h : r.Extends r')
    {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered r bi) : denseBICovered r' bi :=
  ⟨hc.1.mono h, fun e he => (hc.2 e he).mono h⟩

theorem VarRegistry.encodeBIs_covered (r : VarRegistry)
    (bis : List (BusInteraction (Expression p))) :
    ∀ bi ∈ (r.encodeBIs bis).2, denseBICovered (r.encodeBIs bis).1 bi := by
  induction bis generalizing r with
  | nil => intro bi hbi; simp [VarRegistry.encodeBIs] at hbi
  | cons b rest ih =>
      rw [VarRegistry.encodeBIs_cons]
      intro bi hbi
      rcases List.mem_cons.mp hbi with heq | hmem
      · subst heq
        exact denseBICovered_mono ((r.encodeBI b).1.encodeBIs_extends rest) (r.encodeBI_covered b)
      · exact ih (r.encodeBI b).1 bi hmem

/-- The encode of a spec system is covered by the registry it produces (the pipeline entry). -/
theorem VarRegistry.encodeCS_covered (r : VarRegistry) (cs : Circuit p) :
    (r.encodeCS cs).2.CoveredBy (r.encodeCS cs).1 := by
  rw [VarRegistry.encodeCS_fst]
  refine ⟨fun e he => ?_, fun bi hbi => ?_⟩
  · rw [VarRegistry.encodeCS_acs] at he
    exact (r.encodeExprs_covered cs.algebraicConstraints e he).mono
      ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs_extends cs.busInteractions)
  · rw [VarRegistry.encodeCS_bis] at hbi
    exact (r.encodeExprs cs.algebraicConstraints).1.encodeBIs_covered cs.busInteractions bi hbi

/-! ## Decode stability under extension (computation methods, systems, derivations) -/

theorem VarRegistry.Extends.decodeCM_eq {r r' : VarRegistry} (h : r.Extends r')
    {cm : DenseComputationMethod p} (hc : cm.CoveredBy r) : r'.decodeCM cm = r.decodeCM cm := by
  induction cm with
  | const c => rfl
  | quotientOrZero num den =>
      obtain ⟨hn, hd⟩ := hc
      simp only [VarRegistry.decodeCM, h.decodeExpr_eq hn, h.decodeExpr_eq hd]
  | ifEqZero cond thenM elseM iht ihe =>
      obtain ⟨hcond, ht, he⟩ := hc
      simp only [VarRegistry.decodeCM, h.decodeExpr_eq hcond, iht ht, ihe he]

theorem VarRegistry.Extends.decodeCS_eq {r r' : VarRegistry} (h : r.Extends r')
    {d : DenseConstraintSystem p} (hc : d.CoveredBy r) : r'.decodeCS d = r.decodeCS d := by
  obtain ⟨hac, hbi⟩ := hc
  simp only [VarRegistry.decodeCS]
  congr 1
  · exact h.decodeExprs_eq hac
  · exact List.map_congr_left (fun bi hb => h.decodeBI_eq (hbi bi hb))

theorem VarRegistry.Extends.decodeDerivs_eq {r r' : VarRegistry} (h : r.Extends r')
    {dd : DenseDerivations p} (hc : dd.CoveredBy r) : r'.decodeDerivs dd = r.decodeDerivs dd := by
  simp only [VarRegistry.decodeDerivs]
  refine List.map_congr_left (fun x hx => ?_)
  obtain ⟨hk, hcm⟩ := hc x hx
  rw [Prod.ext_iff]
  exact ⟨h.resolve_eq hk, h.decodeCM_eq hcm⟩

/-- `decodeDerivs` distributes over concatenation (it is a `map`). -/
theorem VarRegistry.decodeDerivs_append (r : VarRegistry) (a b : DenseDerivations p) :
    r.decodeDerivs (a ++ b) = r.decodeDerivs a ++ r.decodeDerivs b := by
  simp only [VarRegistry.decodeDerivs, List.map_append]

/-! ## Degree correspondence -/

/-- Degree bound check on the dense system, mirroring `Circuit.withinDegreeB`. -/
def DenseConstraintSystem.withinDegreeB (d : DenseConstraintSystem p) (b : DegreeBound) : Bool :=
  d.algebraicConstraints.all (fun c => c.degree ≤ b.identities) &&
  d.busInteractions.all (fun bi =>
    decide (bi.multiplicity.degree ≤ b.busInteractions) &&
      bi.payload.all (fun e => e.degree ≤ b.busInteractions))

/-! ### The incremental degree check

`withinDegreeB` runs after every pass, and most of what it walks it has already accepted: a pass
rewrites a few items and physically shares the rest of the list, or appends and shares every old
element. Given a certificate that the *input* system is within bound, `degOkFrom` scans the output
list in lockstep with the input list and uses `withPtrEq` — core Lean, safe, inlined by the
compiler to a bare `lean_ptr_addr` compare with no closure — to skip a whole shared suffix, or a
single shared item, without walking it.

`withPtrEq a b k h` *is* `k ()`, so these are hints and nothing more: `degOkFrom_eq` proves the
result equals `withinDegreeB`. The definitions return their own specification
(`{ r : Bool // r = … }`) because `withPtrEq`'s `h` obligation has to be discharged while the
recursion is being elaborated; a `Subtype` whose only runtime field is a `Bool` is that `Bool`. -/

/-- `withinDegreeB`'s per-constraint test. -/
@[inline] def denseCsDegOk (bnd : Nat) (e : DenseExpr p) : Bool := e.degree ≤ bnd

/-- `List.all` over `denseCsDegOk` without the per-interaction closure `List.all` allocates. -/
def denseExprsDegOk (bnd : Nat) : List (DenseExpr p) → Bool
  | [] => true
  | e :: rest => denseCsDegOk bnd e && denseExprsDegOk bnd rest

theorem denseExprsDegOk_eq (bnd : Nat) (l : List (DenseExpr p)) :
    denseExprsDegOk bnd l = l.all (fun e => e.degree ≤ bnd) := by
  induction l with
  | nil => rfl
  | cons e rest ih => rw [denseExprsDegOk, ih, List.all_cons, denseCsDegOk]

/-- `withinDegreeB`'s per-interaction test. -/
def denseBiDegOk (bnd : Nat) (bi : BusInteraction (DenseExpr p)) : Bool :=
  decide (bi.multiplicity.degree ≤ bnd) && denseExprsDegOk bnd bi.payload

/-- Lockstep degree scan of `ol` against a within-bound `dl`: a pointer-identical remaining list
    ends the scan, a pointer-identical item is skipped, everything else is walked. -/
def denseCsDegFrom (bnd : Nat) : (ol dl : List (DenseExpr p)) →
    dl.all (denseCsDegOk bnd) = true → { r : Bool // r = ol.all (denseCsDegOk bnd) }
  | [], _, _ => ⟨true, rfl⟩
  | o :: ot, [], _ =>
      ⟨denseCsDegOk bnd o && (denseCsDegFrom bnd ot [] rfl).1, by
        rw [(denseCsDegFrom bnd ot [] rfl).2, List.all_cons]⟩
  | o :: ot, x :: xt, hd =>
      have hx : denseCsDegOk bnd x = true :=
        ((Bool.and_eq_true _ _).mp (by rwa [List.all_cons] at hd)).1
      have hxt : xt.all (denseCsDegOk bnd) = true :=
        ((Bool.and_eq_true _ _).mp (by rwa [List.all_cons] at hd)).2
      have hval : (withPtrEq o x (fun _ => denseCsDegOk bnd o) (fun h => by rw [h]; exact hx)
            && (denseCsDegFrom bnd ot xt hxt).1) = (o :: ot).all (denseCsDegOk bnd) := by
        show (denseCsDegOk bnd o && (denseCsDegFrom bnd ot xt hxt).1) = _
        rw [(denseCsDegFrom bnd ot xt hxt).2, List.all_cons]
      ⟨withPtrEq (o :: ot) (x :: xt)
          (fun _ => withPtrEq o x (fun _ => denseCsDegOk bnd o) (fun h => by rw [h]; exact hx)
            && (denseCsDegFrom bnd ot xt hxt).1)
          (fun h => hval.trans (by rw [h]; exact hd)),
        hval⟩

/-- `denseCsDegFrom` for bus interactions. -/
def denseBiDegFrom (bnd : Nat) : (ol dl : List (BusInteraction (DenseExpr p))) →
    dl.all (denseBiDegOk bnd) = true → { r : Bool // r = ol.all (denseBiDegOk bnd) }
  | [], _, _ => ⟨true, rfl⟩
  | o :: ot, [], _ =>
      ⟨denseBiDegOk bnd o && (denseBiDegFrom bnd ot [] rfl).1, by
        rw [(denseBiDegFrom bnd ot [] rfl).2, List.all_cons]⟩
  | o :: ot, x :: xt, hd =>
      have hx : denseBiDegOk bnd x = true :=
        ((Bool.and_eq_true _ _).mp (by rwa [List.all_cons] at hd)).1
      have hxt : xt.all (denseBiDegOk bnd) = true :=
        ((Bool.and_eq_true _ _).mp (by rwa [List.all_cons] at hd)).2
      have hval : (withPtrEq o x (fun _ => denseBiDegOk bnd o) (fun h => by rw [h]; exact hx)
            && (denseBiDegFrom bnd ot xt hxt).1) = (o :: ot).all (denseBiDegOk bnd) := by
        show (denseBiDegOk bnd o && (denseBiDegFrom bnd ot xt hxt).1) = _
        rw [(denseBiDegFrom bnd ot xt hxt).2, List.all_cons]
      ⟨withPtrEq (o :: ot) (x :: xt)
          (fun _ => withPtrEq o x (fun _ => denseBiDegOk bnd o) (fun h => by rw [h]; exact hx)
            && (denseBiDegFrom bnd ot xt hxt).1)
          (fun h => hval.trans (by rw [h]; exact hd)),
        hval⟩

/-- `withinDegreeB` in the shape `denseCsDegFrom`/`denseBiDegFrom` decide. -/
theorem DenseConstraintSystem.withinDegreeB_eq_all (d : DenseConstraintSystem p) (b : DegreeBound) :
    d.withinDegreeB b =
      (d.algebraicConstraints.all (denseCsDegOk b.identities) &&
        d.busInteractions.all (denseBiDegOk b.busInteractions)) := by
  have hbi : (fun bi : BusInteraction (DenseExpr p) =>
        decide (bi.multiplicity.degree ≤ b.busInteractions) &&
          bi.payload.all (fun e => e.degree ≤ b.busInteractions))
      = denseBiDegOk b.busInteractions := by
    funext bi; rw [denseBiDegOk, denseExprsDegOk_eq]
  rw [DenseConstraintSystem.withinDegreeB, hbi]
  rfl

/-- `withinDegreeB` on `out`, computed against a within-bound `d` so that items `out` shares with
    `d` cost one pointer compare instead of an AST walk (`degOkFrom_eq`). -/
def DenseConstraintSystem.degOkFrom (b : DegreeBound) (d out : DenseConstraintSystem p)
    (h : d.withinDegreeB b = true) : Bool :=
  (denseCsDegFrom b.identities out.algebraicConstraints d.algebraicConstraints
      ((Bool.and_eq_true _ _).mp (d.withinDegreeB_eq_all b ▸ h)).1).1 &&
  (denseBiDegFrom b.busInteractions out.busInteractions d.busInteractions
      ((Bool.and_eq_true _ _).mp (d.withinDegreeB_eq_all b ▸ h)).2).1

theorem DenseConstraintSystem.degOkFrom_eq (b : DegreeBound) (d out : DenseConstraintSystem p)
    (h : d.withinDegreeB b = true) : d.degOkFrom b out h = out.withinDegreeB b := by
  rw [DenseConstraintSystem.degOkFrom, (denseCsDegFrom ..).2, (denseBiDegFrom ..).2,
    out.withinDegreeB_eq_all b]

/-- The dense degree check equals the spec degree check on the decoded system. -/
theorem VarRegistry.decodeCS_withinDegreeB (r : VarRegistry) (d : DenseConstraintSystem p)
    (b : DegreeBound) : (r.decodeCS d).withinDegreeB b = d.withinDegreeB b := by
  simp only [Circuit.withinDegreeB, DenseConstraintSystem.withinDegreeB,
    VarRegistry.decodeCS, VarRegistry.decodeBI, List.all_map, Function.comp_def,
    r.decodeExpr_degree]

/-! ## Distinct-variable count correspondence -/

/-- The variable-occurrence list of a dense system (constraints then interactions), matching the
    order `Circuit.varCount` folds over. -/
def DenseConstraintSystem.occ (d : DenseConstraintSystem p) : List VarId :=
  d.algebraicConstraints.flatMap DenseExpr.vars ++ d.busInteractions.flatMap denseBIVars

/-- Distinct variables of a dense system, via a `HashSet VarId` (linear; mirrors
    `Circuit.varCount`). -/
def DenseConstraintSystem.varCount (d : DenseConstraintSystem p) : Nat :=
  (d.occ.foldl (·.insert ·) (∅ : Std.HashSet VarId)).size

/-- HashSet distinct-count is invariant under the injective `resolve` relabeling: folding valid IDs
    and their resolutions into hash sets yields equal sizes. -/
private theorem size_fold_map_resolve (r : VarRegistry) :
    ∀ (l : List VarId) (sI : Std.HashSet VarId) (sV : Std.HashSet Variable),
      (∀ j, r.Valid j → (j ∈ sI ↔ r.resolve j ∈ sV)) → sI.size = sV.size →
      (∀ i ∈ l, r.Valid i) →
      ((l.map r.resolve).foldl (·.insert ·) sV).size = (l.foldl (·.insert ·) sI).size
  | [], sI, sV, _, hsize, _ => by simp [hsize]
  | i :: rest, sI, sV, hmem, hsize, hv => by
      have hvi : r.Valid i := hv i (List.mem_cons_self ..)
      simp only [List.map_cons, List.foldl_cons]
      apply size_fold_map_resolve r rest (sI.insert i) (sV.insert (r.resolve i))
      · intro j hj
        simp only [Std.HashSet.mem_insert, beq_iff_eq]
        constructor
        · rintro (rfl | hin)
          · exact Or.inl rfl
          · exact Or.inr ((hmem j hj).mp hin)
        · rintro (heq | hin)
          · exact Or.inl (r.resolve_inj hvi hj heq)
          · exact Or.inr ((hmem j hj).mpr hin)
      · rw [Std.HashSet.size_insert, Std.HashSet.size_insert]
        have hiff := hmem i hvi
        by_cases h : i ∈ sI
        · rw [if_pos h, if_pos (hiff.mp h), hsize]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), hsize]
      · exact fun i' hi' => hv i' (List.mem_cons_of_mem _ hi')

/-- The occurrence list of a decoded system is the dense occurrence list, resolved elementwise. -/
theorem VarRegistry.decodeCS_occ (r : VarRegistry) (d : DenseConstraintSystem p) :
    (r.decodeCS d).algebraicConstraints.flatMap Expression.vars ++
        (r.decodeCS d).busInteractions.flatMap BusInteraction.vars
      = d.occ.map r.resolve := by
  simp only [VarRegistry.decodeCS, DenseConstraintSystem.occ, List.map_append]
  congr 1
  · rw [List.flatMap_map, List.map_flatMap]
    simp only [r.decodeExpr_vars]
  · rw [List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr (fun bi _ => ?_)
    simp only [VarRegistry.decodeBI, BusInteraction.vars, denseBIVars, List.map_append,
      List.map_flatMap, List.flatMap_map, r.decodeExpr_vars]

/-- Every occurrence of a covered dense system is a valid ID. -/
theorem DenseConstraintSystem.occ_valid {r : VarRegistry} {d : DenseConstraintSystem p}
    (hc : d.CoveredBy r) : ∀ i ∈ d.occ, r.Valid i := by
  obtain ⟨hac, hbi⟩ := hc
  intro i hi
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
  rcases hi with ⟨e, he, hie⟩ | ⟨bi, hbimem, hib⟩
  · exact hac e he i hie
  · obtain ⟨hm, hp⟩ := hbi bi hbimem
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hib
    rcases hib with him | ⟨e, hemem, hie⟩
    · exact hm i him
    · exact hp e hemem i hie

/-! ## The dense lexicographic size key -/

/-- The dense lexicographic size key `(distinct vars, bus interactions, constraints)`. -/
def DenseConstraintSystem.sizeKey (d : DenseConstraintSystem p) : Nat ×ₗ Nat ×ₗ Nat :=
  toLex (d.varCount, toLex (d.busInteractions.length, d.algebraicConstraints.length))

end ApcOptimizer.Dense
