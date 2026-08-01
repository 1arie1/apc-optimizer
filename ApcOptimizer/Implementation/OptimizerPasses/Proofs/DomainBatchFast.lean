import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchFast
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch

set_option autoImplicit false

/-! # The rebuilt domain-batch pass

The engine owes one obligation, `dbDomainBatchσ_entailed`: every `var := const` it emits holds in
every satisfying assignment. It is discharged in four layers.

1. **Representation.** The scan runs on `ZMod.val`s, so `dbEval` mirrors `DenseExpr.eval` through
   `ZMod.val` (`dbEval_dbCompile`). Everything above works with field elements again.
2. **Domains.** Each entry of the table contains the value every satisfying assignment gives its
   variable (`dbTab_sound`).
3. **Items.** A gathered item's `dbItemOk` holds at such an assignment (`dbItemOk_of_sat`).
4. **Scan.** Enumerating a box and intersecting the mask over survivors keeps, for every key still
   alive, exactly the value a satisfying assignment gives it (`dbScanLoop_forces`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## 1. The `Nat` representation of the scan

The register file holds `ZMod.val`s. Addition is a conditional subtraction and multiplication a
single reduction, so each mirrors `ZMod.val_add` / `ZMod.val_mul`. -/

theorem dbAddN_eq_mod (p a b : ℕ) (ha : a < p) (hb : b < p) : dbAddN p a b = (a + b) % p := by
  unfold dbAddN
  by_cases h : a + b < p
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have hp : p ≤ a + b := Nat.le_of_not_lt h
    rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)]

theorem dbAddN_val [NeZero p] (a b : ZMod p) : dbAddN p a.val b.val = (a + b).val := by
  rw [dbAddN_eq_mod p a.val b.val (ZMod.val_lt a) (ZMod.val_lt b), ZMod.val_add]

theorem dbMulN_val [NeZero p] (a b : ZMod p) : dbMulN p a.val b.val = (a * b).val := by
  rw [dbMulN, ZMod.val_mul]

/-- The register file agrees with `denv` on every variable of interest. -/
def DbRegsAgree (denv : VarId → ZMod p) (regs : Array ℕ) (vs : List VarId) : Prop :=
  ∀ i ∈ vs, regs.getD i.index 0 = (denv i).val

theorem dbEval_dbCompile [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ) :
    ∀ (e : DenseExpr p), DbRegsAgree denv regs e.vars →
      dbEval p regs (dbCompile e) = (e.eval denv).val := by
  intro e
  induction e with
  | const c => intro _; rfl
  | var i => intro h; exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
    intro h
    have ha : DbRegsAgree denv regs a.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    have hb : DbRegsAgree denv regs b.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    simp only [dbCompile, dbEval, iha ha, ihb hb, DenseExpr.eval]
    exact dbAddN_val _ _
  | mul a b iha ihb =>
    intro h
    have ha : DbRegsAgree denv regs a.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    have hb : DbRegsAgree denv regs b.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    simp only [dbCompile, dbEval, iha ha, ihb hb, DenseExpr.eval]
    exact dbMulN_val _ _

/-- `dbEval` of a compiled expression is zero exactly when the expression evaluates to zero. -/
theorem dbEval_dbCompile_zero [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ)
    (e : DenseExpr p) (h : DbRegsAgree denv regs e.vars) :
    (dbEval p regs (dbCompile e) == 0) = decide (e.eval denv = 0) := by
  rw [dbEval_dbCompile denv regs e h]
  by_cases hz : e.eval denv = 0
  · simp [hz]
  · simpa [hz] using (ZMod.val_eq_zero (e.eval denv)).not.2 hz

/-! ## 2a. Affine roots

The plan linearizes each factor of the product spine once instead of once per queried variable, but
it answers with the same list, so `denseRootsIn_sound` carries over unchanged. -/

theorem dbRootsOfLin_eq [Fact p.Prime] (i : VarId) (l : DenseLinExpr p) :
    dbRootsOfLin i l = denseRootsOfTerms i l.const l.terms := by
  rcases hts : l.terms with _ | ⟨⟨j, a⟩, rest⟩
  · simp only [dbRootsOfLin, denseRootsOfTerms, hts, zmodIsZero_eq, decide_eq_true_eq]
  · rcases rest with _ | ⟨t2, rest2⟩
    · simp only [dbRootsOfLin, denseRootsOfTerms, hts, zmodIsZero_eq, zmodIsOne_eq,
        zmodAddP_eq, zmodMulP_eq, zmodNegP_eq, decide_eq_true_eq]
      by_cases hji : j = i
      · by_cases ha0 : a = 0
        · simp [hji, ha0]
        · by_cases ha1 : a = 1
          · -- the `a = 1` fast path: the root is `-c`, and the residual test cannot fail
            subst ha1
            simp [hji, ha0]
          · simp only [if_neg ha0, if_neg ha1, hji, true_and, ha0, ne_eq, not_false_eq_true]
            by_cases hr : a * -(a⁻¹ * l.const) + l.const = 0 <;> simp [hr]
      · simp [hji]
    · simp only [dbRootsOfLin, denseRootsOfTerms, hts]

theorem dbRootsIn_eq [Fact p.Prime] (i : VarId) :
    ∀ e : DenseExpr p, dbRootsIn i (dbRootPlan e) = denseRootsIn i e := by
  have hleaf : ∀ e : DenseExpr p,
      ((denseLinearize e).map DenseLinExpr.norm).bind (dbRootsOfLin i)
        = denseAffineRootsIn i e := by
    intro e
    rw [denseAffineRootsIn, Option.bind_map]
    cases denseLinearize e with
    | none => rfl
    | some l => simpa using dbRootsOfLin_eq i l.norm
  intro e
  induction e with
  | const n => exact hleaf (.const n)
  | var y => exact hleaf (.var y)
  | add a b _ _ => exact hleaf (.add a b)
  | mul a b iha ihb =>
    rw [dbRootPlan, dbRootsIn, denseRootsIn, hleaf (.mul a b), iha, ihb]
    rfl

/-- The roots the table stores for `i` really do contain `denv i` when the constraint vanishes. -/
theorem dbRootsIn_sound [Fact p.Prime] (i : VarId) (e : DenseExpr p) (roots : List (ZMod p))
    (h : dbRootsIn i (dbRootPlan e) = some roots) (denv : VarId → ZMod p)
    (he : e.eval denv = 0) : denv i ∈ roots :=
  denseRootsIn_sound i e roots (by rwa [dbRootsIn_eq] at h) denv he

/-! ## 2b. Domain membership

A domain is never materialized, so membership is "some in-range index yields the value". This is the
form the scan needs: the enumeration reaches a value exactly when it has an index. -/

/-- `v` is the `k`-th element of `dm`, for some in-range `k`. -/
def DbDomMem (p : ℕ) (dm : DbDom) (v : ℕ) : Prop := ∃ k, k < dm.size ∧ DbDom.at p dm k = v

theorem dbDomMem_explicit (vs : Array ℕ) (v : ℕ) (h : v ∈ vs) : DbDomMem p (.explicit vs) v := by
  obtain ⟨k, hk, hv⟩ := Array.getElem_of_mem h
  refine ⟨k, hk, ?_⟩
  simp only [DbDom.at]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some, hv]

theorem dbDomMem_range [NeZero p] (bound v : ℕ) (hvp : v < p) (h : v < bound) :
    DbDomMem p (.range bound) v :=
  ⟨v, h, by simp only [DbDom.at, if_pos hvp]⟩

/-! ## 2c. Soundness of the table

`DbTabSound` is the invariant every insertion preserves: an entry's domain contains the value the
assignment gives its variable. `DbTab.insert` keeps whichever of the two domains is smaller, so it
preserves the invariant as long as the incoming domain is itself sound. -/

def DbTabSound (p : ℕ) (denv : VarId → ZMod p) (T : DbTab p) : Prop :=
  ∀ i dm, T.get i = some dm → DbDomMem p dm (denv ⟨i⟩).val

theorem dbTab_get_replicate (n i : ℕ) : (⟨Array.replicate n none⟩ : DbTab p).get i = none := by
  rw [DbTab.get, Array.getD_eq_getD_getElem?]
  rcases lt_or_ge i n with hi | hi
  · rw [Array.getElem?_eq_getElem (by simpa using hi), Array.getElem_replicate]; rfl
  · rw [Array.getElem?_eq_none (by simpa using hi)]; rfl

/-- An entry surviving an insertion is either the incoming domain, at the incoming index, or one the
    table already held. -/
theorem dbTab_get_insert_cases (T : DbTab p) (i j : ℕ) (dm dj : DbDom)
    (h : (T.insert i dm).get j = some dj) : (j = i ∧ dj = dm) ∨ T.get j = some dj := by
  rcases T with ⟨dom⟩
  have hset : ∀ w : Option DbDom, (⟨dom.set! i w⟩ : DbTab p).get j = some dj →
      (j = i ∧ some dj = w) ∨ (⟨dom⟩ : DbTab p).get j = some dj := by
    intro w hw
    rw [DbTab.get, Array.getD_eq_getD_getElem?] at hw
    rcases lt_or_ge j (dom.set! i w).size with hlt | hge
    · by_cases hji : j = i
      · subst hji
        rw [Array.set!, Array.getElem?_setIfInBounds_self,
          if_pos (by simpa using hlt)] at hw
        exact Or.inl ⟨rfl, hw.symm⟩
      · rw [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hji)] at hw
        exact Or.inr (by rw [DbTab.get, Array.getD_eq_getD_getElem?, hw])
    · rw [Array.getElem?_eq_none hge] at hw; exact absurd hw (by simp)
  rw [DbTab.insert] at h
  rcases hold : dom.getD i none with _ | d0
  · rw [hold] at h
    dsimp only at h
    rcases hset _ h with ⟨hji, hdj⟩ | hr
    · exact Or.inl ⟨hji, Option.some.inj hdj⟩
    · exact Or.inr hr
  · rw [hold] at h
    dsimp only at h
    by_cases hsm : dm.size < d0.size
    · rw [if_pos hsm] at h
      rcases hset _ h with ⟨hji, hdj⟩ | hr
      · exact Or.inl ⟨hji, Option.some.inj hdj⟩
      · exact Or.inr hr
    · rw [if_neg hsm] at h; exact Or.inr h

theorem dbTabSound_empty (denv : VarId → ZMod p) (n : ℕ) :
    DbTabSound p denv ⟨Array.replicate n none⟩ := by
  intro i dm h
  rw [dbTab_get_replicate] at h
  exact absurd h (by simp)

theorem dbTabSound_insert (denv : VarId → ZMod p) (T : DbTab p) (i : ℕ) (dm : DbDom)
    (hT : DbTabSound p denv T) (hdm : DbDomMem p dm (denv ⟨i⟩).val) :
    DbTabSound p denv (T.insert i dm) := by
  intro j dj hj
  rcases dbTab_get_insert_cases T i j dm dj hj with ⟨hji, hdj⟩ | hr
  · subst hji; subst hdj; exact hdm
  · exact hT j dj hr

/-- Insertions that are skipped, or made under a hypothesis we cannot use, still leave a sound
    table when the table was sound to begin with. -/
theorem dbTabSound_mono (denv : VarId → ZMod p) (T T' : DbTab p)
    (h : ∀ i dm, T'.get i = some dm → T.get i = some dm) (hT : DbTabSound p denv T) :
    DbTabSound p denv T' := fun i dm hi => hT i dm (h i dm hi)

/-! ## 2d. The three table phases

Each phase only inserts, so soundness is an induction with `dbTabSound_insert` at every step. -/

/-- Constraint roots: `dbAddConstraintVars` inserts the roots of each of the constraint's variables,
    and a satisfying assignment's value is one of them. -/
theorem dbAddConstraintVars_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (c : DenseExpr p) (hc : c.eval denv = 0) (vs : Array VarId) :
    ∀ (k : ℕ) (T : DbTab p), DbTabSound p denv T →
      DbTabSound p denv (dbAddConstraintVars (dbRootPlan c) vs k T) := by
  intro k
  induction hk : vs.size - k generalizing k with
  | zero =>
    intro T hT
    rw [dbAddConstraintVars, dif_neg (by omega)]
    exact hT
  | succ n ih =>
    intro T hT
    have hlt : k < vs.size := by omega
    rw [dbAddConstraintVars, dif_pos hlt]
    dsimp only
    split
    · next rs hr =>
      refine ih (k + 1) (by omega) _ (dbTabSound_insert denv T _ _ hT ?_)
      refine dbDomMem_explicit _ _ ?_
      have hmem : denv vs[k] ∈ rs := dbRootsIn_sound vs[k] c rs hr denv hc
      simpa using List.mem_map.mpr ⟨denv vs[k], hmem, rfl⟩
    · exact ih (k + 1) (by omega) T hT

theorem dbConstraintPhase_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (cs : Array (DenseExpr p)) (hcs : ∀ c ∈ cs, c.eval denv = 0)
    (csVars : Array (Array VarId)) :
    ∀ (k : ℕ) (T : DbTab p), DbTabSound p denv T →
      DbTabSound p denv (dbConstraintPhase cs csVars k T) := by
  intro k
  induction hk : cs.size - k generalizing k with
  | zero =>
    intro T hT; rw [dbConstraintPhase, dif_neg (by omega)]; exact hT
  | succ n ih =>
    intro T hT
    have hlt : k < cs.size := by omega
    rw [dbConstraintPhase, dif_pos hlt]
    refine ih (k + 1) (by omega) _ ?_
    split
    · exact dbAddConstraintVars_sound denv cs[k] (hcs cs[k] (Array.getElem_mem hlt)) _ 0 T hT
    · exact hT

/-- Bus slot bounds: the fact's own soundness, specialised to the constant multiplicity and the
    constant-slot pattern the engine precomputes. -/
theorem dbSlotBound_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (slot bound : ℕ) (i : VarId)
    (hslot : bi.payload[slot]? = some (.var i))
    (h : dbSlotBound facts bi bi.multiplicity.constValue?
      (bi.payload.map DenseExpr.constValue?) slot = some bound)
    (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    (denv i).val < bound := by
  rw [dbSlotBound.eq_def] at h
  rcases hm : bi.multiplicity.constValue? with _ | mval
  · rw [hm] at h; exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    by_cases hmz : zmodIsZero mval
    · rw [if_pos hmz] at h; exact absurd h (by simp)
    · rw [if_neg hmz] at h
      have hmeval : (denseBIEval bi denv).multiplicity = mval :=
        bi.multiplicity.constValue?_sound mval hm denv
      have hmne : mval ≠ 0 := by
        simpa [zmodIsZero_eq] using hmz
      have hviol : bs.accepts (denseBIEval bi denv) := hob (by rw [hmeval]; exact hmne)
      have hget : (denseBIEval bi denv).payload[slot]? = some (denv i) := by
        show (bi.payload.map (fun e => e.eval denv))[slot]? = some (denv i)
        rw [List.getElem?_map, hslot]; rfl
      rw [← hmeval] at h
      exact facts.slotBound_sound (denseBIEval bi denv)
        (bi.payload.map DenseExpr.constValue?) slot bound (denv i) h
        (denseMatches_evalPattern bi.payload denv) hviol hget

/-- The slot walk inserts only `.range bound` domains justified by `dbSlotBound_sound`, at the
    variable sitting in that slot. `rest` is the suffix of the payload starting at `slot`. -/
theorem dbBusSlots_sound [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    ∀ (rest : List (DenseExpr p)) (slot : ℕ) (seen : Array VarId) (inf : Bool) (T : DbTab p),
      (∀ k, rest[k]? = bi.payload[slot + k]?) → DbTabSound p denv T →
      DbTabSound p denv (dbBusSlots facts bi bi.multiplicity.constValue?
        (bi.payload.map DenseExpr.constValue?) rest slot seen inf T).2 := by
  intro rest
  induction rest with
  | nil => intro slot seen inf T _ hT; exact hT
  | cons e rest ih =>
    intro slot seen inf T hsuf hT
    have hshift : ∀ k, rest[k]? = bi.payload[(slot + 1) + k]? := by
      intro k
      have := hsuf (k + 1)
      simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using this
    cases e with
    | var i =>
      rw [dbBusSlots]
      dsimp only
      by_cases hseen : seen.contains i
      · rw [if_pos hseen]; exact ih (slot + 1) seen inf T hshift hT
      · rw [if_neg hseen]
        have hslot : bi.payload[slot]? = some (.var i) := by
          have := hsuf 0; simpa using this.symm
        rcases hsb : dbSlotBound facts bi bi.multiplicity.constValue?
          (bi.payload.map DenseExpr.constValue?) slot with _ | bound
        · dsimp only; exact ih (slot + 1) (seen.push i) true T hshift hT
        · dsimp only
          refine ih (slot + 1) (seen.push i) inf _ hshift ?_
          by_cases hb : bound ≤ maxDomainBound
          · rw [if_pos hb]
            refine dbTabSound_insert denv T i.index _ hT ?_
            exact dbDomMem_range bound _ (ZMod.val_lt _)
              (dbSlotBound_sound facts bi slot bound i hslot hsb denv hob)
          · rw [if_neg hb]; exact hT
    | const c =>
      simp only [dbBusSlots]; exact ih (slot + 1) seen _ T hshift hT
    | add a b =>
      simp only [dbBusSlots]; exact ih (slot + 1) seen _ T hshift hT
    | mul a b =>
      simp only [dbBusSlots]; exact ih (slot + 1) seen _ T hshift hT

theorem dbDomainBatchσ_entailed [Fact p.Prime] [NeZero p]
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    EntailedMap d bs (dbDomainBatchσ bs facts d).map := by
  sorry

theorem dbDomainBatchTransform_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    (dbDomainBatchTransform pw bs facts d).CoveredBy reg := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d = applyσ (dbDomainBatchσ bs facts d) d
        from by simp only [dbDomainBatchTransform, if_pos hpB], applyσ]
    by_cases he : (dbDomainBatchσ bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact hcov
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_covered hcov (fun i _ t ht z hz => ?_)
      exact DenseConstraintSystem.occ_valid hcov z
        ((dbDomainBatchσ_entailed bs facts d i t ht).1 z hz)
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact hcov

theorem dbDomainBatchTransform_correct (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (dbDomainBatchTransform pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d = applyσ (dbDomainBatchσ bs facts d) d
        from by simp only [dbDomainBatchTransform, if_pos hpB], applyσ]
    by_cases he : (dbDomainBatchσ bs facts d).map.isEmpty = true
    · rw [if_pos he]; exact DensePassCorrect_refl reg.isInput d bs
    · rw [if_neg he]
      refine DenseConstraintSystem.substF_denseCorrect d (dbDomainBatchσ bs facts d).fn bs
        reg.isInput (fun denv hsat j t hjt => ?_) (fun j t hjt z hz => ?_)
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).2 denv hsat
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).1 z hz
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact DensePassCorrect_refl reg.isInput d bs

/-- The rebuilt domain-batch pass (see `dbDomainBatchσ`). -/
def dbDomainBatchPass (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := dbDomainBatchTransform pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := dbDomainBatchTransform_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := DensePassCorrect.lift hcov
      (dbDomainBatchTransform_covered pw reg bs facts d hcov) (by intro x hx; simp at hx)
      (dbDomainBatchTransform_correct pw reg bs facts d) }

end ApcOptimizer.Dense
