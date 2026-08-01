import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ByteCheckPack

set_option autoImplicit false

/-! # Correctness of the `domainBatch` pass

The pass owes one obligation, `dbDomainBatchσ_entailed`: every `var := const` it emits holds in
every satisfying assignment. It is discharged in five layers.

1. **Representation.** The scan runs on `ZMod.val`s, so `dbEval` mirrors `DenseExpr.eval` through
   `ZMod.val` (`dbEval_dbCompile`). Everything above works with field elements again.
2. **Domains.** Each entry of the table contains the value every satisfying assignment gives its
   variable (`DbTabSound`, established phase by phase).
3. **Items.** A gathered item's `dbItemOk` holds at such an assignment (`dbCompileBi_ok`).
4. **Scan.** Enumerating a box and intersecting the mask over survivors keeps, for every key still
   alive, exactly the value a satisfying assignment gives it (`dbScanLoop_reach`).
5. **Assembly.** The context is sound (`dbBuildCtx_good`), so each preflighted plan answers soundly
   (`dbPreflight_sound`) and the run's forced lists fold into an entailed solution map. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

universe u v

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
  · simp [hz]

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
          · simp only [if_neg ha1, hji, true_and, ha0, ne_eq, not_false_eq_true]
            by_cases hr : a * -(a⁻¹ * l.const) + l.const = 0 <;> simp
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

/-! ### Byte-operand domains

A byte operand's domain is the `bound`-element coset `{(v + negB) * aInv}`, streamed rather than
materialized, with `negB` and `aInv` stored as `val`s. -/

theorem dbDom_at_coset [NeZero p] (bound negB aInv k : ℕ) :
    DbDom.at p (.coset bound negB aInv) k = dbMulN p (dbAddN p (k % p) negB) aInv := by
  simp only [DbDom.at]
  by_cases hk : k < p
  · rw [if_pos hk, Nat.mod_eq_of_lt hk]
  · rw [if_neg hk]

theorem dbDomMem_coset [NeZero p] (bound : ℕ) (b ainv : ZMod p) (v : ZMod p) (k : ℕ)
    (hk : k < bound) (hv : v = ((k : ZMod p) - b) * ainv) :
    DbDomMem p (.coset bound (zmodNegP b).val ainv.val) v.val := by
  refine ⟨k, hk, ?_⟩
  rw [dbDom_at_coset, ← ZMod.val_natCast (n := p) k, dbAddN_val, dbMulN_val, hv,
    zmodNegP_eq, sub_eq_add_neg]

/-- `denseByteOperandCosetMem` as an index into the coset. -/
theorem dbByteOperand_cosetIndex [Fact p.Prime] [NeZero p] (e : DenseExpr p) (bound : ℕ)
    (x : VarId) (a b : ZMod p) (haff : denseAffineOfExpr e = some (x, a, b))
    (denv : VarId → ZMod p) (hbnd : (e.eval denv).val < bound) :
    ∃ k, k < bound ∧ denv x = ((k : ZMod p) - b) * a⁻¹ := by
  have hmem := denseByteOperandCosetMem e bound x a b haff denv hbnd
  rw [List.map_map, List.mem_map] at hmem
  obtain ⟨k, hk, hveq⟩ := hmem
  exact ⟨k, List.mem_range.mp hk, hveq.symm⟩

/-- An operand domain contains the value a satisfying assignment gives its variable, given the
    operand is below the byte bound. -/
theorem dbByteOperand_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (e : DenseExpr p) (bound i : ℕ) (dm : DbDom)
    (h : dbByteOperand e bound = some (i, dm))
    (hbnd : (e.eval denv).val < bound) : DbDomMem p dm (denv ⟨i⟩).val := by
  unfold dbByteOperand at h
  cases e with
  | var j =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dbDomMem_range bound _ (ZMod.val_lt _) hbnd
  | const c =>
    rcases haff : denseAffineOfExpr (.const c : DenseExpr p) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.const c) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq
  | add ea eb =>
    rcases haff : denseAffineOfExpr (.add ea eb) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.add ea eb) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq
  | mul ea eb =>
    rcases haff : denseAffineOfExpr (.mul ea eb) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.mul ea eb) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq

/-! ### Linking a precomputed view to its interaction

`DbBiPre` caches the `BusFacts` answers for one interaction; these say the cache is faithful. -/

def DbBytePreOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (b : DbBytePre p) : Prop :=
  facts.byteXorSpec bi.busId = some b.spec ∧
    ∃ op, b.spec.decode bi.payload = some (op, b.o1, b.o2, b.result) ∧ b.op? = op.constValue?

def DbBiPreOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : Prop :=
  e.mult? = bi.multiplicity.constValue? ∧ e.pat = bi.payload.map DenseExpr.constValue? ∧
    (∀ b, e.byte? = some b → DbBytePreOf facts bi b) ∧
    (e.varRange = true → facts.varRangeBus bi.busId = true) ∧
    (∀ t, e.tuple? = some t → facts.tupleRangeBus bi.busId = some t) ∧
    (∀ t, e.rangeAt? = some t → facts.rangeCheckAt bi.busId e.pat = some t)

theorem dbAddByteOperand_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (e : DenseExpr p) (bound : ℕ) (T : DbTab p) (hT : DbTabSound p denv T)
    (hbnd : (e.eval denv).val < bound) : DbTabSound p denv (dbAddByteOperand e bound T) := by
  unfold dbAddByteOperand
  rcases hv : dbByteOperandVar e with _ | i
  · exact hT
  · dsimp only
    rcases hg : T.get i with _ | d0
    · exact hT
    · dsimp only
      by_cases hlt : bound < d0.size
      · rw [if_pos hlt]
        rcases hbo : dbByteOperand e bound with _ | ⟨i', dm⟩
        · exact hT
        · dsimp only
          exact dbTabSound_insert denv T i' dm hT
            (dbByteOperand_sound denv e bound i' dm hbo hbnd)
      · rw [if_neg hlt]; exact hT

theorem dbAddByteBi_sound [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (T : DbTab p) (hT : DbTabSound p denv T) : DbTabSound p denv (dbAddByteBi e T) := by
  obtain ⟨hmult, _, hbyte, _, _, _⟩ := hpre
  rw [dbAddByteBi]
  rcases hm : e.mult? with _ | mult
  · exact hT
  · dsimp only
    by_cases hmz : zmodIsZero mult
    · rw [if_pos hmz]; exact hT
    · rw [if_neg hmz]
      rcases hb : e.byte? with _ | b
      · exact hT
      · dsimp only
        rcases hop : b.op? with _ | opv
        · exact hT
        · dsimp only
          by_cases hbnds : denseByteOpBounds b.spec opv
          · rw [if_pos hbnds]
            obtain ⟨hspec, op, hdec, hopc⟩ := hbyte b hb
            have hmz' : mult ≠ 0 := by simpa [zmodIsZero_eq] using hmz
            obtain ⟨h1, h2⟩ := denseByteOperandBound bs facts bi denv mult
              (by rw [← hmult, hm]) hmz' b.spec hspec op b.o1 b.o2 b.result hdec opv
              (by rw [← hopc, hop]) hbnds hob
            exact dbAddByteOperand_sound denv b.o2 b.spec.bound _
              (dbAddByteOperand_sound denv b.o1 b.spec.bound T hT h1) h2
          · rw [if_neg hbnds]; exact hT

theorem dbBytePhase_sound [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (pre : Array (DbBiPre p))
    (hpre : ∀ k, ∀ hk : k < pre.size, ∃ bi, DbBiPreOf facts bi pre[k] ∧
      ((denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))) :
    ∀ (k : ℕ) (T : DbTab p), DbTabSound p denv T →
      DbTabSound p denv (dbBytePhase pre k T) := by
  intro k
  induction hk : pre.size - k generalizing k with
  | zero => intro T hT; rw [dbBytePhase, dif_neg (by omega)]; exact hT
  | succ n ih =>
    intro T hT
    have hlt : k < pre.size := by omega
    rw [dbBytePhase, dif_pos hlt]
    obtain ⟨bi, hbi, hob⟩ := hpre k hlt
    exact ih (k + 1) (by omega) _ (dbAddByteBi_sound facts bi pre[k] hbi denv hob T hT)

theorem dbBusPhase_sound [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (bis : Array (BusInteraction (DenseExpr p)))
    (pre : Array (DbBiPre p))
    (hpre : ∀ k, ∀ hk : k < bis.size, DbBiPreOf facts bis[k] (pre.getD k dbBiPreEmpty) ∧
      ((denseBIEval bis[k] denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bis[k] denv))) :
    ∀ (k : ℕ) (st : DbTab p × Array Bool), DbTabSound p denv st.1 →
      DbTabSound p denv (dbBusPhase facts bis pre k st).1 := by
  intro k
  induction hk : bis.size - k generalizing k with
  | zero => intro st hT; rw [dbBusPhase, dif_neg (by omega)]; exact hT
  | succ n ih =>
    intro st hT
    have hlt : k < bis.size := by omega
    rw [dbBusPhase, dif_pos hlt]
    obtain ⟨⟨hmult, hpat, _, _, _, _⟩, hob⟩ := hpre k hlt
    refine ih (k + 1) (by omega) _ ?_
    dsimp only
    rw [hmult, hpat]
    exact dbBusSlots_sound facts bis[k] denv hob bis[k].payload 0 #[] false st.1
      (fun m => by simp) hT

/-! ## 3. Items

A gathered item's obligation holds at a satisfying assignment. Only this direction is needed: the
mask is an intersection over *survivors*, so it suffices that the assignment's own point survives. -/

theorem zmodOfNatP_eq [NeZero p] (n : ℕ) : zmodOfNatP p n = (n : ZMod p) := by
  cases p with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m =>
    refine ZMod.val_injective (m + 1) ?_
    rw [ZMod.val_natCast]
    rfl

theorem zmodOfNatP_val [NeZero p] (x : ZMod p) : zmodOfNatP p x.val = x := by
  rw [zmodOfNatP_eq, ZMod.natCast_val, ZMod.cast_id]

/-- Agreement on a bus interaction's variables restricts to each of its expressions. -/
theorem dbRegsAgree_mult (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgree denv regs (denseBIVars bi)) :
    DbRegsAgree denv regs bi.multiplicity.vars := fun i hi =>
  h i (by rw [denseBIVars]; exact List.mem_append_left _ hi)

theorem dbRegsAgree_payload (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgree denv regs (denseBIVars bi))
    (x : DenseExpr p) (hx : x ∈ bi.payload) : DbRegsAgree denv regs x.vars := fun i hi =>
  h i (by
    rw [denseBIVars]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hi⟩))

/-- The evaluated message of `bi`, spelled out. -/
theorem denseBIEval_mk (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    denseBIEval bi denv =
      { busId := bi.busId, multiplicity := bi.multiplicity.eval denv,
        payload := bi.payload.map (fun e => e.eval denv) } := rfl

section Items
variable {bs : BusSemantics p}

/-- The evaluated payload of the fallback message is the interaction's own evaluated payload. -/
theorem dbFallback_payload [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (hagree : DbRegsAgree denv regs (denseBIVars bi)) :
    (bi.payload.map dbCompile).map (fun t => zmodOfNatP p (dbEval p regs t))
      = bi.payload.map (fun ex => ex.eval denv) := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro x hx
  simp only [Function.comp_apply]
  rw [dbEval_dbCompile denv regs x (dbRegsAgree_payload denv regs bi hagree x hx),
    zmodOfNatP_val]

theorem dbFallback_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs
      (.fallback bi.busId (dbCompile bi.multiplicity) (bi.payload.map dbCompile)) = true := by
  have hmv : dbEval p regs (dbCompile bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_dbCompile denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  simp only [dbItemOk]
  by_cases hz : dbEval p regs (dbCompile bi.multiplicity) = 0
  · simp [hz]
  · have hne : bi.multiplicity.eval denv ≠ 0 := by
      intro h0; exact hz (by rw [hmv, h0, ZMod.val_zero])
    have hmsg : (⟨bi.busId, zmodOfNatP p (dbEval p regs (dbCompile bi.multiplicity)),
        (bi.payload.map dbCompile).map (fun t => zmodOfNatP p (dbEval p regs t))⟩ :
          BusInteraction (ZMod p)) = denseBIEval bi denv := by
      rw [denseBIEval_mk, hmv, zmodOfNatP_val, dbFallback_payload denv regs bi hagree]
    simp only [beq_iff_eq, hz, if_false]
    rw [hmsg]
    exact (facts.acceptsDec_iff _).mpr (hob (by rw [denseBIEval_mk]; exact hne))

theorem dbCompileRange_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (item : DbItem) (h : dbCompileRange bi e (dbCompile bi.multiplicity) = some item) :
    dbItemOk facts regs item = true := by
  obtain ⟨hmult?, hpat, _, _, _, hra⟩ := hpre
  rw [dbCompileRange] at h
  rcases hm : e.mult? with _ | m
  · rw [hm] at h; exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    by_cases hone : zmodIsOne m
    · rw [if_pos hone] at h
      rcases hr : e.rangeAt? with _ | ⟨slot, bound⟩
      · rw [hr] at h; exact absurd h (by simp)
      · rw [hr] at h
        dsimp only at h
        rcases hv : bi.payload[slot]? with _ | value
        · rw [hv] at h; exact absurd h (by simp)
        · rw [hv] at h
          simp only [Option.some.injEq] at h
          subst h
          have hm1 : m = 1 := by simpa [zmodIsOne_eq] using hone
          have hmc : bi.multiplicity.constValue? = some 1 := by rw [← hmult?, hm, hm1]
          have hmeval : bi.multiplicity.eval denv = 1 :=
            bi.multiplicity.constValue?_sound 1 hmc denv
          have hvmem : value ∈ bi.payload := List.mem_of_getElem? hv
          have hvv : dbEval p regs (dbCompile value) = (value.eval denv).val :=
            dbEval_dbCompile denv regs value (dbRegsAgree_payload denv regs bi hagree value hvmem)
          have hmv : dbEval p regs (dbCompile bi.multiplicity) = (bi.multiplicity.eval denv).val :=
            dbEval_dbCompile denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
          obtain ⟨_, hrc⟩ := facts.rangeCheckAt_sound bi.busId
            (bi.payload.map DenseExpr.constValue?) slot bound (by rw [← hpat]; exact hra _ hr)
          obtain ⟨_, hiff⟩ := hrc (denseBIEval bi denv) rfl (by rw [denseBIEval_mk]; exact hmeval)
            (denseMatches_evalPattern bi.payload denv)
          have hpl : (denseBIEval bi denv).payload[slot]? = some (value.eval denv) := by
            show (bi.payload.map (fun x => x.eval denv))[slot]? = _
            rw [List.getElem?_map, hv]; rfl
          have hacc : bs.accepts (denseBIEval bi denv) := by
            refine hob ?_
            rw [denseBIEval_mk, hmeval]; exact one_ne_zero
          simp only [dbItemOk, hvv, hmv, hmeval]
          by_cases hz : (1 : ZMod p).val = 0
          · simp [hz]
          · simp only [beq_iff_eq, hz, if_false, decide_eq_true_eq]
            exact (hiff (value.eval denv) hpl).mp hacc
    · rw [if_neg hone] at h; exact absurd h (by simp)

/-- The byte arm: bounds and the bitwise relation come from the spec's own soundness. -/
theorem dbByteItem_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (o1 o2 r : DenseExpr p) (h1m : o1 ∈ bi.payload) (h2m : o2 ∈ bi.payload)
    (hrm : r ∈ bi.payload) (bound : ℕ) (kind : DenseBytePredKind)
    (hrel : bs.accepts (denseBIEval bi denv) →
      (o1.eval denv).val < bound ∧ (o2.eval denv).val < bound ∧
        dbByteRel kind (o1.eval denv).val (o2.eval denv).val (r.eval denv).val = true) :
    dbItemOk facts regs (.byte (dbCompile bi.multiplicity) (dbCompile o1) (dbCompile o2)
      (dbCompile r) bound kind) = true := by
  have hmv : dbEval p regs (dbCompile bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_dbCompile denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  have e1 : dbEval p regs (dbCompile o1) = (o1.eval denv).val :=
    dbEval_dbCompile denv regs o1 (dbRegsAgree_payload denv regs bi hagree o1 h1m)
  have e2 : dbEval p regs (dbCompile o2) = (o2.eval denv).val :=
    dbEval_dbCompile denv regs o2 (dbRegsAgree_payload denv regs bi hagree o2 h2m)
  have er : dbEval p regs (dbCompile r) = (r.eval denv).val :=
    dbEval_dbCompile denv regs r (dbRegsAgree_payload denv regs bi hagree r hrm)
  simp only [dbItemOk, hmv, e1, e2, er]
  by_cases hz : (bi.multiplicity.eval denv).val = 0
  · simp [hz]
  · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
    obtain ⟨hb1, hb2, hrl⟩ := hrel (hob (by rw [denseBIEval_mk]; exact hne))
    simp [hz, hb1, hb2, hrl]

theorem dbCompileByte_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (e : DbBiPre p) (hpre : DbBiPreOf facts bi e) (denv : VarId → ZMod p) (regs : Array ℕ)
    (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (item : DbItem) (h : dbCompileByte e (dbCompile bi.multiplicity) = some item) :
    dbItemOk facts regs item = true := by
  obtain ⟨_, _, hbyte, _, _, _⟩ := hpre
  rw [dbCompileByte] at h
  rcases hb : e.byte? with _ | b
  · rw [hb] at h; exact absurd h (by simp)
  · rw [hb] at h
    dsimp only at h
    rcases hop : b.op? with _ | opv
    · rw [hop] at h; exact absurd h (by simp)
    · rw [hop] at h
      dsimp only at h
      obtain ⟨hspec, op, hdec, hopc⟩ := hbyte b hb
      obtain ⟨h1m, h2m, hrm⟩ := b.spec.decode_mem bi.payload op b.o1 b.o2 b.result hdec
      have hopeval : op.eval denv = opv := op.constValue?_sound opv (by rw [← hopc, hop]) denv
      obtain ⟨hxor, hpair⟩ :=
        denseByteXorSpec_decode_iff bs facts b.spec bi hspec op b.o1 b.o2 b.result hdec denv
      obtain ⟨hor, hand⟩ :=
        denseByteBoolSound_decode_iff bs facts b.spec bi hspec op b.o1 b.o2 b.result hdec denv
      have mk : ∀ kind, (bs.accepts (denseBIEval bi denv) →
          (b.o1.eval denv).val < b.spec.bound ∧ (b.o2.eval denv).val < b.spec.bound ∧
            dbByteRel kind (b.o1.eval denv).val (b.o2.eval denv).val
              (b.result.eval denv).val = true) →
          dbItemOk facts regs (.byte (dbCompile bi.multiplicity) (dbCompile b.o1)
            (dbCompile b.o2) (dbCompile b.result) b.spec.bound kind) = true :=
        fun kind hrel => dbByteItem_ok facts bi denv regs hagree hob b.o1 b.o2 b.result
          h1m h2m hrm b.spec.bound kind hrel
      by_cases hxo : opv = b.spec.xorOp
      · rw [if_pos hxo] at h
        simp only [Option.some.injEq] at h; subst h
        refine mk .xor (fun hacc => ?_)
        obtain ⟨u1, u2, u3⟩ := (hxor (by rw [hopeval, hxo])).mp hacc
        exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
      · rw [if_neg hxo] at h
        by_cases hpo : opv = b.spec.pairOp
        · rw [if_pos hpo] at h
          simp only [Option.some.injEq] at h; subst h
          refine mk .pair (fun hacc => ?_)
          obtain ⟨u1, u2, u3⟩ := (hpair (by rw [hopeval, hpo])).mp hacc
          exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
        · rw [if_neg hpo] at h
          rcases hoo : b.spec.orOp with _ | oop
          · rw [hoo] at h
            dsimp only at h
            rcases hao : b.spec.andOp with _ | aop
            · rw [hao] at h; exact absurd h (by simp)
            · rw [hao] at h
              dsimp only at h
              by_cases hae : opv = aop
              · rw [if_pos hae] at h
                simp only [Option.some.injEq] at h; subst h
                refine mk .and (fun hacc => ?_)
                obtain ⟨u1, u2, u3⟩ := (hand aop hao (by rw [hopeval, hae])).mp hacc
                exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
              · rw [if_neg hae] at h; exact absurd h (by simp)
          · rw [hoo] at h
            dsimp only at h
            by_cases hoe : opv = oop
            · rw [if_pos hoe] at h
              simp only [Option.some.injEq] at h; subst h
              refine mk .or (fun hacc => ?_)
              obtain ⟨u1, u2, u3⟩ := (hor oop hoo (by rw [hopeval, hoe])).mp hacc
              exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
            · rw [if_neg hoe] at h
              rcases hao : b.spec.andOp with _ | aop
              · rw [hao] at h; exact absurd h (by simp)
              · rw [hao] at h
                dsimp only at h
                by_cases hae : opv = aop
                · rw [if_pos hae] at h
                  simp only [Option.some.injEq] at h; subst h
                  refine mk .and (fun hacc => ?_)
                  obtain ⟨u1, u2, u3⟩ := (hand aop hao (by rw [hopeval, hae])).mp hacc
                  exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
                · rw [if_neg hae] at h; exact absurd h (by simp)

theorem dbCompileOther_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs (dbCompileOther bi e (dbCompile bi.multiplicity)) = true := by
  rw [dbCompileOther]
  rcases hr : dbCompileRange bi e (dbCompile bi.multiplicity) with _ | item
  · dsimp only
    rcases hb : dbCompileByte e (dbCompile bi.multiplicity) with _ | item2
    · exact dbFallback_ok facts bi denv regs hagree hob
    · exact dbCompileByte_ok facts bi e hpre denv regs hagree hob item2 hb
  · exact dbCompileRange_ok facts bi e hpre denv regs hagree hob item hr

theorem dbCompileBi_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs (dbCompileBi facts bi e) = true := by
  obtain ⟨_, _, _, hvrf, htuf, _⟩ := hpre
  have hmv : dbEval p regs (dbCompile bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_dbCompile denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  rw [dbCompileBi]
  by_cases hok : denseBiAlwaysOk facts bi
  · rw [if_pos hok]; rfl
  · rw [if_neg hok]
    dsimp only
    split
    · next x width heq =>
      have hx : x ∈ bi.payload := by rw [heq]; simp
      have hw : width ∈ bi.payload := by rw [heq]; simp
      have ex : dbEval p regs (dbCompile x) = (x.eval denv).val :=
        dbEval_dbCompile denv regs x (dbRegsAgree_payload denv regs bi hagree x hx)
      have ew : dbEval p regs (dbCompile width) = (width.eval denv).val :=
        dbEval_dbCompile denv regs width (dbRegsAgree_payload denv regs bi hagree width hw)
      have hmsg : denseBIEval bi denv =
          ⟨bi.busId, bi.multiplicity.eval denv, [x.eval denv, width.eval denv]⟩ := by
        rw [denseBIEval_mk, heq]; rfl
      by_cases hvr : e.varRange
      · rw [if_pos hvr]
        obtain ⟨_, hiff⟩ := facts.varRangeBus_sound bi.busId (hvrf hvr)
        have hkey : bi.multiplicity.eval denv ≠ 0 →
            (width.eval denv).val ≤ 17 ∧ (x.eval denv).val < 2 ^ (width.eval denv).val := by
          intro hne
          exact (hiff (x.eval denv) (width.eval denv) (bi.multiplicity.eval denv)).mp
            (by rw [← hmsg]; exact hob (by rw [hmsg]; exact hne))
        rcases hwc : width.constValue? with _ | widthValue
        · dsimp only
          simp only [dbItemOk, hmv, ex, ew]
          by_cases hz : (bi.multiplicity.eval denv).val = 0
          · simp [hz]
          · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
            obtain ⟨u1, u2⟩ := hkey hne
            simp [hz, u1, u2]
        · dsimp only
          have hweval : width.eval denv = widthValue := width.constValue?_sound _ hwc denv
          by_cases hle : widthValue.val ≤ 17
          · rw [if_pos hle]
            simp only [dbItemOk, hmv, ex]
            by_cases hz : (bi.multiplicity.eval denv).val = 0
            · simp [hz]
            · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
              obtain ⟨_, u2⟩ := hkey hne
              rw [hweval] at u2
              simp [hz, u2]
          · rw [if_neg hle]
            simp only [dbItemOk, hmv, ex, ew]
            by_cases hz : (bi.multiplicity.eval denv).val = 0
            · simp [hz]
            · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
              obtain ⟨u1, u2⟩ := hkey hne
              simp [hz, u1, u2]
      · rw [if_neg hvr]
        rcases ht : e.tuple? with _ | ⟨bx, byy⟩
        · dsimp only
          exact dbCompileOther_ok facts bi e ⟨‹_›, ‹_›, ‹_›, hvrf, htuf, ‹_›⟩ denv regs hagree hob
        · dsimp only
          obtain ⟨_, _, hiff⟩ := facts.tupleRangeBus_sound bi.busId bx byy (htuf _ ht)
          simp only [dbItemOk, hmv, ex, ew]
          by_cases hz : (bi.multiplicity.eval denv).val = 0
          · simp [hz]
          · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
            obtain ⟨u1, u2⟩ := (hiff (x.eval denv) (width.eval denv)
              (bi.multiplicity.eval denv)).mp (by rw [← hmsg]; exact hob (by rw [hmsg]; exact hne))
            simp [hz, u1, u2]
    · exact dbCompileOther_ok facts bi e ⟨‹_›, ‹_›, ‹_›, hvrf, htuf, ‹_›⟩ denv regs hagree hob

end Items

/-! ## 4. The scan

The mask is an intersection over surviving points, so the key facts are: absorbing *any* point can
only kill keys, and absorbing the assignment's own point makes every surviving key carry the
assignment's value. Reaching that point is an induction over the box dimensions. -/

/-- The register file carries the assignment's values on the target's keys. -/
def DbRegsAt (denv : VarId → ZMod p) (keys : Array ℕ) (regs : Array ℕ) : Prop :=
  ∀ d, d < keys.size → regs.getD (keys.getD d 0) 0 = (denv ⟨keys.getD d 0⟩).val

/-- Every key the mask still calls forced carries the assignment's value. -/
def DbMaskAgree (denv : VarId → ZMod p) (keys : Array ℕ) (st : DbScanSt) : Prop :=
  ∀ i, i < keys.size → st.alive.getD i false = true →
    st.vals.getD i 0 = (denv ⟨keys.getD i 0⟩).val

/-- What the scan must deliver: it started, and either nothing survives or the mask agrees. -/
def DbScanGood (denv : VarId → ZMod p) (keys : Array ℕ) (st : DbScanSt) : Prop :=
  st.started = true ∧ (st.live = 0 ∨ DbMaskAgree denv keys st)

theorem dbAbsorbGo_spec (regs keys vals : Array ℕ) :
    ∀ (m i live : ℕ) (alive : Array Bool), keys.size - i ≤ m →
      (dbAbsorbGo regs keys i vals alive live).1 = vals ∧
      (∀ j, (dbAbsorbGo regs keys i vals alive live).2.1.getD j false = true →
        alive.getD j false = true) ∧
      (∀ j, i ≤ j → j < keys.size →
        (dbAbsorbGo regs keys i vals alive live).2.1.getD j false = true →
        regs.getD (keys.getD j 0) 0 = vals.getD j 0) := by
  intro m
  induction m with
  | zero =>
    intro i live alive hm
    rw [dbAbsorbGo, dif_neg (by omega)]
    exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩
  | succ m ih =>
    intro i live alive hm
    by_cases hlt : i < keys.size
    · rw [dbAbsorbGo, dif_pos hlt]
      have hkey : keys.getD i 0 = keys[i] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]; rfl
      have hdead : ∀ (al : Array Bool), (al.set! i false).getD i false = false := by
        intro al
        rw [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_self]
        split <;> rfl
      have hne : ∀ (al : Array Bool) (j : ℕ), j ≠ i →
          (al.set! i false).getD j false = al.getD j false := by
        intro al j hji
        rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!,
          Array.getElem?_setIfInBounds_ne (Ne.symm hji)]
      by_cases hal : alive.getD i false
      · rw [if_pos hal]
        by_cases heq : regs.getD keys[i] 0 == vals.getD i 0
        · rw [if_pos heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
          refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact h3 j (by omega) hjs hjl
          · have : j = i := by omega
            subst this; rw [hkey]; simpa using heq
        · rw [if_neg heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) (live - 1) (alive.set! i false) (by omega)
          refine ⟨h1, fun j hjl => ?_, fun j hj hjs hjl => ?_⟩
          · have hj2 := h2 j hjl
            rcases Nat.decEq j i with hji | hji
            · rwa [hne alive j hji] at hj2
            · subst hji; rw [hdead alive] at hj2; exact absurd hj2 (by simp)
          · rcases Nat.lt_or_ge i j with hij | hij
            · exact h3 j (by omega) hjs hjl
            · have hji : j = i := by omega
              subst hji
              have hj2 := h2 j hjl
              rw [hdead alive] at hj2; exact absurd hj2 (by simp)
      · rw [if_neg hal]
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
        refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact h3 j (by omega) hjs hjl
        · have : j = i := by omega
          subst this
          exact absurd (h2 j hjl) (by simpa using hal)
    · rw [dbAbsorbGo, dif_neg hlt]
      exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩

theorem dbAbsorbArgs_true (keys regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) :
    dbAbsorbArgs keys regs vals alive live true =
      ((dbAbsorbGo regs keys 0 vals alive live).1, (dbAbsorbGo regs keys 0 vals alive live).2.1,
        (dbAbsorbGo regs keys 0 vals alive live).2.2, true) := by
  rw [dbAbsorbArgs]; simp

theorem dbAbsorbArgs_false (keys regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) :
    dbAbsorbArgs keys regs vals alive live false =
      (keys.map (fun k => regs.getD k 0), Array.replicate keys.size true, keys.size, true) := by
  rw [dbAbsorbArgs]; simp

theorem dbMap_getD (keys : Array ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < keys.size) :
    (keys.map f).getD j 0 = f (keys.getD j 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hj), Array.getElem?_eq_getElem hj,
    Array.getElem_map]
  rfl

/-- Absorbing the assignment's own point leaves the mask agreeing with it, whatever it held. -/
theorem dbAbsorbArgs_agree (denv : VarId → ZMod p) (keys regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ) (started : Bool) (hregs : DbRegsAt denv keys regs) :
    ∀ j, j < keys.size →
      (dbAbsorbArgs keys regs vals alive live started).2.1.getD j false = true →
      (dbAbsorbArgs keys regs vals alive live started).1.getD j 0
        = (denv ⟨keys.getD j 0⟩).val := by
  intro j hj hal
  cases started with
  | true =>
    rw [dbAbsorbArgs_true] at hal ⊢
    obtain ⟨h1, _, h3⟩ := dbAbsorbGo_spec regs keys vals keys.size 0 live alive (by omega)
    simp only at hal ⊢
    rw [h1, ← h3 j (Nat.zero_le j) hj hal]
    exact hregs j hj
  | false =>
    rw [dbAbsorbArgs_false] at hal ⊢
    simp only at hal ⊢
    rw [dbMap_getD keys _ j hj]
    exact hregs j hj

/-- Absorbing any point can only kill keys, so agreement survives. -/
theorem dbAbsorbArgs_preserve (denv : VarId → ZMod p) (keys regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ)
    (hag : ∀ j, j < keys.size → alive.getD j false = true →
      vals.getD j 0 = (denv ⟨keys.getD j 0⟩).val) :
    ∀ j, j < keys.size →
      (dbAbsorbArgs keys regs vals alive live true).2.1.getD j false = true →
      (dbAbsorbArgs keys regs vals alive live true).1.getD j 0
        = (denv ⟨keys.getD j 0⟩).val := by
  intro j hj hal
  rw [dbAbsorbArgs_true] at hal ⊢
  obtain ⟨h1, h2, _⟩ := dbAbsorbGo_spec regs keys vals keys.size 0 live alive (by omega)
  simp only at hal ⊢
  rw [h1]
  exact hag j hj (h2 j hal)

/-- Once the mask is good, the rest of the sweep keeps it good. -/
theorem dbScanLoop_preserve {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (keys : Array ℕ) (doms : Array DbDom) (denv : VarId → ZMod p) :
    ∀ (d i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
      DbScanGood denv keys ⟨regs, vals, alive, live, started⟩ →
      DbScanGood denv keys
        (dbScanLoop facts items keys doms d i n regs vals alive live started) := by
  intro d i n regs vals alive live started
  induction d, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items keys doms with
  | case1 d i n regs vals alive live started hge =>
    intro hg; rw [dbScanLoop, if_pos hge]; exact hg
  | case2 d i n regs vals alive live started hlt hdead =>
    intro hg; rw [dbScanLoop, if_neg hlt, if_pos hdead]; exact hg
  | case3 d i n regs vals alive live started hlt halive regs1 hinner hok vals1 alive1 live1
      started1 habs ih =>
    intro hg
    obtain ⟨hst, hlive⟩ := hg
    have hst' : started = true := hst
    subst hst'
    have hne : ¬ live = 0 := fun h0 => halive (by simp [h0])
    have hagree : DbMaskAgree denv keys ⟨regs, vals, alive, live, true⟩ := hlive.resolve_left hne
    have hok' : dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    have habs' : dbAbsorbArgs keys
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live true = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_pos hok', habs']
    refine ih ⟨?_, Or.inr ?_⟩
    · have hst4 : (dbAbsorbArgs keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live true).2.2.2 = started1 := congrArg (fun r => r.2.2.2) habs'
      rw [dbAbsorbArgs_true] at hst4
      exact hst4.symm
    · intro j hj hj2
      rw [show vals1 = (dbAbsorbArgs keys regs1 vals alive live true).1 from
        (congrArg (fun r => r.1) habs).symm]
      refine dbAbsorbArgs_preserve denv keys regs1 vals alive live hagree j hj ?_
      rw [show (dbAbsorbArgs keys regs1 vals alive live true).2.1 = alive1 from
        congrArg (fun r => r.2.1) habs]
      exact hj2
  | case4 d i n regs vals alive live started hlt halive regs1 hinner hok ih =>
    intro hg
    have hok' : ¬ dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_neg hok']
    exact ih hg
  | case5 d i n regs vals alive live started hlt halive regs1 hinner regs2 vals1 alive1 live1
      started1 hrec ihinner ih =>
    intro hg
    have hrec' : dbScanLoop facts items keys doms (d + 1) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_neg hinner]
    rw [hrec']
    refine ih ?_
    have := ihinner hg
    rw [hrec] at this
    exact this

theorem dbSetD_self (regs : Array ℕ) (k v : ℕ) (hk : k < regs.size) :
    (regs.set! k v).getD k 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_self, if_pos hk]
  rfl

theorem dbSet_size (regs : Array ℕ) (k v : ℕ) : (regs.set! k v).size = regs.size := by
  rw [Array.set!]; simp

theorem dbSetD_ne {α : Type} (a : Array α) (k k' : ℕ) (v dflt : α) (h : k' ≠ k) :
    (a.set! k v).getD k' dflt = a.getD k' dflt := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-- The sweep at dimension `d` writes only the keys from `d` on. -/
theorem dbScanLoop_regs {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (keys : Array ℕ) (doms : Array DbDom) (k : ℕ) :
    ∀ (d i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
      d < keys.size → (∀ d', d ≤ d' → d' < keys.size → keys.getD d' 0 ≠ k) →
      (dbScanLoop facts items keys doms d i n regs vals alive live started).regs.getD k 0
        = regs.getD k 0 := by
  intro d i n regs vals alive live started
  induction d, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items keys doms with
  | case1 d i n regs vals alive live started hge =>
    intro _ _; rw [dbScanLoop, if_pos hge]
  | case2 d i n regs vals alive live started hlt hdead =>
    intro _ _; rw [dbScanLoop, if_neg hlt, if_pos hdead]
  | case3 d i n regs vals alive live started hlt halive regs1 hinner hok vals1 alive1 live1
      started1 habs ih =>
    intro hd hfp
    have hok' : dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    have habs' : dbAbsorbArgs keys
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_pos hok', habs', ih hd hfp]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)
  | case4 d i n regs vals alive live started hlt halive regs1 hinner hok ih =>
    intro hd hfp
    have hok' : ¬ dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_neg hok', ih hd hfp]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)
  | case5 d i n regs vals alive live started hlt halive regs1 hinner regs2 vals1 alive1 live1
      started1 hrec ihinner ih =>
    intro hd hfp
    have hrec' : dbScanLoop facts items keys doms (d + 1) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_neg hinner]
    rw [hrec', ih hd hfp]
    have hin := ihinner (by omega) (fun d' hd' hlt' => hfp d' (by omega) hlt')
    rw [hrec'] at hin
    rw [hin]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)

theorem dbScanLoop_size {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (keys : Array ℕ) (doms : Array DbDom) :
    ∀ (d i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
      (dbScanLoop facts items keys doms d i n regs vals alive live started).regs.size
        = regs.size := by
  intro d i n regs vals alive live started
  induction d, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items keys doms with
  | case1 d i n regs vals alive live started hge => rw [dbScanLoop, if_pos hge]
  | case2 d i n regs vals alive live started hlt hdead =>
    rw [dbScanLoop, if_neg hlt, if_pos hdead]
  | case3 d i n regs vals alive live started hlt halive regs1 hinner hok vals1 alive1 live1
      started1 habs ih =>
    have hok' : dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    have habs' : dbAbsorbArgs keys
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_pos hok', habs', ih, dbSet_size]
  | case4 d i n regs vals alive live started hlt halive regs1 hinner hok ih =>
    have hok' : ¬ dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_neg hok', ih, dbSet_size]
  | case5 d i n regs vals alive live started hlt halive regs1 hinner regs2 vals1 alive1 live1
      started1 hrec ihinner ih =>
    have hrec' : dbScanLoop facts items keys doms (d + 1) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_neg hinner]
    rw [hrec', ih]
    have := ihinner
    rw [hrec'] at this
    rw [this, dbSet_size]

/-- The sweep reaches the assignment's own point, so the mask it ends with agrees with it (or is
    empty, in which case the plan forces nothing). `idx` picks each key's index in its domain. -/
theorem dbScanLoop_reach {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (keys : Array ℕ) (doms : Array DbDom) (denv : VarId → ZMod p) (idx : ℕ → ℕ)
    (hdist : ∀ a b, a < keys.size → b < keys.size → keys.getD a 0 = keys.getD b 0 → a = b)
    (hidx : ∀ d, d < keys.size → idx d < (doms.getD d (.range 0)).size ∧
      DbDom.at p (doms.getD d (.range 0)) (idx d) = (denv ⟨keys.getD d 0⟩).val)
    (hitems : ∀ regs', DbRegsAt denv keys regs' → dbAllOk facts items regs' 0 = true) :
    ∀ (d i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
      d < keys.size → n = (doms.getD d (.range 0)).size → i ≤ idx d →
      (∀ d', d' < keys.size → keys.getD d' 0 < regs.size) →
      (∀ d', d' < d → regs.getD (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val) →
      DbScanGood denv keys
        (dbScanLoop facts items keys doms d i n regs vals alive live started) := by
  intro d i n regs vals alive live started
  induction d, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items keys doms with
  | case1 d i n regs vals alive live started hge =>
    intro hd hn hi _ _
    exact absurd hge (by rw [hn]; have := (hidx d hd).1; omega)
  | case2 d i n regs vals alive live started hlt hdead =>
    intro _ _ _ _ _
    rw [dbScanLoop, if_neg hlt, if_pos hdead]
    simp only [Bool.and_eq_true, beq_iff_eq] at hdead
    exact ⟨hdead.1, Or.inl hdead.2⟩
  | case3 d i n regs vals alive live started hlt halive regs1 hinner hok vals1 alive1 live1
      started1 habs ih =>
    intro hd hn hi hcov houter
    have hok' : dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    have habs' : dbAbsorbArgs keys
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_pos hok', habs']
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · exact ih hd hn (by omega) (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd')
        (fun d' hd' => hset d' hd')
    · -- this is the assignment's own point: the mask now agrees, and stays agreeing
      have hieq : i = idx d := by omega
      have hregsAt : DbRegsAt denv keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) := by
        intro d0 hd0
        rcases Nat.lt_trichotomy d0 d with h | h | h
        · exact hset d0 h
        · subst h
          rw [dbSetD_self regs _ _ (hcov d0 hd0), hieq]
          exact (hidx d0 hd0).2
        · omega
      refine dbScanLoop_preserve facts items keys doms denv _ _ _ _ _ _ _ _ ⟨?_, Or.inr ?_⟩
      · have hst4 : (dbAbsorbArgs keys
            (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
            vals alive live started).2.2.2 = started1 := congrArg (fun r => r.2.2.2) habs'
        cases started with
        | true => rw [dbAbsorbArgs_true] at hst4; exact hst4.symm
        | false => rw [dbAbsorbArgs_false] at hst4; exact hst4.symm
      · intro j hj hj2
        rw [show vals1 = (dbAbsorbArgs keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started).1 from (congrArg (fun r => r.1) habs').symm]
        refine dbAbsorbArgs_agree denv keys _ vals alive live started hregsAt j hj ?_
        rw [show (dbAbsorbArgs keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started).2.1 = alive1 from congrArg (fun r => r.2.1) habs']
        exact hj2
  | case4 d i n regs vals alive live started hlt halive regs1 hinner hok ih =>
    intro hd hn hi hcov houter
    have hok' : ¬ dbAllOk facts items
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) 0 = true := hok
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_pos hinner]
    rw [if_neg hok']
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · exact ih hd hn (by omega) (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd')
        (fun d' hd' => hset d' hd')
    · -- the assignment's own point cannot fail
      exfalso
      refine hok' (hitems _ ?_)
      intro d0 hd0
      rcases Nat.lt_trichotomy d0 d with h | h | h
      · exact hset d0 h
      · subst h
        rw [dbSetD_self regs _ _ (hcov d0 hd0), show i = idx d0 from by omega]
        exact (hidx d0 hd0).2
      · omega
  | case5 d i n regs vals alive live started hlt halive regs1 hinner regs2 vals1 alive1 live1
      started1 hrec ihinner ih =>
    intro hd hn hi hcov houter
    have hrec' : dbScanLoop facts items keys doms (d + 1) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    have hd1 : d + 1 < keys.size := by omega
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive]
    simp only [if_neg hinner]
    rw [hrec']
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · -- not yet the right index at this dimension: keep sweeping, restoring the outer agreement
      refine ih hd hn (by omega) (fun d' hd' => by
        have hsz := dbScanLoop_size facts items keys doms (d + 1) 0
          (doms.getD (d + 1) (DbDom.range 0)).size
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started
        rw [hrec'] at hsz
        rw [show regs2.size = regs.size from by rw [hsz, dbSet_size]]
        exact hcov d' hd') (fun d' hd' => ?_)
      have hfoot := dbScanLoop_regs facts items keys doms (keys.getD d' 0) (d + 1) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started hd1
        (fun e he hes hkey => by have := hdist d' e (by omega) hes hkey.symm; omega)
      rw [hrec'] at hfoot
      rw [hfoot]
      exact hset d' hd'
    · -- the right index here: the inner sweep reaches the point, then the rest preserves it
      have hieq : i = idx d := by omega
      refine dbScanLoop_preserve facts items keys doms denv _ _ _ _ _ _ _ _ ?_
      have := ihinner hd1 rfl (Nat.zero_le _)
        (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd') (fun d' hd' => by
        rcases Nat.lt_trichotomy d' d with h | h | h
        · exact hset d' h
        · subst h
          rw [dbSetD_self regs _ _ (hcov d' hd), hieq]
          exact (hidx d' hd).2
        · omega)
      rw [hrec'] at this
      exact this

/-! ## 5. Assembling the invocation

The scan is sound point-wise (layer 4); what remains is that the pass only ever scans boxes it is
entitled to: the domain table is sound (layer 2), the gathered items hold at the assignment (layer
3), and the two "no answer" exits — a failing variable-free obligation and an empty box — happen
only when nothing satisfies the system. -/

/-- Agreement on an array of variables, as the context's per-item variable lists carry them. -/
def DbRegsAgreeA (denv : VarId → ZMod p) (regs : Array ℕ) (vs : Array VarId) : Prop :=
  ∀ i ∈ vs, regs.getD i.index 0 = (denv i).val

/-- A target's keys are pairwise distinct, so the sweep's dimensions write disjoint registers. -/
def DbNodupIdx (vs : Array VarId) : Prop :=
  ∀ a b, a < vs.size → b < vs.size → (vs.getD a ⟨0⟩).index = (vs.getD b ⟨0⟩).index → a = b

theorem dbGetD_lt {α : Type u} (vs : Array α) (k : ℕ) (dflt : α) (h : k < vs.size) :
    vs.getD k dflt = vs[k] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

private theorem dbListFoldlInv {α : Type u} {β : Type v} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α), (∀ b a, a ∈ l → P b → P (f b a)) → ∀ b0, P b0 → P (l.foldl f b0) := by
  intro l
  induction l with
  | nil => intro _ b0 h0; exact h0
  | cons a rest ih =>
    intro hstep b0 h0
    rw [List.foldl_cons]
    exact ih (fun b a' ha' hb => hstep b a' (List.mem_cons_of_mem _ ha') hb) _
      (hstep b0 a (List.mem_cons_self ..) h0)

/-- Any invariant preserved by one step of an array fold survives the fold. -/
theorem dbFoldlInv {α : Type u} {β : Type v} (P : β → Prop) (f : β → α → β) (as : Array α)
    (hstep : ∀ b a, a ∈ as → P b → P (f b a)) (b0 : β) (h0 : P b0) : P (as.foldl f b0) := by
  rw [← Array.foldl_toList]
  exact dbListFoldlInv P f as.toList (fun b a ha hb => hstep b a (by simpa using ha) hb) b0 h0

/-- A position of `as.zipIdx` names its own element. -/
theorem dbMem_zipIdx {α : Type u} (as : Array α) (x : α × ℕ) (h : x ∈ as.zipIdx) :
    ∃ hlt : x.2 < as.size, as[x.2] = x.1 := by
  have h' : as[x.2]? = some x.1 := Array.mem_zipIdx_iff_getElem?.mp h
  have hlt : x.2 < as.size := by
    rcases Nat.lt_or_ge x.2 as.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at h'; exact absurd h' (by simp)
  rw [Array.getElem?_eq_getElem hlt] at h'
  exact ⟨hlt, Option.some.inj h'⟩

/-! ### Constant domains

`DbDom.at` reduces a `Nat` index into the field, so a one-element domain pins its variable's value
whatever representative the index arithmetic produced. -/

theorem dbAddN_modEq (p a b : ℕ) : dbAddN p a b % p = (a + b) % p := by
  unfold dbAddN
  by_cases h : a + b < p
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Nat.mod_eq_sub_mod (Nat.le_of_not_lt h)).symm

theorem dbMulN_addN (p a b c : ℕ) : dbMulN p (dbAddN p a b) c = (a + b) * c % p := by
  rw [dbMulN, Nat.mul_mod, dbAddN_modEq, ← Nat.mul_mod]

/-- A domain admitting a single value pins any of its members to that value. -/
theorem dbDom_const?_sound [NeZero p] (dm : DbDom) (v c : ℕ) (hmem : DbDomMem p dm v)
    (hc : DbDom.const? p dm = some c) : v = c := by
  obtain ⟨k, hk, hat⟩ := hmem
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  cases dm with
  | explicit vs =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    rcases h0 : vs[0]? with _ | v0
    · rw [h0] at hc; exact absurd hc (by simp)
    · rw [h0] at hc
      dsimp only at hc
      by_cases hall : vs.all (fun w => w == v0)
      · rw [if_pos hall] at hc
        have hcv : v0 = c := by simpa using hc
        have hall' : ∀ (i : ℕ) (h : i < vs.size), vs[i] = v0 := by simpa using hall
        rw [← hcv, ← hat]
        simp only [DbDom.at]
        rw [dbGetD_lt vs k 0 hk]
        exact hall' k hk
      · rw [if_neg hall] at hc; exact absurd hc (by simp)
  | range b =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    by_cases hb : b == 1
    · rw [if_pos hb] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      have hk0 : k = 0 := by simp only [beq_iff_eq] at hb; omega
      subst hk0
      rw [← hat]
      simp [DbDom.at]
    · rw [if_neg hb] at hc; exact absurd hc (by simp)
  | coset b negB aInv =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    by_cases hb : b == 1
    · rw [if_pos hb] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      have hk0 : k = 0 := by simp only [beq_iff_eq] at hb; omega
      subst hk0
      rw [← hat]
      simp only [DbDom.at]
      rw [if_pos hp, dbMulN_addN, Nat.zero_add, dbMulN]
    · rw [if_neg hb] at hc; exact absurd hc (by simp)

private theorem dbConstantDomains_go [NeZero p] (denv : VarId → ZMod p) (doms : Array DbDom) :
    ∀ (l : List (VarId × ℕ)),
      (∀ ki ∈ l, DbDomMem p (doms.getD ki.2 (.range 0)) (denv ki.1).val) →
      ∀ f ∈ (l.foldr (init := ([] : List (VarId × ZMod p))) fun ki acc =>
          match DbDom.const? p (doms.getD ki.2 (.range 0)) with
          | some c => (ki.1, zmodOfNatP p c) :: acc
          | none => acc), denv f.1 = f.2 := by
  intro l
  induction l with
  | nil => intro _ f hf; simp at hf
  | cons ki rest ih =>
    intro hmem f hf
    rw [List.foldr_cons] at hf
    rcases hc : DbDom.const? p (doms.getD ki.2 (.range 0)) with _ | c
    · rw [hc] at hf
      exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) f hf
    · rw [hc] at hf
      dsimp only at hf
      rcases List.mem_cons.mp hf with rfl | hf'
      · show denv ki.1 = zmodOfNatP p c
        rw [← dbDom_const?_sound (doms.getD ki.2 (.range 0)) (denv ki.1).val c
          (hmem ki (List.mem_cons_self ..)) hc, zmodOfNatP_val]
      · exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) f hf'

/-- The answers a target needs no scan for: every one-element domain forces its key. -/
theorem dbConstantDomains_sound [NeZero p] (denv : VarId → ZMod p) (keys : Array VarId)
    (doms : Array DbDom)
    (hdom : ∀ k, ∀ hk : k < keys.size, DbDomMem p (doms.getD k (.range 0)) (denv keys[k]).val) :
    ∀ f ∈ dbConstantDomains p keys doms, denv f.1 = f.2 := by
  rw [dbConstantDomains, ← Array.foldr_toList]
  refine dbConstantDomains_go denv doms keys.zipIdx.toList (fun ki hki => ?_)
  obtain ⟨hlt, heq⟩ := dbMem_zipIdx keys ki (Array.mem_toList_iff.mp hki)
  rw [← heq]
  exact hdom ki.2 hlt

/-! ### The target's domains

`dbDomsOf` answers only when every key is domained, and then key `k`'s domain sits at position `k`. -/

private theorem dbDomsGo_none (T : DbTab p) : ∀ (l : List VarId),
    l.foldl (fun acc v => match acc with
      | none => none
      | some ds => match T.get v.index with
        | none => none
        | some dm => some (ds.push dm)) (none : Option (Array DbDom)) = none := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih => simpa using ih

private theorem dbGetD_push_lt (acc : Array DbDom) (dm : DbDom) (k : ℕ) (h : k < acc.size) :
    (acc.push dm).getD k (.range 0) = acc.getD k (.range 0) := by
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), dbGetD_lt _ _ _ h,
    Array.getElem_push_lt h]

private theorem dbGetD_push_eq (acc : Array DbDom) (dm : DbDom) :
    (acc.push dm).getD acc.size (.range 0) = dm := by
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

private theorem dbDomsGo (T : DbTab p) : ∀ (l : List VarId) (acc doms : Array DbDom),
    l.foldl (fun acc v => match acc with
      | none => none
      | some ds => match T.get v.index with
        | none => none
        | some dm => some (ds.push dm)) (some acc) = some doms →
      (∀ k, k < acc.size → doms.getD k (.range 0) = acc.getD k (.range 0)) ∧
      (∀ k v, l[k]? = some v → T.get v.index = some (doms.getD (acc.size + k) (.range 0))) := by
  intro l
  induction l with
  | nil =>
    intro acc doms h
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, fun k v hv => by simp at hv⟩
  | cons v rest ih =>
    intro acc doms h
    simp only [List.foldl_cons] at h
    rcases hg : T.get v.index with _ | dm
    · rw [hg] at h
      simp only at h
      rw [dbDomsGo_none] at h
      exact absurd h (by simp)
    · rw [hg] at h
      simp only at h
      obtain ⟨h1, h2⟩ := ih (acc.push dm) doms h
      refine ⟨fun k hk => by rw [h1 k (by rw [Array.size_push]; omega), dbGetD_push_lt acc dm k hk],
        fun k w hw => ?_⟩
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
        subst hw
        rw [hg, Nat.add_zero, h1 acc.size (by rw [Array.size_push]; omega), dbGetD_push_eq]
      · rw [List.getElem?_cons_succ] at hw
        have := h2 k w hw
        rwa [Array.size_push, show acc.size + 1 + k = acc.size + (k + 1) from by omega] at this

/-- Key `k` of a preflighted target carries the domain the table holds for it. -/
theorem dbDomsOf_get (T : DbTab p) (vs : Array VarId) (doms : Array DbDom)
    (h : dbDomsOf T vs = some doms) :
    ∀ k, ∀ hk : k < vs.size, T.get vs[k].index = some (doms.getD k (.range 0)) := by
  rw [dbDomsOf, ← Array.foldl_toList] at h
  obtain ⟨_, h2⟩ := dbDomsGo T vs.toList #[] doms h
  intro k hk
  have := h2 k vs[k] (by rw [List.getElem?_eq_getElem (by simpa using hk)]; simp)
  simpa using this

/-! ### The mask's answer -/

theorem dbForcedOfMask_sound [NeZero p] (denv : VarId → ZMod p) (keys : Array VarId)
    (vals : Array ℕ) (alive : Array Bool)
    (hag : ∀ j, ∀ hj : j < keys.size, alive.getD j false = true →
      vals.getD j 0 = (denv keys[j]).val) :
    ∀ (i : ℕ), ∀ f ∈ dbForcedOfMask p keys vals alive i, denv f.1 = f.2 := by
  intro i
  induction hn : keys.size - i generalizing i with
  | zero =>
    intro f hf
    rw [dbForcedOfMask, dif_neg (by omega)] at hf
    simp at hf
  | succ n ih =>
    intro f hf
    have hlt : i < keys.size := by omega
    rw [dbForcedOfMask, dif_pos hlt] at hf
    dsimp only at hf
    by_cases hal : alive.getD i false
    · rw [if_pos hal] at hf
      rcases List.mem_cons.mp hf with rfl | hf'
      · show denv keys[i] = zmodOfNatP p (vals.getD i 0)
        rw [hag i hlt hal, zmodOfNatP_val]
      · exact ih (i + 1) (by omega) f hf'
    · rw [if_neg hal] at hf
      exact ih (i + 1) (by omega) f hf

theorem dbAllOk_of_forall {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (regs : Array ℕ) (h : ∀ item ∈ items, dbItemOk facts regs item = true) :
    ∀ i, dbAllOk facts items regs i = true := by
  intro i
  induction hn : items.size - i generalizing i with
  | zero => rw [dbAllOk, dif_neg (by omega)]
  | succ n ih =>
    have hlt : i < items.size := by omega
    rw [dbAllOk, dif_pos hlt, if_pos (h items[i] (Array.getElem_mem hlt))]
    exact ih (i + 1) (by omega)

/-! ### The per-item variable lists

`dbVarsOf` collects a superset of `DenseExpr.vars` without duplicates: the first gives agreement on
every expression the item mentions, the second that the sweep's dimensions are independent. -/

private theorem dbPushVar_mem (acc : Array VarId) (i : VarId) : ∀ x ∈ acc, x ∈ dbPushVar acc i := by
  intro x hx
  rw [dbPushVar]
  split
  · exact hx
  · exact Array.mem_push_of_mem _ hx

private theorem dbPushVar_self (acc : Array VarId) (i : VarId) : i ∈ dbPushVar acc i := by
  rw [dbPushVar]
  split
  · next h => exact Array.contains_iff_mem.mp h
  · exact Array.mem_push_self

private theorem dbVarsOf_mem : ∀ (e : DenseExpr p) (acc : Array VarId),
    (∀ x ∈ acc, x ∈ dbVarsOf e acc) ∧ (∀ i ∈ e.vars, i ∈ dbVarsOf e acc) := by
  intro e
  induction e with
  | const c => intro acc; exact ⟨fun x hx => hx, fun i hi => by simp [DenseExpr.vars] at hi⟩
  | var j =>
    intro acc
    refine ⟨dbPushVar_mem acc j, fun i hi => ?_⟩
    have hij : i = j := by simpa [DenseExpr.vars] using hi
    subst hij
    exact dbPushVar_self acc i
  | add a b iha ihb =>
    intro acc
    refine ⟨fun x hx => (ihb (dbVarsOf a acc)).1 x ((iha acc).1 x hx), fun i hi => ?_⟩
    rcases List.mem_append.mp (by simpa only [DenseExpr.vars] using hi) with h | h
    · exact (ihb (dbVarsOf a acc)).1 i ((iha acc).2 i h)
    · exact (ihb (dbVarsOf a acc)).2 i h
  | mul a b iha ihb =>
    intro acc
    refine ⟨fun x hx => (ihb (dbVarsOf a acc)).1 x ((iha acc).1 x hx), fun i hi => ?_⟩
    rcases List.mem_append.mp (by simpa only [DenseExpr.vars] using hi) with h | h
    · exact (ihb (dbVarsOf a acc)).1 i ((iha acc).2 i h)
    · exact (ihb (dbVarsOf a acc)).2 i h

private theorem dbVarsOfList_mem : ∀ (es : List (DenseExpr p)) (acc : Array VarId),
    (∀ x ∈ acc, x ∈ dbVarsOfList es acc) ∧
      (∀ e ∈ es, ∀ i ∈ e.vars, i ∈ dbVarsOfList es acc) := by
  intro es
  induction es with
  | nil => intro acc; exact ⟨fun x hx => hx, fun e he => by simp at he⟩
  | cons e rest ih =>
    intro acc
    refine ⟨fun x hx => (ih (dbVarsOf e acc)).1 x ((dbVarsOf_mem e acc).1 x hx),
      fun e' he' i hi => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he''
    · exact (ih (dbVarsOf e' acc)).1 i ((dbVarsOf_mem e' acc).2 i hi)
    · exact (ih (dbVarsOf e acc)).2 e' he'' i hi

theorem dbVarsOf_agree (denv : VarId → ZMod p) (regs : Array ℕ) (e : DenseExpr p)
    (h : DbRegsAgreeA denv regs (dbVarsOf e #[])) : DbRegsAgree denv regs e.vars :=
  fun i hi => h i ((dbVarsOf_mem e #[]).2 i hi)

theorem dbBiVars_agree (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgreeA denv regs (dbBiVars bi)) :
    DbRegsAgree denv regs (denseBIVars bi) := by
  intro i hi
  refine h i ?_
  rw [dbBiVars]
  rcases List.mem_append.mp (by simpa only [denseBIVars] using hi) with hm | hm
  · exact (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity #[])).1 i
      ((dbVarsOf_mem bi.multiplicity #[]).2 i hm)
  · obtain ⟨e, he, hie⟩ := List.mem_flatMap.mp hm
    exact (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity #[])).2 e he i hie

/-- Positional distinctness, in the `getElem` form the collectors preserve. -/
private def DbNodupA (vs : Array VarId) : Prop :=
  ∀ a b (ha : a < vs.size) (hb : b < vs.size), vs[a] = vs[b] → a = b

private theorem dbVarId_eq (x y : VarId) (h : x.index = y.index) : x = y := by
  cases x; cases y; simpa using h

private theorem dbNodupIdx_of (vs : Array VarId) (h : DbNodupA vs) : DbNodupIdx vs := by
  intro a b ha hb hidx
  rw [dbGetD_lt vs a ⟨0⟩ ha, dbGetD_lt vs b ⟨0⟩ hb] at hidx
  exact h a b ha hb (dbVarId_eq _ _ hidx)

private theorem dbPushVar_nodup (acc : Array VarId) (i : VarId) (h : DbNodupA acc) :
    DbNodupA (dbPushVar acc i) := by
  rw [dbPushVar]
  split
  · exact h
  · next hc =>
    have hni : ∀ k, ∀ hk : k < acc.size, acc[k] ≠ i := by
      intro k hk hki
      exact hc (Array.contains_iff_mem.mpr (by rw [← hki]; exact Array.getElem_mem hk))
    intro a b ha hb hab
    rw [Array.size_push] at ha hb
    rcases Nat.lt_or_ge a acc.size with h1 | h1 <;> rcases Nat.lt_or_ge b acc.size with h2 | h2
    · rw [Array.getElem_push_lt h1, Array.getElem_push_lt h2] at hab
      exact h a b h1 h2 hab
    · have hb' : b = acc.size := by omega
      subst hb'
      rw [Array.getElem_push_lt h1, Array.getElem_push_eq] at hab
      exact absurd hab (hni a h1)
    · have ha' : a = acc.size := by omega
      subst ha'
      rw [Array.getElem_push_lt h2, Array.getElem_push_eq] at hab
      exact absurd hab.symm (hni b h2)
    · omega

private theorem dbVarsOf_nodup : ∀ (e : DenseExpr p) (acc : Array VarId), DbNodupA acc →
    DbNodupA (dbVarsOf e acc) := by
  intro e
  induction e with
  | const c => intro acc h; exact h
  | var j => intro acc h; exact dbPushVar_nodup acc j h
  | add a b iha ihb => intro acc h; exact ihb _ (iha acc h)
  | mul a b iha ihb => intro acc h; exact ihb _ (iha acc h)

private theorem dbVarsOfList_nodup : ∀ (es : List (DenseExpr p)) (acc : Array VarId),
    DbNodupA acc → DbNodupA (dbVarsOfList es acc) := by
  intro es
  induction es with
  | nil => intro acc h; exact h
  | cons e rest ih => intro acc h; exact ih _ (dbVarsOf_nodup e acc h)

private theorem dbNodupA_empty : DbNodupA (#[] : Array VarId) := by
  intro a b ha; simp at ha

theorem dbVarsOf_nodupIdx (e : DenseExpr p) : DbNodupIdx (dbVarsOf e #[]) :=
  dbNodupIdx_of _ (dbVarsOf_nodup e #[] dbNodupA_empty)

theorem dbBiVars_nodupIdx (bi : BusInteraction (DenseExpr p)) : DbNodupIdx (dbBiVars bi) :=
  dbNodupIdx_of _ (dbVarsOfList_nodup bi.payload _ (dbVarsOf_nodup bi.multiplicity #[]
    dbNodupA_empty))

/-! ### The register file's width -/

private theorem dbFoldMaxL_ge : ∀ (l : List VarId) (m : ℕ),
    m ≤ l.foldl (fun b v => max b (v.index + 1)) m := by
  intro l
  induction l with
  | nil => intro m; exact Nat.le_refl m
  | cons v rest ih =>
    intro m
    rw [List.foldl_cons]
    exact le_trans (le_max_left m (v.index + 1)) (ih _)

private theorem dbFoldMaxL_mem : ∀ (l : List VarId) (m : ℕ), ∀ i ∈ l,
    i.index < l.foldl (fun b v => max b (v.index + 1)) m := by
  intro l
  induction l with
  | nil => intro m i hi; simp at hi
  | cons v rest ih =>
    intro m i hi
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact lt_of_lt_of_le (lt_of_lt_of_le (by omega) (le_max_right m (i.index + 1)))
        (dbFoldMaxL_ge rest _)
    · exact ih _ i hi'

private theorem dbNvOfL_ge : ∀ (l : List (Array VarId)) (m : ℕ),
    m ≤ l.foldl (fun acc a => a.foldl (fun b v => max b (v.index + 1)) acc) m := by
  intro l
  induction l with
  | nil => intro m; exact Nat.le_refl m
  | cons a rest ih =>
    intro m
    rw [List.foldl_cons]
    refine le_trans ?_ (ih _)
    rw [← Array.foldl_toList]
    exact dbFoldMaxL_ge a.toList m

theorem dbNvOf_ge (vs : Array (Array VarId)) (m : ℕ) : m ≤ dbNvOf vs m := by
  rw [dbNvOf, ← Array.foldl_toList]
  exact dbNvOfL_ge vs.toList m

private theorem dbNvOfL_mem : ∀ (l : List (Array VarId)) (m : ℕ), ∀ a ∈ l, ∀ i ∈ a,
    i.index < l.foldl (fun acc a => a.foldl (fun b v => max b (v.index + 1)) acc) m := by
  intro l
  induction l with
  | nil => intro m a ha; simp at ha
  | cons a rest ih =>
    intro m a' ha' i hi
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha' with rfl | ha''
    · refine lt_of_lt_of_le ?_ (dbNvOfL_ge rest _)
      rw [← Array.foldl_toList]
      exact dbFoldMaxL_mem a'.toList m i (by simpa using hi)
    · exact ih _ a' ha'' i hi

theorem dbNvOf_mem (vs : Array (Array VarId)) (m : ℕ) : ∀ a ∈ vs, ∀ i ∈ a,
    i.index < dbNvOf vs m := by
  rw [dbNvOf, ← Array.foldl_toList]
  exact fun a ha i hi => dbNvOfL_mem vs.toList m a (by simpa using ha) i hi

/-! ### The context

Everything the target loop reads is built once. `DbCtxGood` is what a satisfying assignment makes
true of it; `DbCtxShape` what holds unconditionally. -/

theorem dbGetD_map {α : Type u} {β : Type v} (as : Array α) (f : α → β) (pos : ℕ) (dflt : β) :
    (as.map f).getD pos dflt = if h : pos < as.size then f as[pos] else dflt := by
  rcases Nat.lt_or_ge pos as.size with h | h
  · rw [dif_pos h, dbGetD_lt _ _ _ (by simpa using h), Array.getElem_map]
  · rw [dif_neg (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using h)]
    rfl

theorem dbGetD_map_zipIdx {α : Type u} {β : Type v} (as : Array α) (f : α × ℕ → β) (pos : ℕ) (dflt : β) :
    ((as.zipIdx).map f).getD pos dflt = if h : pos < as.size then f (as[pos], pos) else dflt := by
  rw [dbGetD_map]
  simp only [Array.size_zipIdx]
  split
  · rw [Array.getElem_zipIdx, Nat.zero_add]
  · rfl

/-- The cache resolves each fact about the interaction it was built from. -/
theorem dbPreOne_preOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (vars : Array VarId) :
    DbBiPreOf facts bi (dbPreOne facts bi vars) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [dbPreOne] at hb
    split at hb
    · rcases hspec : facts.byteXorSpec bi.busId with _ | spec
      · rw [hspec] at hb; simp at hb
      · rw [hspec] at hb
        simp only [Option.bind_some] at hb
        rcases hdec : spec.decode bi.payload with _ | t
        · rw [hdec] at hb; simp at hb
        · rw [hdec] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          subst hb
          exact ⟨hspec, t.1, hdec, rfl⟩
    · simp at hb
  · intro h
    simp only [dbPreOne, Bool.and_eq_true] at h
    exact h.2
  · intro t ht
    simp only [dbPreOne] at ht
    split_ifs at ht
    exact ht
  · intro t ht
    simp only [dbPreOne] at ht
    split_ifs at ht <;> exact ht

theorem dbCsItemsOf_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (cs : Array (DenseExpr p)) (csVars : Array (Array VarId)) (denv : VarId → ZMod p)
    (hcs : ∀ c ∈ cs, c.eval denv = 0)
    (hvars : ∀ k, ∀ hk : k < cs.size, csVars.getD k #[] = dbVarsOf cs[k] #[]) :
    ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (csVars.getD pos #[]) →
      dbItemOk facts regs ((dbCsItemsOf T cs csVars).getD pos DbItem.always) = true := by
  intro pos regs hagree
  simp only [dbCsItemsOf, dbGetD_map_zipIdx]
  split
  · next hpos =>
    split
    · rw [hvars pos hpos] at hagree
      show (dbEval p regs (dbCompile cs[pos]) == 0) = true
      rw [dbEval_dbCompile_zero denv regs cs[pos] (dbVarsOf_agree denv regs cs[pos] hagree)]
      exact decide_eq_true (hcs cs[pos] (Array.getElem_mem hpos))
    · rfl
  · rfl

theorem dbBiItemsOf_ok [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (T : DbTab p) (bis : Array (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p))
    (biVars : Array (Array VarId)) (denv : VarId → ZMod p)
    (hbis : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (hpre : ∀ k, ∀ hk : k < bis.size, DbBiPreOf facts bis[k] (pre.getD k dbBiPreEmpty))
    (hvars : ∀ k, ∀ hk : k < bis.size, biVars.getD k #[] = dbBiVars bis[k]) :
    ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (biVars.getD pos #[]) →
      dbItemOk facts regs ((dbBiItemsOf facts T bis pre).getD pos DbItem.always) = true := by
  intro pos regs hagree
  simp only [dbBiItemsOf, dbGetD_map_zipIdx]
  split
  · next hpos =>
    split
    · rw [hvars pos hpos] at hagree
      exact dbCompileBi_ok facts bis[pos] _ (hpre pos hpos) denv regs
        (dbBiVars_agree denv regs bis[pos] hagree) (hbis bis[pos] (Array.getElem_mem hpos))
    · rfl
  · rfl

/-- A variable-free item's position lands in the varless bucket. -/
theorem dbBucketsOf_varless (nv : ℕ) (vars : Array (Array VarId)) :
    ∀ i ∈ (dbBucketsOf nv vars).2, vars.getD i #[] = #[] := by
  rw [dbBucketsOf]
  refine dbFoldlInv (fun st : Array (Array ℕ) × Array ℕ => ∀ i ∈ st.2, vars.getD i #[] = #[])
    _ _ (fun st vi hvi hst => ?_) _ (fun i hi => by simp at hi)
  obtain ⟨hlt, heq⟩ := dbMem_zipIdx vars vi hvi
  dsimp only
  split
  · next h0 =>
    intro i hi
    rcases Array.mem_push.mp hi with hi' | rfl
    · exact hst i hi'
    · rw [dbGetD_lt vars vi.2 #[] hlt, heq]
      have hsz : vi.1.size = 0 := by
        rcases Nat.eq_zero_or_pos vi.1.size with h | h
        · exact h
        · rw [Array.getElem?_eq_getElem h] at h0; simp at h0
      exact Array.eq_empty_of_size_eq_zero hsz
  · exact hst

/-- What a satisfying assignment makes true of the once-built context. -/
structure DbCtxGood {p : ℕ} {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) : Prop where
  /-- Every domain contains the value the assignment gives its variable. -/
  tab : DbTabSound p denv ctx.T
  /-- The variable-free obligations hold, so the pass does not take the vacuous exit. -/
  constOk : ctx.constOk = true
  csItem : ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (ctx.csVars.getD pos #[]) →
    dbItemOk facts regs (ctx.csItems.getD pos DbItem.always) = true
  csVarless : ∀ item ∈ ctx.csVarlessItems, ∀ regs : Array ℕ, dbItemOk facts regs item = true
  biItem : ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (ctx.biVars.getD pos #[]) →
    dbItemOk facts regs (ctx.biItems.getD pos DbItem.always) = true

/-- What holds of the context whether or not anything satisfies the system. -/
structure DbCtxShape {p : ℕ} (ctx : DbCtx p) : Prop where
  csNodup : ∀ pos, DbNodupIdx (ctx.csVars.getD pos #[])
  csNv : ∀ pos, ∀ i ∈ ctx.csVars.getD pos #[], i.index < ctx.nv
  biNodup : ∀ pos, DbNodupIdx (ctx.biVars.getD pos #[])
  biNv : ∀ pos, ∀ i ∈ ctx.biVars.getD pos #[], i.index < ctx.nv

private theorem dbNodupIdx_empty : DbNodupIdx (#[] : Array VarId) := by
  intro a b ha; simp at ha

theorem dbBuildCtx_shape (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DbCtxShape (dbBuildCtx bs facts d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pos
    simp only [dbBuildCtx]
    rw [dbGetD_map]
    split
    · exact dbVarsOf_nodupIdx _
    · exact dbNodupIdx_empty
  · intro pos i hi
    simp only [dbBuildCtx] at hi ⊢
    rw [dbGetD_map] at hi
    split at hi
    · next hpos =>
      refine lt_of_lt_of_le (dbNvOf_mem
        ((d.algebraicConstraints.toArray).map (fun c => dbVarsOf c #[])) 0
        (dbVarsOf (d.algebraicConstraints.toArray)[pos] #[]) (Array.mem_map.mpr
          ⟨(d.algebraicConstraints.toArray)[pos], Array.getElem_mem hpos, rfl⟩) i hi) ?_
      exact dbNvOf_ge _ _
    · simp at hi
  · intro pos
    simp only [dbBuildCtx]
    rw [dbGetD_map]
    split
    · exact dbBiVars_nodupIdx _
    · exact dbNodupIdx_empty
  · intro pos i hi
    simp only [dbBuildCtx] at hi ⊢
    rw [dbGetD_map] at hi
    split at hi
    · next hpos =>
      exact dbNvOf_mem ((d.busInteractions.toArray).map dbBiVars) _
        (dbBiVars (d.busInteractions.toArray)[pos]) (Array.mem_map.mpr
          ⟨(d.busInteractions.toArray)[pos], Array.getElem_mem hpos, rfl⟩) i hi
    · simp at hi

theorem dbBuildCtx_good [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    DbCtxGood facts denv (dbBuildCtx bs facts d) := by
  have hcs : ∀ c ∈ d.algebraicConstraints.toArray, c.eval denv = 0 :=
    fun c hc => hsat.1 c (by simpa using hc)
  have hbis : ∀ bi ∈ d.busInteractions.toArray,
      (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv) :=
    fun bi hbi => hsat.2 bi (by simpa using hbi)
  have hprevars : ∀ k, ∀ hk : k < (d.busInteractions.toArray).size,
      ((d.busInteractions.toArray).map dbBiVars).getD k #[] =
        dbBiVars (d.busInteractions.toArray)[k] := fun k hk => by rw [dbGetD_map, dif_pos hk]
  have hcsvars : ∀ k, ∀ hk : k < (d.algebraicConstraints.toArray).size,
      ((d.algebraicConstraints.toArray).map (fun c => dbVarsOf c #[])).getD k #[] =
        dbVarsOf (d.algebraicConstraints.toArray)[k] #[] := fun k hk => by
    rw [dbGetD_map, dif_pos hk]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the domain table: the three phases only insert sound domains
    simp only [dbBuildCtx]
    refine dbBytePhase_sound facts denv _ (fun k hk => ?_) 0 _ ?_
    · have hk' : k < (d.busInteractions.toArray).size := by simpa using hk
      refine ⟨(d.busInteractions.toArray)[k], ?_, hbis _ (Array.getElem_mem hk')⟩
      rw [Array.getElem_map, Array.getElem_zipIdx]
      simp only [Nat.zero_add]
      exact dbPreOne_preOf facts _ _
    · refine dbBusPhase_sound facts denv _ _ (fun k hk => ?_) 0 _ ?_
      · simp only [dbGetD_map_zipIdx, dif_pos hk]
        exact ⟨dbPreOne_preOf facts _ _, hbis _ (Array.getElem_mem hk)⟩
      · exact dbConstraintPhase_sound denv _ hcs _ 0 _ (dbTabSound_empty denv _)
  · -- `constOk`: a variable-free interaction's obligation holds at the assignment
    simp only [dbBuildCtx]
    refine dbFoldlInv (fun s : ℕ × Bool × Bool × Bool => s.2.2.2 = true) _ _
      (fun s i hi hsi => ?_) _ rfl
    dsimp only
    split
    · dsimp only
      rw [hsi, Bool.true_and]
      refine dbBiItemsOf_ok facts _ _ _ _ denv hbis
        (fun k hk => by simp only [dbGetD_map_zipIdx, dif_pos hk]; exact dbPreOne_preOf facts _ _)
        hprevars i #[] ?_
      rw [dbBucketsOf_varless _ _ i hi]
      intro x hx; simp at hx
    · exact hsi
  · -- constraint items
    intro pos regs hagree
    simp only [dbBuildCtx] at hagree ⊢
    exact dbCsItemsOf_ok facts _ _ _ denv hcs hcsvars pos regs hagree
  · -- variable-free constraint items: their programs read no register
    intro item hitem regs
    simp only [dbBuildCtx] at hitem ⊢
    obtain ⟨i, hi, hfi⟩ := Array.mem_filterMap.mp hitem
    split at hfi
    · rw [show item = (dbCsItemsOf _ _ _).getD i DbItem.always from (Option.some.inj hfi).symm]
      refine dbCsItemsOf_ok facts _ _ _ denv hcs hcsvars i regs ?_
      rw [dbBucketsOf_varless _ _ i hi]
      intro x hx; simp at hx
    · simp at hfi
  · -- bus items
    intro pos regs hagree
    simp only [dbBuildCtx] at hagree ⊢
    refine dbBiItemsOf_ok facts _ _ _ _ denv hbis
      (fun k hk => by simp only [dbGetD_map_zipIdx, dif_pos hk]; exact dbPreOne_preOf facts _ _)
      hprevars pos regs hagree

/-! ### Gathering

A gathered item's variables are all keys of the target, so agreement on the keys is agreement on the
item. -/

theorem dbSubset_agree (denv : VarId → ZMod p) (regs : Array ℕ) (vs xs : Array VarId)
    (hregs : DbRegsAgreeA denv regs xs) (hsub : dbSubset vs xs = true) :
    DbRegsAgreeA denv regs vs := by
  intro i hi
  refine hregs i ?_
  have hall : ∀ (j : ℕ) (h : j < vs.size), vs[j] ∈ xs := by simpa [dbSubset] using hsub
  obtain ⟨j, hj, hvj⟩ := Array.getElem_of_mem hi
  rw [← hvj]
  exact hall j hj

private theorem dbGatherCsAt_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (xs : Array VarId) (regs : Array ℕ) (hregs : DbRegsAgreeA denv regs xs)
    (g : DbGather p) (pos : ℕ) (hg : ∀ item ∈ g.items, dbItemOk facts regs item = true) :
    ∀ item ∈ (dbGatherCsAt ctx xs g pos).items, dbItemOk facts regs item = true := by
  rw [dbGatherCsAt]
  split
  · next hsub =>
    split
    · intro item hitem
      rcases Array.mem_push.mp hitem with hitem' | rfl
      · exact hg item hitem'
      · exact hgood.csItem pos regs (dbSubset_agree denv regs _ xs hregs hsub)
    · exact hg
  · exact hg

private theorem dbGatherBiAt_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (xs : Array VarId) (regs : Array ℕ) (hregs : DbRegsAgreeA denv regs xs)
    (g : DbGather p) (pos : ℕ) (hg : ∀ item ∈ g.items, dbItemOk facts regs item = true) :
    ∀ item ∈ (dbGatherBiAt ctx xs g pos).items, dbItemOk facts regs item = true := by
  rw [dbGatherBiAt]
  split
  · next hsub =>
    intro item hitem
    rcases Array.mem_push.mp hitem with hitem' | rfl
    · exact hg item hitem'
    · refine hgood.biItem pos regs (dbSubset_agree denv regs _ xs hregs ?_)
      exact (Bool.and_eq_true _ _ ▸ hsub : _ ∧ _).2
  · exact hg

theorem dbGather_items_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (xs : Array VarId) (regs : Array ℕ) (hregs : DbRegsAgreeA denv regs xs) :
    ∀ item ∈ (dbGather ctx xs).items, dbItemOk facts regs item = true := by
  rw [dbGather]
  refine dbFoldlInv (fun g : DbGather p => ∀ item ∈ g.items, dbItemOk facts regs item = true)
    _ _ (fun g v _ hg => ?_) _ (fun item hitem => hgood.csVarless item hitem regs)
  dsimp only
  refine dbFoldlInv (fun g : DbGather p => ∀ item ∈ g.items, dbItemOk facts regs item = true)
    _ _ (fun g' pos _ hg' => dbGatherBiAt_ok facts denv ctx hgood xs regs hregs g' pos hg') _ ?_
  exact dbFoldlInv (fun g : DbGather p => ∀ item ∈ g.items, dbItemOk facts regs item = true)
    _ _ (fun g' pos _ hg' => dbGatherCsAt_ok facts denv ctx hgood xs regs hregs g' pos hg') _ hg

/-! ### Plans

`dbRunPlan` threads a register file through the run, so a plan's answer is a function of whatever
file it inherits; `DbPlanSound` quantifies over that. -/

/-- The forced list one plan contributes, as a function of the register file it starts from. -/
def dbRunPlanNew {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ) (regs0 : Array ℕ)
    (plan : DbPlan p) : List (VarId × ZMod p) :=
  match plan with
  | .done forced => forced
  | .scan keys doms items constOk =>
    let regs0 := if regs0.size == nv then regs0 else Array.replicate nv 0
    if !constOk then dbZeroAll keys
    else
      let res := dbScanBox facts items (keys.map (fun v => v.index)) doms regs0
      if !res.started then dbZeroAll keys
      else if res.live == 0 then []
      else dbForcedOfMask p keys res.vals res.alive 0

theorem dbRunPlan_snd {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (st : Array ℕ × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    (dbRunPlan facts nv st plan).2 = dbRunPlanNew facts nv st.1 plan :: st.2 := by
  cases plan with
  | done forced => rfl
  | scan keys doms items constOk =>
    simp only [dbRunPlan, dbRunPlanNew]
    split_ifs <;> rfl

/-- A plan answers soundly: whatever register file it starts from, every constant it forces holds in
    every satisfying assignment. -/
def DbPlanSound {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (d : DenseConstraintSystem p) (plan : DbPlan p) : Prop :=
  ∀ (regs0 : Array ℕ), ∀ f ∈ dbRunPlanNew facts nv regs0 plan,
    ∀ denv, d.satisfies bs denv → denv f.1 = f.2

private theorem dbKeys_getD (xs : Array VarId) (j : ℕ) (hj : j < xs.size) :
    (xs.map (fun v => v.index)).getD j 0 = xs[j].index := by
  rw [dbGetD_map, dif_pos hj]

/-- The sweep of a preflighted box ends with a good mask: it started, and either nothing survives or
    every survivor carries the assignment's value. -/
theorem dbScanBox_good [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (items : Array DbItem) (xs : Array VarId) (doms : Array DbDom)
    (regs : Array ℕ) (hnodup : DbNodupIdx xs) (hcov : ∀ i ∈ xs, i.index < regs.size)
    (hmem : ∀ k, ∀ hk : k < xs.size, DbDomMem p (doms.getD k (.range 0)) (denv xs[k]).val)
    (hitems : ∀ regs', DbRegsAt denv (xs.map (fun v => v.index)) regs' →
      dbAllOk facts items regs' 0 = true) :
    DbScanGood denv (xs.map (fun v => v.index))
      (dbScanBox facts items (xs.map (fun v => v.index)) doms regs) := by
  have hcov' : ∀ d', d' < (xs.map (fun v => v.index)).size →
      (xs.map (fun v => v.index)).getD d' 0 < regs.size := by
    intro d' hd'
    rw [Array.size_map] at hd'
    rw [dbKeys_getD xs d' hd']
    exact hcov xs[d'] (Array.getElem_mem hd')
  rw [dbScanBox]
  split
  · next hempty =>
    have hxs : xs.size = 0 := by
      have hz : (xs.map (fun v => v.index)).size = 0 := by simpa [Array.isEmpty] using hempty
      rwa [Array.size_map] at hz
    rw [if_pos (hitems regs (fun dd hdd => by
      rw [Array.size_map] at hdd; exact absurd hdd (by omega)))]
    exact ⟨rfl, Or.inl rfl⟩
  · next hempty =>
    have hsz : 0 < (xs.map (fun v => v.index)).size := by
      rcases Nat.eq_zero_or_pos (xs.map (fun v => v.index)).size with h | h
      · exact absurd (by simp [Array.isEmpty, h]) hempty
      · exact h
    have hmem' : ∀ dd, dd < (xs.map (fun v => v.index)).size →
        DbDomMem p (doms.getD dd (.range 0))
          (denv ⟨(xs.map (fun v => v.index)).getD dd 0⟩).val := by
      intro dd hdd
      rw [Array.size_map] at hdd
      rw [dbKeys_getD xs dd hdd]
      exact hmem dd hdd
    have hdist : ∀ a b, a < (xs.map (fun v => v.index)).size →
        b < (xs.map (fun v => v.index)).size →
        (xs.map (fun v => v.index)).getD a 0 = (xs.map (fun v => v.index)).getD b 0 → a = b := by
      intro a b ha hb hab
      rw [Array.size_map] at ha hb
      rw [dbKeys_getD xs a ha, dbKeys_getD xs b hb] at hab
      exact hnodup a b ha hb (by
        rw [dbGetD_lt xs a ⟨0⟩ ha, dbGetD_lt xs b ⟨0⟩ hb]; exact hab)
    refine dbScanLoop_reach facts items _ doms denv
      (fun dd => if h : dd < (xs.map (fun v => v.index)).size then (hmem' dd h).choose else 0)
      hdist (fun dd hdd => ?_) hitems 0 0 _ regs #[] #[] 0 false hsz rfl (Nat.zero_le _) hcov'
      (fun d' hd' => absurd hd' (by omega))
    dsimp only
    rw [dif_pos hdd]
    exact (hmem' dd hdd).choose_spec

/-- What the scan's answer forces, given a good mask. -/
theorem dbScanAnswer_sound [NeZero p] (denv : VarId → ZMod p) (xs : Array VarId) (st : DbScanSt)
    (hgoodst : DbScanGood denv (xs.map (fun v => v.index)) st) :
    ∀ f ∈ (if !st.started then dbZeroAll xs
      else if st.live == 0 then [] else dbForcedOfMask p xs st.vals st.alive 0),
      denv f.1 = f.2 := by
  obtain ⟨hstarted, hlive⟩ := hgoodst
  rw [hstarted]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hl : st.live == 0
  · rw [if_pos hl]; intro f hf; simp at hf
  · rw [if_neg hl]
    rcases hlive with h0 | hag
    · exact absurd (by simpa using h0) hl
    · refine dbForcedOfMask_sound denv xs st.vals st.alive (fun j hj hal => ?_) 0
      have hj' := hag j (by rwa [Array.size_map]) hal
      rwa [dbKeys_getD xs j hj] at hj'

/-- A preflighted target's plan is sound. The two "no answer" exits are vacuous: a variable-free
    obligation cannot fail at a satisfying assignment (`DbCtxGood.constOk`), and the sweep visits
    that assignment's own point, so it cannot come back empty. -/
theorem dbPreflight_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (xs : Array VarId) (hnodup : DbNodupIdx xs) (hnv : ∀ i ∈ xs, i.index < ctx.nv)
    (plan : DbPlan p) (hpre : dbPreflight ctx xs = some plan) :
    DbPlanSound facts ctx.nv d plan := by
  intro regs0 f hf denv hsat
  have hg := hgood denv hsat
  rw [dbPreflight] at hpre
  rcases hdoms : dbDomsOf ctx.T xs with _ | doms
  · rw [hdoms] at hpre; simp at hpre
  · rw [hdoms] at hpre
    dsimp only at hpre
    have hmem : ∀ k, ∀ hk : k < xs.size,
        DbDomMem p (doms.getD k (.range 0)) (denv xs[k]).val := fun k hk =>
      hg.tab _ _ (dbDomsOf_get ctx.T xs doms hdoms k hk)
    split_ifs at hpre
    · -- every domain is a single value: no scan needed
      rw [show plan = DbPlan.done (dbConstantDomains p xs doms) from (Option.some.inj hpre).symm,
        dbRunPlanNew] at hf
      exact dbConstantDomains_sound denv xs doms hmem f hf
    · -- the scan
      rw [show plan = DbPlan.scan xs doms (dbGather ctx xs).items ctx.constOk
          from (Option.some.inj hpre).symm, dbRunPlanNew, hg.constOk] at hf
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at hf
      have hcovr : ∀ i ∈ xs,
          i.index < (if regs0.size == ctx.nv then regs0 else Array.replicate ctx.nv 0).size := by
        intro i hi
        split
        · next hs => rw [show regs0.size = ctx.nv from by simpa using hs]; exact hnv i hi
        · rw [Array.size_replicate]; exact hnv i hi
      have hitems : ∀ regs', DbRegsAt denv (xs.map (fun v => v.index)) regs' →
          dbAllOk facts (dbGather ctx xs).items regs' 0 = true := by
        intro regs' hregs'
        refine dbAllOk_of_forall facts _ regs' ?_ 0
        refine dbGather_items_ok facts denv ctx hg xs regs' (fun i hi => ?_)
        obtain ⟨j, hj, hij⟩ := Array.getElem_of_mem hi
        have hj' := hregs' j (by rwa [Array.size_map])
        rw [dbKeys_getD xs j hj, hij] at hj'
        exact hj'
      exact dbScanAnswer_sound denv xs _
        (dbScanBox_good facts denv _ xs doms _ hnodup hcovr hmem hitems) f hf

/-! ### The target loop -/

theorem dbTargetStep_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (xs : Array VarId) (hnodup : DbNodupIdx xs) (hnv : ∀ i ∈ xs, i.index < ctx.nv)
    (st : DbSeen × List (DbPlan p))
    (hst : ∀ plan ∈ st.2, DbPlanSound facts ctx.nv d plan) :
    ∀ plan ∈ (dbTargetStep ctx xs st).2, DbPlanSound facts ctx.nv d plan := by
  rw [dbTargetStep]
  split
  · exact hst
  · split
    · exact hst
    · split
      · exact hst
      · dsimp only
        split
        · exact hst
        · split
          · exact hst
          · next plan heq =>
            intro plan' hplan'
            rcases List.mem_cons.mp hplan' with rfl | hrest
            · exact dbPreflight_sound bs facts d ctx hgood xs hnodup hnv plan' heq
            · exact hst plan' hrest

theorem dbTargetsCs_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p) (hshape : DbCtxShape ctx)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx) :
    ∀ (k : ℕ) (st : DbSeen × List (DbPlan p)),
      (∀ plan ∈ st.2, DbPlanSound facts ctx.nv d plan) →
      ∀ plan ∈ (dbTargetsCs ctx k st).2, DbPlanSound facts ctx.nv d plan := by
  intro k
  induction hn : ctx.csVars.size - k generalizing k with
  | zero => intro st hst; rw [dbTargetsCs, dif_neg (by omega)]; exact hst
  | succ n ih =>
    intro st hst
    have hlt : k < ctx.csVars.size := by omega
    rw [dbTargetsCs, dif_pos hlt]
    refine ih (k + 1) (by omega) _ (dbTargetStep_sound bs facts d ctx hgood ctx.csVars[k] ?_ ?_ st
      hst)
    · have := hshape.csNodup k; rwa [dbGetD_lt _ _ _ hlt] at this
    · have := hshape.csNv k; rwa [dbGetD_lt _ _ _ hlt] at this

theorem dbTargetsBis_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p) (hshape : DbCtxShape ctx)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx) :
    ∀ (k : ℕ) (st : DbSeen × List (DbPlan p)),
      (∀ plan ∈ st.2, DbPlanSound facts ctx.nv d plan) →
      ∀ plan ∈ (dbTargetsBis ctx k st).2, DbPlanSound facts ctx.nv d plan := by
  intro k
  induction hn : ctx.biVars.size - k generalizing k with
  | zero => intro st hst; rw [dbTargetsBis, dif_neg (by omega)]; exact hst
  | succ n ih =>
    intro st hst
    have hlt : k < ctx.biVars.size := by omega
    rw [dbTargetsBis, dif_pos hlt]
    refine ih (k + 1) (by omega) _ (dbTargetStep_sound bs facts d ctx hgood ctx.biVars[k] ?_ ?_ st
      hst)
    · have := hshape.biNodup k; rwa [dbGetD_lt _ _ _ hlt] at this
    · have := hshape.biNv k; rwa [dbGetD_lt _ _ _ hlt] at this

/-! ### The run and the solution map -/

theorem dbRunPlans_sound {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (d : DenseConstraintSystem p) (plans : List (DbPlan p))
    (hplans : ∀ plan ∈ plans, DbPlanSound facts nv d plan) :
    ∀ l ∈ dbRunPlans facts nv plans, ∀ f ∈ l,
      ∀ denv, d.satisfies bs denv → denv f.1 = f.2 := by
  have hfold : ∀ (plans : List (DbPlan p)) (st : Array ℕ × List (List (VarId × ZMod p))),
      (∀ plan ∈ plans, DbPlanSound facts nv d plan) →
      (∀ l ∈ st.2, ∀ f ∈ l, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) →
      ∀ l ∈ (plans.foldl (dbRunPlan facts nv) st).2, ∀ f ∈ l,
        ∀ denv, d.satisfies bs denv → denv f.1 = f.2 := by
    intro plans
    induction plans with
    | nil => intro st _ hst; exact hst
    | cons plan rest ih =>
      intro st hp hst
      rw [List.foldl_cons]
      refine ih _ (fun q hq => hp q (List.mem_cons_of_mem _ hq)) ?_
      rw [dbRunPlan_snd]
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact hp plan (List.mem_cons_self ..) st.1
      · exact hst l hl'
  intro l hl
  rw [dbRunPlans, List.mem_reverse] at hl
  exact hfold plans _ hplans (fun l hl => by simp at hl) l hl

theorem dbDomainBatchσ_entailed [Fact p.Prime] [NeZero p]
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    EntailedMap d bs (dbDomainBatchσ bs facts d).map := by
  have hfold : ∀ (results : List (List (VarId × ZMod p))) (dσ : DenseSolved p),
      (∀ l ∈ results, ∀ f ∈ l, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) →
      EntailedMap d bs dσ.map →
      EntailedMap d bs (results.foldl (fun dσ forced =>
        dσ.insertAll (forced.map (fun f => (f.1, DenseExpr.const f.2)))) dσ).map := by
    intro results
    induction results with
    | nil => intro dσ _ h; exact h
    | cons l rest ih =>
      intro dσ hres h
      rw [List.foldl_cons]
      refine ih _ (fun l' hl' => hres l' (List.mem_cons_of_mem _ hl')) ?_
      rw [DenseSolved.insertAll_map]
      refine EntailedMap_foldl_insert d bs _ dσ.map h (fun pr hpr => ?_)
      obtain ⟨f, hfm, rfl⟩ := List.mem_map.1 hpr
      refine ⟨fun z hz => by simp [DenseExpr.vars] at hz, fun denv hsat => ?_⟩
      show denv f.1 = (DenseExpr.const f.2).eval denv
      rw [DenseExpr.eval]
      exact hres l (List.mem_cons_self ..) f hfm denv hsat
  rw [dbDomainBatchσ]
  refine hfold _ DenseSolved.empty ?_ (fun i t h => by
    rw [DenseSolved.empty, Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp))
  refine dbRunPlans_sound facts _ d _ (fun plan hplan => ?_)
  rw [List.mem_reverse] at hplan
  exact dbTargetsBis_sound bs facts d _ (dbBuildCtx_shape bs facts d)
    (fun denv hsat => dbBuildCtx_good bs facts d denv hsat) 0 _
    (dbTargetsCs_sound bs facts d _ (dbBuildCtx_shape bs facts d)
      (fun denv hsat => dbBuildCtx_good bs facts d denv hsat) 0 ⟨⟨∅⟩, []⟩
      (fun plan hplan => by simp at hplan)) plan hplan

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
