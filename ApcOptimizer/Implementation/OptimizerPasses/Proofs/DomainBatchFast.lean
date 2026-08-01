import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchFast
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ByteCheckPack

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

theorem dbReplicate_getD (n j : ℕ) (hj : j < n) : (Array.replicate n true).getD j false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj),
    Array.getElem_replicate]
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
