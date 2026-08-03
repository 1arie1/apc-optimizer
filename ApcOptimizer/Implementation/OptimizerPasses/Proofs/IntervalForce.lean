import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable

set_option autoImplicit false

/-! # Dense interval forcing: proof and wiring for `denseIntervalForceNew` (`IntervalForce.lean`).

The pass appends entailed constraints, so correctness rides on
`DensePassCorrect.denseAddConstraints` once each emitted key is shown to state a truth about the
assignment (`DenseIFKeyHolds`) and to mention only variables of `d` (`DenseIFFrom`).

The chain is: `denseIFLin` is `denseLinearizeAcc`, so the whole `Affine`/`Normalize` layer
(`denseLinearize_eval`, `denseLinearize_vars`, `denseMergeTerms_eval`, `denseMergeTerms_fst`)
applies to the merged term list; `denseIFProc` turns that into terms carrying their integer window;
`int_window` pins the signed integer value of a bounded slot to `[0, B)`; and the walk's two arms
are then `omega` over that window. -/

namespace ApcOptimizer.Dense

open IntervalForce

variable {p : ℕ}

/-! ## `denseIFLin` is `denseLinearizeAcc` -/

theorem denseIFConst_eq (e : DenseExpr p) :
    denseIFConst e = (denseLinearize e).bind
      (fun l => if l.terms.isEmpty then some l.const else none) := by
  induction e with
  | const n => simp [denseIFConst, denseLinearize]
  | var i => simp [denseIFConst, denseLinearize]
  | add a b iha ihb =>
    cases ha : denseLinearize a with
    | none => simp [denseIFConst, denseLinearize, ha, iha]
    | some la =>
      cases hb : denseLinearize b with
      | none =>
        cases hta : la.terms <;>
          simp [denseIFConst, denseLinearize, ha, hb, iha, ihb, hta]
      | some lb =>
        simp only [denseIFConst, iha, ihb, ha, hb, Option.bind_some]
        cases hta : la.terms <;> cases htb : lb.terms <;>
          simp [denseLinearize, ha, hb, DenseLinExpr.add, hta, htb, zmodAdd_eq]
  | mul a b iha ihb =>
    cases ha : denseLinearize a with
    | none => simp [denseIFConst, denseLinearize, ha, iha]
    | some la =>
      cases hb : denseLinearize b with
      | none =>
        cases hta : la.terms <;>
          simp [denseIFConst, denseLinearize, ha, hb, iha, ihb, hta]
      | some lb =>
        simp only [denseIFConst, iha, ihb, ha, hb, Option.bind_some]
        cases hta : la.terms <;> cases htb : lb.terms <;>
          simp [denseLinearize, ha, hb, DenseLinExpr.scale, hta, htb, zmodMul_eq]

/-- `denseIFLin` is `denseLinearize` with the terms threaded onto an accumulator: the only change
    is that a product whose left factor has terms decides its right factor with `denseIFConst`
    (variable-free), which is the same test as "the right factor's term list is empty". -/
theorem denseIFLin_eq (e : DenseExpr p) (acc : List (VarId × ZMod p)) :
    denseIFLin e acc = (denseLinearize e).map (fun l => (l.const, l.terms ++ acc)) := by
  induction e generalizing acc with
  | const n => simp [denseIFLin, denseLinearize]
  | var i => simp [denseIFLin, denseLinearize]
  | add a b iha ihb =>
    rw [denseIFLin, ihb acc]
    cases hb : denseLinearize b with
    | none => simp [denseLinearize, hb]
    | some lb =>
      simp only [Option.map_some, iha (lb.terms ++ acc)]
      cases ha : denseLinearize a with
      | none => simp [denseLinearize, ha, hb]
      | some la =>
        simp [denseLinearize, ha, hb, DenseLinExpr.add, zmodAdd_eq, List.append_assoc]
  | mul a b iha ihb =>
    rw [denseIFLin, iha []]
    cases ha : denseLinearize a with
    | none => simp [denseLinearize, ha]
    | some la =>
      simp only [Option.map_some, List.append_nil]
      by_cases h1 : la.terms.isEmpty
      · rw [if_pos h1, ihb []]
        cases hb : denseLinearize b with
        | none => simp [denseLinearize, ha, hb]
        | some lb =>
          simp only [Option.map_some, List.append_nil]
          simp [denseLinearize, ha, hb, h1, DenseLinExpr.scale, denseScaleAppend_eq, zmodMul_eq]
      · rw [if_neg h1, denseIFConst_eq]
        cases hb : denseLinearize b with
        | none => simp [denseLinearize, ha, hb]
        | some lb =>
          simp only [Option.bind_some]
          by_cases h2 : lb.terms.isEmpty
          · rw [if_pos h2]
            simp [denseLinearize, ha, hb, h1, h2, DenseLinExpr.scale, denseScaleAppend_eq,
              zmodMul_eq]
          · rw [if_neg h2]
            simp [denseLinearize, ha, hb, h1, h2]

theorem denseIFLin_spec (e : DenseExpr p) (c : ZMod p) (raw : List (VarId × ZMod p))
    (h : denseIFLin e [] = some (c, raw)) :
    ∃ l : DenseLinExpr p, denseLinearize e = some l ∧ l.const = c ∧ l.terms = raw := by
  rw [denseIFLin_eq] at h
  cases hl : denseLinearize e with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some l =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at h
    exact ⟨l, rfl, h.1, h.2⟩

/-! ## Processed terms

`denseIFVal` is the integer value the term list stands for. The two facts `denseIFProc` establishes
are that this value casts back to the slot's field value, and that each term's `(mn, mx)` bracket
its own contribution. -/

def denseIFVal (denv : VarId → ZMod p) : List DenseIFTerm → Int
  | [] => 0
  | t :: rest => t.sc * ((denv t.v).val : Int) + denseIFVal denv rest

theorem denseIFVal_eq (denv : VarId → ZMod p) (l : List DenseIFTerm) :
    denseIFVal denv l = (l.map (fun t => t.sc * ((denv t.v).val : Int))).sum := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [denseIFVal, ih]

theorem denseIFSumMn_eq (l : List DenseIFTerm) :
    denseIFSumMn l = (l.map (fun t => t.mn)).sum := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [denseIFSumMn, ih]

theorem denseIFSumMx_eq (l : List DenseIFTerm) :
    denseIFSumMx l = (l.map (fun t => t.mx)).sum := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [denseIFSumMx, ih]

theorem denseIFVal_perm (denv : VarId → ZMod p) {l1 l2 : List DenseIFTerm} (h : l1.Perm l2) :
    denseIFVal denv l1 = denseIFVal denv l2 := by
  rw [denseIFVal_eq, denseIFVal_eq]; exact List.Perm.sum_eq (List.Perm.map _ h)

theorem denseIFSumMn_perm {l1 l2 : List DenseIFTerm} (h : l1.Perm l2) :
    denseIFSumMn l1 = denseIFSumMn l2 := by
  rw [denseIFSumMn_eq, denseIFSumMn_eq]; exact List.Perm.sum_eq (List.Perm.map _ h)

theorem denseIFSumMx_perm {l1 l2 : List DenseIFTerm} (h : l1.Perm l2) :
    denseIFSumMx l1 = denseIFSumMx l2 := by
  rw [denseIFSumMx_eq, denseIFSumMx_eq]; exact List.Perm.sum_eq (List.Perm.map _ h)

/-- Every term's contribution sits inside its own window, so the whole value sits inside the sum
    of the windows. -/
theorem denseIFVal_window (denv : VarId → ZMod p) (l : List DenseIFTerm)
    (hw : ∀ t ∈ l, t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
      t.sc * ((denv t.v).val : Int) ≤ t.mx) :
    denseIFSumMn l ≤ denseIFVal denv l ∧ denseIFVal denv l ≤ denseIFSumMx l := by
  induction l with
  | nil => simp [denseIFVal, denseIFSumMn, denseIFSumMx]
  | cons t rest ih =>
    have hr := ih (fun t' ht' => hw t' (List.mem_cons_of_mem _ ht'))
    have ht := hw t (List.mem_cons_self ..)
    simp only [denseIFVal, denseIFSumMn, denseIFSumMx]
    omega

theorem denseIFTermOf_v (half : Nat) (c : ZMod p) (Bv : Nat) (v : VarId) :
    (denseIFTermOf half c Bv v).v = v := rfl

theorem denseIFSrep_eq (c : ZMod p) : denseIFSrep ((p - 1) / 2) c = srep c := rfl

/-- The window of a term built by `denseIFTermOf`, from its variable's own bound. -/
theorem denseIFTermOf_window (c : ZMod p) (Bv : Nat) (v : VarId) (denv : VarId → ZMod p)
    (hb : (denv v).val < Bv) :
    (denseIFTermOf ((p - 1) / 2) c Bv v).mn ≤
        (denseIFTermOf ((p - 1) / 2) c Bv v).sc * ((denv v).val : Int) ∧
      (denseIFTermOf ((p - 1) / 2) c Bv v).sc * ((denv v).val : Int) ≤
        (denseIFTermOf ((p - 1) / 2) c Bv v).mx := by
  have hd : ((denv v).val : Int) < (Bv : Int) := by exact_mod_cast hb
  obtain ⟨h1, h2⟩ := term_window (srep c) ((denv v).val : Int) (Bv : Int)
    (Int.natCast_nonneg _) hd
  simp only [denseIFTermOf, denseIFSrep_eq]
  refine ⟨?_, ?_⟩
  · split_ifs with h <;> omega
  · split_ifs with h <;> omega

/-- Each processed term mentions a variable of the input term list. -/
theorem denseIFProc_vars (half : Nat) (idx : Std.HashMap VarId Nat) :
    ∀ (n : Nat) (l : List (VarId × ZMod p)) (ts : List DenseIFTerm),
      denseIFProc half idx n l = some ts → ∀ t ∈ ts, t.v ∈ l.map Prod.fst := by
  intro n l
  induction l generalizing n with
  | nil =>
    intro ts h t ht
    simp only [denseIFProc, Option.some.injEq] at h
    exact absurd (h ▸ ht) (by simp)
  | cons vc rest ih =>
    obtain ⟨v, c⟩ := vc
    intro ts h t ht
    simp only [denseIFProc] at h
    by_cases hz : zmodIsZero c = true
    · rw [if_pos hz] at h
      exact List.mem_cons_of_mem _ (ih n ts h t ht)
    rw [if_neg hz] at h
    by_cases hcap : maxTerms ≤ n
    · rw [if_pos hcap] at h; exact absurd h (by simp)
    rw [if_neg hcap] at h
    · cases hb : idx[v]? with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some Bv =>
        rw [hb] at h
        cases hp : denseIFProc half idx (n + 1) rest with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some ts' =>
          rw [hp] at h
          simp only [Option.some.injEq] at h
          subst h
          rcases List.mem_cons.1 ht with rfl | ht'
          · simp [denseIFTermOf_v]
          · exact List.mem_cons_of_mem _ (ih (n + 1) ts' hp t ht')

/-- The processed terms' integer value casts to the term list's field value, and each term's
    window brackets its contribution. -/
theorem denseIFProc_val [NeZero p] (idx : Std.HashMap VarId Nat) (denv : VarId → ZMod p)
    (hidx : ∀ v b, idx[v]? = some b → (denv v).val < b) :
    ∀ (n : Nat) (l : List (VarId × ZMod p)) (ts : List DenseIFTerm),
      denseIFProc ((p - 1) / 2) idx n l = some ts →
        ((denseIFVal denv ts : Int) : ZMod p) = (l.map (fun t => t.2 * denv t.1)).sum ∧
        ∀ t ∈ ts, t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
          t.sc * ((denv t.v).val : Int) ≤ t.mx := by
  intro n l
  induction l generalizing n with
  | nil =>
    intro ts h
    simp only [denseIFProc, Option.some.injEq] at h
    subst h
    exact ⟨by simp [denseIFVal], by simp⟩
  | cons vc rest ih =>
    obtain ⟨v, c⟩ := vc
    intro ts h
    simp only [denseIFProc] at h
    by_cases hz : zmodIsZero c = true
    · rw [if_pos hz] at h
      obtain ⟨h1, h2⟩ := ih n ts h
      refine ⟨?_, h2⟩
      have hc : c = 0 := by simpa using hz
      simp [h1, hc]
    rw [if_neg hz] at h
    by_cases hcap : maxTerms ≤ n
    · rw [if_pos hcap] at h; exact absurd h (by simp)
    rw [if_neg hcap] at h
    · cases hb : idx[v]? with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some Bv =>
        rw [hb] at h
        cases hp : denseIFProc ((p - 1) / 2) idx (n + 1) rest with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some ts' =>
          rw [hp] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := ih (n + 1) ts' hp
          have hvb : (denv v).val < Bv := hidx v Bv hb
          refine ⟨?_, ?_⟩
          · have hsc : (denseIFTermOf ((p - 1) / 2) c Bv v).sc = srep c := rfl
            simp only [denseIFVal, denseIFTermOf_v, hsc, List.map_cons, List.sum_cons]
            push_cast
            rw [h1, srep_cast, ZMod.natCast_val, ZMod.cast_id]
          · intro t ht
            rcases List.mem_cons.1 ht with rfl | ht'
            · exact denseIFTermOf_window c Bv v denv hvb
            · exact h2 t ht'

/-! ## The walk -/

/-- What an emitted key says about the assignment. -/
def DenseIFKeyHolds (denv : VarId → ZMod p) (k : DenseIFKey) : Prop :=
  (k.b = 0 → denv ⟨k.a⟩ = 0) ∧ (k.b ≠ 0 → denv ⟨k.a⟩ = denv ⟨k.b - 1⟩)

/-- Which terms an emitted key can have come from. -/
def DenseIFFrom (ts : List DenseIFTerm) (k : DenseIFKey) : Prop :=
  (∃ t ∈ ts, t.v.index = k.a) ∧ (k.b = 0 ∨ ∃ u ∈ ts, u.v.index + 1 = k.b)

theorem denseIFPush_keys (st : DenseIFAcc) (k : DenseIFKey) :
    ∀ k' ∈ (denseIFPush st k).keys, k' ∈ st.keys ∨ k' = k := by
  intro k' hk'
  unfold denseIFPush at hk'
  split_ifs at hk' with h
  · exact Or.inl hk'
  · rcases List.mem_cons.1 hk' with rfl | h'
    · exact Or.inr rfl
    · exact Or.inl h'

theorem denseIFPartner_spec (g : Int) :
    ∀ (l : List DenseIFTerm) (u : DenseIFTerm), denseIFPartner g l = some u →
      u ∈ l ∧ u.sc = g := by
  intro l
  induction l with
  | nil => intro u h; exact absurd h (by simp [denseIFPartner])
  | cons t rest ih =>
    intro u h
    simp only [denseIFPartner] at h
    split_ifs at h with hsc
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self .., by simpa using hsc⟩
    · obtain ⟨hm, hg⟩ := ih u h
      exact ⟨List.mem_cons_of_mem _ hm, hg⟩

theorem denseIFPartner_or_spec (g : Int) (seen rest : List DenseIFTerm) (u : DenseIFTerm)
    (h : ((denseIFPartner g seen).or (denseIFPartner g rest)) = some u) :
    u ∈ seen ++ rest ∧ u.sc = g := by
  cases hs : denseIFPartner g seen with
  | some u' =>
    rw [hs] at h
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    obtain ⟨hm, hg⟩ := denseIFPartner_spec g seen u' hs
    exact ⟨List.mem_append_left _ hm, hg⟩
  | none =>
    rw [hs] at h
    simp only [Option.none_or] at h
    obtain ⟨hm, hg⟩ := denseIFPartner_spec g rest u h
    exact ⟨List.mem_append_right _ hm, hg⟩

/-- Structural half of one step: every key it adds names `t` and, for a pair arm, some term of
    `seen ++ rest`. -/
theorem denseIFStep_keys (B : Nat) (c0 m M : Int) (t : DenseIFTerm)
    (seen rest : List DenseIFTerm) (st : DenseIFAcc) :
    ∀ k ∈ (denseIFStep B c0 m M t seen rest st).keys,
      k ∈ st.keys ∨ k = ⟨t.v.index, 0⟩ ∨ ∃ u ∈ seen ++ rest, k = ⟨t.v.index, u.v.index + 1⟩ := by
  have h1 : ∀ k ∈ (denseIFZeroArm B c0 m M t st).keys,
      k ∈ st.keys ∨ k = ⟨t.v.index, 0⟩ ∨
        ∃ u ∈ seen ++ rest, k = ⟨t.v.index, u.v.index + 1⟩ := by
    intro k hk
    unfold denseIFZeroArm at hk
    split_ifs at hk with hc
    · rcases denseIFPush_keys st ⟨t.v.index, 0⟩ k hk with h | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
    · exact Or.inl hk
  intro k hk
  unfold denseIFStep denseIFPairArm at hk
  split_ifs at hk with hpos
  · cases hpt : ((denseIFPartner (-t.sc) seen).or (denseIFPartner (-t.sc) rest)) with
    | none => simp only [hpt] at hk; exact h1 k hk
    | some u =>
      simp only [hpt] at hk
      obtain ⟨hum, _⟩ := denseIFPartner_or_spec (-t.sc) seen rest u hpt
      split_ifs at hk with hc
      · rcases denseIFPush_keys _ ⟨t.v.index, u.v.index + 1⟩ k hk with h | rfl
        · exact h1 k h
        · exact Or.inr (Or.inr ⟨u, hum, rfl⟩)
      · exact h1 k hk
  · exact h1 k hk

/-- Structural half of the walk: every key it adds mentions terms of `seen ++ rest`. -/
theorem denseIFWalk_from (B : Nat) (c0 m M : Int) :
    ∀ (seen rest : List DenseIFTerm) (st : DenseIFAcc),
      ∀ k ∈ (denseIFWalk B c0 m M seen rest st).keys,
        k ∈ st.keys ∨ DenseIFFrom (seen ++ rest) k := by
  intro seen rest
  induction rest generalizing seen with
  | nil => intro st k hk; exact Or.inl hk
  | cons t rest ih =>
    intro st k hk
    rw [denseIFWalk] at hk
    have hperm : (t :: seen ++ rest).Perm (seen ++ t :: rest) :=
      (List.perm_middle (a := t) (l₁ := seen) (l₂ := rest)).symm
    have htk : t ∈ seen ++ t :: rest := List.mem_append_right _ (List.mem_cons_self ..)
    rcases ih (t :: seen) _ k hk with h | h
    · rcases denseIFStep_keys B c0 m M t seen rest st k h with h' | rfl | ⟨u, hum, rfl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨⟨t, htk, rfl⟩, Or.inl rfl⟩
      · have huk : u ∈ seen ++ t :: rest := by
          rcases List.mem_append.1 hum with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
        exact Or.inr ⟨⟨t, htk, rfl⟩, Or.inr ⟨u, huk, rfl⟩⟩
    · exact Or.inr ⟨h.1.imp (fun _ h' => ⟨hperm.subset h'.1, h'.2⟩),
        h.2.imp id (fun h' => h'.imp (fun _ h'' => ⟨hperm.subset h''.1, h''.2⟩))⟩

/-- Soundness of one step, given the slot's signed value pinned to `[0, B)`. -/
theorem denseIFStep_sound [NeZero p] (B : Nat) (c0 : Int) (denv : VarId → ZMod p) (ts0 : List DenseIFTerm)
    (hw : ∀ t ∈ ts0, t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
      t.sc * ((denv t.v).val : Int) ≤ t.mx)
    (hS0 : 0 ≤ c0 + denseIFVal denv ts0) (hSB : c0 + denseIFVal denv ts0 < (B : Int))
    (t : DenseIFTerm) (seen rest : List DenseIFTerm) (hperm : (t :: (seen ++ rest)).Perm ts0)
    (st : DenseIFAcc) :
    ∀ k ∈ (denseIFStep B c0 (denseIFSumMn ts0) (denseIFSumMx ts0) t seen rest st).keys,
      k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  have hbnds' : ∀ t' ∈ seen ++ rest, t'.mn ≤ t'.sc * ((denv t'.v).val : Int) ∧
      t'.sc * ((denv t'.v).val : Int) ≤ t'.mx := fun t' ht' =>
    hw t' (hperm.subset (List.mem_cons_of_mem _ ht'))
  have hsplit : denseIFVal denv ts0
      = t.sc * ((denv t.v).val : Int) + denseIFVal denv (seen ++ rest) := by
    rw [← denseIFVal_perm denv hperm]; rfl
  have hmn : denseIFSumMn ts0 = t.mn + denseIFSumMn (seen ++ rest) := by
    rw [← denseIFSumMn_perm hperm]; rfl
  have hmx : denseIFSumMx ts0 = t.mx + denseIFSumMx (seen ++ rest) := by
    rw [← denseIFSumMx_perm hperm]; rfl
  have hwother := denseIFVal_window denv (seen ++ rest) hbnds'
  have h1 : ∀ k ∈ (denseIFZeroArm B c0 (denseIFSumMn ts0) (denseIFSumMx ts0) t st).keys,
      k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
    intro k hk
    unfold denseIFZeroArm at hk
    split_ifs at hk with hc
    · rcases denseIFPush_keys st ⟨t.v.index, 0⟩ k hk with h | rfl
      · exact Or.inl h
      · refine Or.inr ⟨fun _ => ?_, fun h => absurd rfl h⟩
        show denv t.v = 0
        rw [← ZMod.val_eq_zero]
        by_contra hne
        have hd1 : (1 : Int) ≤ ((denv t.v).val : Int) := by
          have h1 : 1 ≤ (denv t.v).val := Nat.one_le_iff_ne_zero.mpr hne
          exact_mod_cast h1
        rcases hc with ⟨hsc, hcnd⟩ | ⟨hsc, hcnd⟩
        · have hscd : t.sc ≤ t.sc * ((denv t.v).val : Int) :=
            le_mul_of_one_le_right (le_of_lt hsc) hd1
          generalize hX : t.sc * ((denv t.v).val : Int) = X at hsplit hscd
          omega
        · have hscd : t.sc * ((denv t.v).val : Int) ≤ t.sc := by
            have h1 : t.sc * ((denv t.v).val : Int) ≤ t.sc * 1 :=
              mul_le_mul_of_nonpos_left hd1 (le_of_lt hsc)
            rwa [mul_one] at h1
          generalize hX : t.sc * ((denv t.v).val : Int) = X at hsplit hscd
          omega
    · exact Or.inl hk
  intro k hk
  unfold denseIFStep denseIFPairArm at hk
  split_ifs at hk with hpos
  · cases hpt : ((denseIFPartner (-t.sc) seen).or (denseIFPartner (-t.sc) rest)) with
    | none => simp only [hpt] at hk; exact h1 k hk
    | some u =>
      simp only [hpt] at hk
      obtain ⟨hum, hug⟩ := denseIFPartner_or_spec (-t.sc) seen rest u hpt
      obtain ⟨s1, s2, hsplitl⟩ := List.append_of_mem hum
      have hpermu : (seen ++ rest).Perm (u :: (s1 ++ s2)) := by
        rw [hsplitl]; exact List.perm_middle
      have hvalu : denseIFVal denv (seen ++ rest)
          = u.sc * ((denv u.v).val : Int) + denseIFVal denv (s1 ++ s2) := by
        rw [denseIFVal_perm denv hpermu]; rfl
      have hmnu : denseIFSumMn (seen ++ rest) = u.mn + denseIFSumMn (s1 ++ s2) := by
        rw [denseIFSumMn_perm hpermu]; rfl
      have hmxu : denseIFSumMx (seen ++ rest) = u.mx + denseIFSumMx (s1 ++ s2) := by
        rw [denseIFSumMx_perm hpermu]; rfl
      have hbnds'' : ∀ w ∈ s1 ++ s2, w.mn ≤ w.sc * ((denv w.v).val : Int) ∧
          w.sc * ((denv w.v).val : Int) ≤ w.mx := fun w hwm =>
        hbnds' w (hpermu.symm.subset (List.mem_cons_of_mem _ hwm))
      have hwother' := denseIFVal_window denv (s1 ++ s2) hbnds''
      split_ifs at hk with hc
      · rcases denseIFPush_keys _ ⟨t.v.index, u.v.index + 1⟩ k hk with h | rfl
        · exact h1 k h
        · obtain ⟨hc1, hc2, _⟩ := hc
          refine Or.inr ⟨fun h => absurd h (by simp), fun _ => ?_⟩
          show denv t.v = denv u.v
          have hcomb : denseIFVal denv ts0
              = t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int))
                + denseIFVal denv (s1 ++ s2) := by
            rw [hsplit, hvalu, hug]; ring
          have hveq : (denv t.v).val = (denv u.v).val := by
            by_contra hnev
            rcases Nat.lt_or_ge (denv t.v).val (denv u.v).val with hlt | hge
            · have hdlt : ((denv t.v).val : Int) - ((denv u.v).val : Int) ≤ -1 := by
                have h2 : ((denv t.v).val : Int) + 1 ≤ ((denv u.v).val : Int) := by
                  exact_mod_cast hlt
                omega
              have hXle : t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int)) ≤ -t.sc := by
                have h2 : t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int))
                    ≤ t.sc * (-1) := mul_le_mul_of_nonneg_left hdlt (le_of_lt hpos)
                rwa [mul_neg_one] at h2
              generalize hX : t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int)) = X
                at hcomb hXle
              omega
            · have hdgt : (1 : Int) ≤ ((denv t.v).val : Int) - ((denv u.v).val : Int) := by
                have h2 : ((denv u.v).val : Int) + 1 ≤ ((denv t.v).val : Int) := by
                  have h3 : (denv u.v).val + 1 ≤ (denv t.v).val := by omega
                  exact_mod_cast h3
                omega
              have hXge : t.sc ≤ t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int)) :=
                le_mul_of_one_le_right (le_of_lt hpos) hdgt
              generalize hX : t.sc * (((denv t.v).val : Int) - ((denv u.v).val : Int)) = X
                at hcomb hXge
              omega
          exact ZMod.val_injective p hveq
      · exact h1 k hk
  · exact h1 k hk

/-- Soundness of the walk: with the slot's signed value pinned to `[0, B)`, every key it emits
    states a truth about the assignment. -/
theorem denseIFWalk_sound [NeZero p] (B : Nat) (c0 : Int) (denv : VarId → ZMod p) (ts0 : List DenseIFTerm)
    (hw : ∀ t ∈ ts0, t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
      t.sc * ((denv t.v).val : Int) ≤ t.mx)
    (hS0 : 0 ≤ c0 + denseIFVal denv ts0) (hSB : c0 + denseIFVal denv ts0 < (B : Int)) :
    ∀ (seen rest : List DenseIFTerm), (seen ++ rest).Perm ts0 → ∀ st : DenseIFAcc,
      ∀ k ∈ (denseIFWalk B c0 (denseIFSumMn ts0) (denseIFSumMx ts0) seen rest st).keys,
        k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  intro seen rest
  induction rest generalizing seen with
  | nil => intro _ st k hk; exact Or.inl hk
  | cons t rest ih =>
    intro hperm st k hk
    have hperm' : (t :: (seen ++ rest)).Perm ts0 :=
      (List.perm_middle (a := t) (l₁ := seen) (l₂ := rest)).symm.trans hperm
    rw [denseIFWalk] at hk
    rcases ih (t :: seen) (by simpa using hperm') _ k hk with h | h
    · exact denseIFStep_sound B c0 denv ts0 hw hS0 hSB t seen rest hperm' st k h
    · exact Or.inr h

/-! ## One slot -/

theorem denseIFRun_from (pI : Int) (B : Nat) (c0 : Int) (ts : List DenseIFTerm)
    (st : DenseIFAcc) :
    ∀ k ∈ (denseIFRun pI B c0 ts st).keys, k ∈ st.keys ∨ DenseIFFrom ts k := by
  intro k hk
  unfold denseIFRun at hk
  split_ifs at hk with hg
  · simpa using denseIFWalk_from B c0 (denseIFSumMn ts) (denseIFSumMx ts) [] ts st k hk
  · exact Or.inl hk

theorem denseIFRun_sound [NeZero p] (B : Nat) (c0 : Int) (ts : List DenseIFTerm)
    (denv : VarId → ZMod p) (x : ZMod p)
    (hw : ∀ t ∈ ts, t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
      t.sc * ((denv t.v).val : Int) ≤ t.mx)
    (hcast : ((c0 + denseIFVal denv ts : Int) : ZMod p) = x) (hx : x.val < B) (st : DenseIFAcc) :
    ∀ k ∈ (denseIFRun (p : Int) B c0 ts st).keys, k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  intro k hk
  unfold denseIFRun at hk
  split_ifs at hk with hg
  · obtain ⟨hhi, hlo⟩ := hg
    obtain ⟨hwm, hwM⟩ := denseIFVal_window denv ts hw
    have hS := int_window (c0 + denseIFVal denv ts) B x hcast hx (by omega) (by omega)
    have hS0 : 0 ≤ c0 + denseIFVal denv ts := by rw [hS]; exact Int.natCast_nonneg _
    have hSB : c0 + denseIFVal denv ts < (B : Int) := by rw [hS]; exact_mod_cast hx
    exact denseIFWalk_sound B c0 denv ts hw hS0 hSB [] ts (by simp) st k hk
  · exact Or.inl hk

/-- Every key one slot emits mentions variables of the slot expression. -/
theorem denseIFSlot_vars (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) (B : Nat)
    (e : DenseExpr p) (st : DenseIFAcc) :
    ∀ k ∈ (denseIFSlot half pI idx B e st).keys,
      k ∈ st.keys ∨ ((⟨k.a⟩ : VarId) ∈ e.vars ∧ (k.b = 0 ∨ (⟨k.b - 1⟩ : VarId) ∈ e.vars)) := by
  have general : ∀ (e' : DenseExpr p) (c : ZMod p) (raw : List (VarId × ZMod p))
      (ts : List DenseIFTerm), denseIFLin e' [] = some (c, raw) →
      denseIFProc half idx 0 (denseMergeTerms raw) = some ts →
      ∀ k ∈ (denseIFRun pI B (denseIFSrep half c) ts st).keys,
        k ∈ st.keys ∨ ((⟨k.a⟩ : VarId) ∈ e'.vars ∧ (k.b = 0 ∨ (⟨k.b - 1⟩ : VarId) ∈ e'.vars)) := by
    intro e' c raw ts hlin hproc k hk
    obtain ⟨l, hl, hlc, hlt⟩ := denseIFLin_spec e' c raw hlin
    have hterm : ∀ t ∈ ts, t.v ∈ e'.vars := by
      intro t ht
      have h1 := denseIFProc_vars half idx 0 (denseMergeTerms raw) ts hproc t ht
      exact denseLinearize_vars e' l hl t.v (hlt ▸ denseMergeTerms_fst raw t.v h1)
    rcases denseIFRun_from pI B (denseIFSrep half c) ts st k hk with h | ⟨⟨t, htm, hta⟩, hb⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← hta]; exact hterm t htm
      · rcases hb with h | ⟨u, hum, hub⟩
        · exact Or.inl h
        · exact Or.inr (by rw [← hub]; simpa using hterm u hum)
  intro k hk
  unfold denseIFSlot at hk
  match e with
  | .const _ => exact Or.inl hk
  | .var x =>
    simp only at hk
    cases hb : idx[x]? with
    | none => simp only [hb] at hk; exact Or.inl hk
    | some Bv =>
      simp only [hb] at hk
      rcases denseIFRun_from pI B 0 [denseIFTermOf half (zmodOneP p) Bv x] st k hk with
        h | ⟨⟨t, htm, hta⟩, hbb⟩
      · exact Or.inl h
      · rw [List.mem_singleton] at htm
        subst htm
        rw [denseIFTermOf_v] at hta
        refine Or.inr ⟨by rw [← hta]; simp [DenseExpr.vars], ?_⟩
        rcases hbb with h | ⟨u, hum, hub⟩
        · exact Or.inl h
        · rw [List.mem_singleton] at hum
          subst hum
          rw [denseIFTermOf_v] at hub
          exact Or.inr (by rw [← hub]; simp [DenseExpr.vars])
  | .add a b =>
    simp only at hk
    cases hlin : denseIFLin (.add a b : DenseExpr p) [] with
    | none => simp only [hlin] at hk; exact Or.inl hk
    | some cr =>
      obtain ⟨c, raw⟩ := cr
      simp only [hlin] at hk
      cases hproc : denseIFProc half idx 0 (denseMergeTerms raw) with
      | none => simp only [hproc] at hk; exact Or.inl hk
      | some ts => simp only [hproc] at hk; exact general _ c raw ts hlin hproc k hk
  | .mul a b =>
    simp only at hk
    cases hlin : denseIFLin (.mul a b : DenseExpr p) [] with
    | none => simp only [hlin] at hk; exact Or.inl hk
    | some cr =>
      obtain ⟨c, raw⟩ := cr
      simp only [hlin] at hk
      cases hproc : denseIFProc half idx 0 (denseMergeTerms raw) with
      | none => simp only [hproc] at hk; exact Or.inl hk
      | some ts => simp only [hproc] at hk; exact general _ c raw ts hlin hproc k hk

/-- Every key one bounded slot emits states a truth about the assignment. -/
theorem denseIFSlot_sound [NeZero p] (idx : Std.HashMap VarId Nat) (B : Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p) (hidx : ∀ v b, idx[v]? = some b → (denv v).val < b)
    (hB : (e.eval denv).val < B) (st : DenseIFAcc) :
    ∀ k ∈ (denseIFSlot ((p - 1) / 2) (p : Int) idx B e st).keys,
      k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  have general : ∀ (e' : DenseExpr p) (c : ZMod p) (raw : List (VarId × ZMod p))
      (ts : List DenseIFTerm), (e'.eval denv).val < B → denseIFLin e' [] = some (c, raw) →
      denseIFProc ((p - 1) / 2) idx 0 (denseMergeTerms raw) = some ts →
      ∀ k ∈ (denseIFRun (p : Int) B (denseIFSrep ((p - 1) / 2) c) ts st).keys,
        k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
    intro e' c raw ts hB' hlin hproc k hk
    obtain ⟨l, hl, hlc, hlt⟩ := denseIFLin_spec e' c raw hlin
    obtain ⟨hval, hw⟩ := denseIFProc_val idx denv hidx 0 (denseMergeTerms raw) ts hproc
    have hcast : ((denseIFSrep ((p - 1) / 2) c + denseIFVal denv ts : Int) : ZMod p)
        = e'.eval denv := by
      push_cast
      rw [denseIFSrep_eq, srep_cast, hval, denseMergeTerms_eval, denseLinearize_eval e' l hl denv]
      rw [← hlc, ← hlt]
      rfl
    exact denseIFRun_sound B _ ts denv (e'.eval denv) hw hcast hB' st k hk
  intro k hk
  unfold denseIFSlot at hk
  match e with
  | .const _ => exact Or.inl hk
  | .var x =>
    simp only at hk
    cases hb : idx[x]? with
    | none => simp only [hb] at hk; exact Or.inl hk
    | some Bv =>
      simp only [hb] at hk
      have hvb : (denv x).val < Bv := hidx x Bv hb
      have hw : ∀ t ∈ [denseIFTermOf ((p - 1) / 2) (zmodOneP p) Bv x],
          t.mn ≤ t.sc * ((denv t.v).val : Int) ∧
          t.sc * ((denv t.v).val : Int) ≤ t.mx := by
        intro t ht
        rw [List.mem_singleton] at ht
        subst ht
        rw [denseIFTermOf_v]
        exact denseIFTermOf_window (zmodOneP p) Bv x denv hvb
      have hcast : ((0 + denseIFVal denv [denseIFTermOf ((p - 1) / 2) (zmodOneP p) Bv x] : Int)
          : ZMod p) = (DenseExpr.var x : DenseExpr p).eval denv := by
        have hsc : (denseIFTermOf ((p - 1) / 2) (zmodOneP p) Bv x).sc = srep (zmodOneP p) := rfl
        simp only [denseIFVal, denseIFTermOf_v, hsc, zero_add]
        push_cast
        rw [srep_cast, zmodOneP_eq, ZMod.natCast_val, ZMod.cast_id, one_mul]
        simp [DenseExpr.eval]
      exact denseIFRun_sound B 0 _ denv _ hw hcast hB st k hk
  | .add a b =>
    simp only at hk
    cases hlin : denseIFLin (.add a b : DenseExpr p) [] with
    | none => simp only [hlin] at hk; exact Or.inl hk
    | some cr =>
      obtain ⟨c, raw⟩ := cr
      simp only [hlin] at hk
      cases hproc : denseIFProc ((p - 1) / 2) idx 0 (denseMergeTerms raw) with
      | none => simp only [hproc] at hk; exact Or.inl hk
      | some ts => simp only [hproc] at hk; exact general _ c raw ts hB hlin hproc k hk
  | .mul a b =>
    simp only at hk
    cases hlin : denseIFLin (.mul a b : DenseExpr p) [] with
    | none => simp only [hlin] at hk; exact Or.inl hk
    | some cr =>
      obtain ⟨c, raw⟩ := cr
      simp only [hlin] at hk
      cases hproc : denseIFProc ((p - 1) / 2) idx 0 (denseMergeTerms raw) with
      | none => simp only [hproc] at hk; exact Or.inl hk
      | some ts => simp only [hproc] at hk; exact general _ c raw ts hB hlin hproc k hk


/-! ## The prepared interaction sweep

Both consumers of the sweep — the collected slots and the bounds index — are justified by the same
witness: the entry came from a payload slot of a member interaction whose multiplicity is a nonzero
constant and whose slot the facts bound. `denseIFSlotWit_bound` turns that into the value bound via
`BusFacts.slotBound_sound`. -/

def DenseIFSlotWit (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (e : DenseExpr p) (B : Nat) : Prop :=
  ∃ bi ∈ bis, ∃ mval, bi.multiplicity.constValue? = some mval ∧ mval ≠ 0 ∧
    ∃ j, bi.payload[j]? = some e ∧
      facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) j = some B

theorem denseIFSlotWit_bound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.accepts (denseBIEval bi denv))
    (e : DenseExpr p) (B : Nat) (h : DenseIFSlotWit bs facts bis e B) :
    (e.eval denv).val < B := by
  obtain ⟨bi, hbi, mval, hmc, hmz, j, hpe, hsb⟩ := h
  have hmeval : (denseBIEval bi denv).multiplicity = mval :=
    bi.multiplicity.constValue?_sound mval hmc denv
  have hv : bs.accepts (denseBIEval bi denv) := hbus bi hbi (by rw [hmeval]; exact hmz)
  have hget : (denseBIEval bi denv).payload[j]? = some (e.eval denv) := by
    show (bi.payload.map (fun t => t.eval denv))[j]? = some (e.eval denv)
    rw [List.getElem?_map, hpe]
    rfl
  have hsb' : facts.slotBound (denseBIEval bi denv).busId (denseBIEval bi denv).multiplicity
      (bi.payload.map DenseExpr.constValue?) j = some B := by
    show facts.slotBound bi.busId (denseBIEval bi denv).multiplicity _ j = some B
    rw [hmeval]
    exact hsb
  exact facts.slotBound_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?) j B
    (e.eval denv) hsb' (denseMatches_evalPattern bi.payload denv) hv hget

theorem denseIFSlotWit_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (e : DenseExpr p) (B : Nat)
    (h : DenseIFSlotWit bs facts bis e B) : ∃ bi ∈ bis, e ∈ bi.payload := by
  obtain ⟨bi, hbi, _, _, _, j, hpe, _⟩ := h
  exact ⟨bi, hbi, List.mem_of_getElem? hpe⟩

theorem denseIFIdxInsert_spec (idx : Std.HashMap VarId Nat) (x : VarId) (B : Nat) :
    ∀ y B', (denseIFIdxInsert idx x B)[y]? = some B' → idx[y]? = some B' ∨ (y = x ∧ B' = B) := by
  intro y B' h
  unfold denseIFIdxInsert at h
  have hins : ∀ m : Std.HashMap VarId Nat, (m.insert x B)[y]? = some B' →
      m[y]? = some B' ∨ (y = x ∧ B' = B) := by
    intro m hm
    rw [Std.HashMap.getElem?_insert] at hm
    by_cases hxy : (x == y) = true
    · rw [if_pos hxy] at hm
      simp only [Option.some.injEq] at hm
      have hxy' : x = y := by simpa using hxy
      exact Or.inr ⟨hxy'.symm, hm.symm⟩
    · rw [if_neg hxy] at hm
      exact Or.inl hm
  split at h
  · split_ifs at h with hlt
    · exact hins idx h
    · exact Or.inl h
  · exact hins idx h

/-- One interaction's payload walk: every slot it collects and every index entry it writes is
    witnessed by that interaction. -/
theorem denseIFPrepGo_spec {bs : BusSemantics p} (facts : BusFacts p bs) (sc1 : Int)
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p))
    (hbi : bi ∈ bis) (mval : ZMod p) (hmc : bi.multiplicity.constValue? = some mval)
    (hmz : mval ≠ 0) :
    ∀ (l : List (DenseExpr p)) (i : Nat), (∀ j, l[j]? = bi.payload[i + j]?) →
      ∀ st : DenseIFPrep p,
        (∀ eB ∈ (denseIFPrepGo bs facts sc1 bi.busId mval
            (bi.payload.map DenseExpr.constValue?) bi.payload l i st).slots,
          eB ∈ st.slots ∨ DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
        (∀ x B, (denseIFPrepGo bs facts sc1 bi.busId mval
            (bi.payload.map DenseExpr.constValue?) bi.payload l i st).idx[x]? = some B →
          st.idx[x]? = some B ∨ DenseIFSlotWit bs facts bis (DenseExpr.var x) B) := by
  intro l
  induction l with
  | nil => intro i _ st; exact ⟨fun eB h => Or.inl h, fun x B h => Or.inl h⟩
  | cons e rest ih =>
    intro i hsuf st
    have hpe : bi.payload[i]? = some e := by
      have := hsuf 0
      simpa using this.symm
    have hsuf' : ∀ j, rest[j]? = bi.payload[(i + 1) + j]? := by
      intro j
      have := hsuf (j + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    have hstep : (∀ eB ∈ (denseIFPrepSlot bs facts sc1 bi.busId mval
          (bi.payload.map DenseExpr.constValue?) bi.payload e i st).slots,
          eB ∈ st.slots ∨ DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
        (∀ x B, (denseIFPrepSlot bs facts sc1 bi.busId mval
          (bi.payload.map DenseExpr.constValue?) bi.payload e i st).idx[x]? = some B →
          st.idx[x]? = some B ∨ DenseIFSlotWit bs facts bis (DenseExpr.var x) B) := by
      have hwit : ∀ B, facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i
          = some B → DenseIFSlotWit bs facts bis e B := fun B hB =>
        ⟨bi, hbi, mval, hmc, hmz, i, hpe, hB⟩
      unfold denseIFPrepSlot
      match e with
      | .const _ => exact ⟨fun eB h => Or.inl h, fun x B h => Or.inl h⟩
      | .var x =>
        simp only
        cases hB : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
        | none => exact ⟨fun eB h => Or.inl h, fun y B h => Or.inl h⟩
        | some B =>
          simp only
          have hgen : ∀ (sl : List (DenseExpr p × Nat)) (ix : Std.HashMap VarId Nat),
              (sl = ((DenseExpr.var x : DenseExpr p), B) :: st.slots ∨ sl = st.slots) →
              (ix = denseIFIdxInsert st.idx x B ∨ ix = st.idx) →
              (∀ eB ∈ sl, eB ∈ st.slots ∨ DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
              (∀ y B', ix[y]? = some B' →
                st.idx[y]? = some B' ∨ DenseIFSlotWit bs facts bis (DenseExpr.var y) B') := by
            intro sl ix hsl hix
            constructor
            · intro eB h
              rcases hsl with rfl | rfl
              · rcases List.mem_cons.1 h with rfl | h'
                · exact Or.inr (hwit B hB)
                · exact Or.inl h'
              · exact Or.inl h
            · intro y B' h
              rcases hix with rfl | rfl
              · rcases denseIFIdxInsert_spec st.idx x B y B' h with h' | ⟨rfl, rfl⟩
                · exact Or.inl h'
                · exact Or.inr (hwit B' hB)
              · exact Or.inl h
          split_ifs <;>
            first
              | exact hgen _ _ (Or.inl rfl) (Or.inl rfl)
              | exact hgen _ _ (Or.inl rfl) (Or.inr rfl)
              | exact hgen _ _ (Or.inr rfl) (Or.inl rfl)
              | exact hgen _ _ (Or.inr rfl) (Or.inr rfl)
      | .add a b =>
        simp only
        cases hB : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
        | none => exact ⟨fun eB h => Or.inl h, fun y B h => Or.inl h⟩
        | some B =>
          refine ⟨fun eB h => ?_, fun y B' h => Or.inl h⟩
          rcases List.mem_cons.1 h with rfl | h'
          · exact Or.inr (hwit B hB)
          · exact Or.inl h'
      | .mul a b =>
        simp only
        cases hB : facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
        | none => exact ⟨fun eB h => Or.inl h, fun y B h => Or.inl h⟩
        | some B =>
          refine ⟨fun eB h => ?_, fun y B' h => Or.inl h⟩
          rcases List.mem_cons.1 h with rfl | h'
          · exact Or.inr (hwit B hB)
          · exact Or.inl h'
    obtain ⟨hrec1, hrec2⟩ := ih (i + 1) hsuf'
      (denseIFPrepSlot bs facts sc1 bi.busId mval (bi.payload.map DenseExpr.constValue?)
        bi.payload e i st)
    refine ⟨fun eB h => ?_, fun x B h => ?_⟩
    · rcases hrec1 eB (by rw [denseIFPrepGo] at h; exact h) with h' | h'
      · exact hstep.1 eB h'
      · exact Or.inr h'
    · rcases hrec2 x B (by rw [denseIFPrepGo] at h; exact h) with h' | h'
      · exact hstep.2 x B h'
      · exact Or.inr h'

theorem denseIFPrepBi_spec {bs : BusSemantics p} (facts : BusFacts p bs) (sc1 : Int)
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p))
    (hbi : bi ∈ bis) (st : DenseIFPrep p) :
    (∀ eB ∈ (denseIFPrepBi bs facts sc1 st bi).slots,
      eB ∈ st.slots ∨ DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
    (∀ x B, (denseIFPrepBi bs facts sc1 st bi).idx[x]? = some B →
      st.idx[x]? = some B ∨ DenseIFSlotWit bs facts bis (DenseExpr.var x) B) := by
  unfold denseIFPrepBi
  cases hmc : bi.multiplicity.constValue? with
  | none => exact ⟨fun eB h => Or.inl h, fun x B h => Or.inl h⟩
  | some mval =>
    simp only
    split_ifs with hz
    · exact ⟨fun eB h => Or.inl h, fun x B h => Or.inl h⟩
    · exact denseIFPrepGo_spec facts sc1 bis bi hbi mval hmc (by simpa using hz)
        bi.payload 0 (by intro j; simp) st

theorem denseIFPrep_spec {bs : BusSemantics p} (facts : BusFacts p bs) (sc1 : Int)
    (bis : List (BusInteraction (DenseExpr p))) :
    (∀ eB ∈ (denseIFPrep bs facts sc1 bis).slots, DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
    (∀ x B, (denseIFPrep bs facts sc1 bis).idx[x]? = some B →
      DenseIFSlotWit bs facts bis (DenseExpr.var x) B) := by
  have go : ∀ (rest : List (BusInteraction (DenseExpr p))), (∀ bi ∈ rest, bi ∈ bis) →
      ∀ st : DenseIFPrep p,
        (∀ eB ∈ (rest.foldl (denseIFPrepBi bs facts sc1) st).slots,
          eB ∈ st.slots ∨ DenseIFSlotWit bs facts bis eB.1 eB.2) ∧
        (∀ x B, (rest.foldl (denseIFPrepBi bs facts sc1) st).idx[x]? = some B →
          st.idx[x]? = some B ∨ DenseIFSlotWit bs facts bis (DenseExpr.var x) B) := by
    intro rest
    induction rest with
    | nil => intro _ st; exact ⟨fun eB h => Or.inl h, fun x B h => Or.inl h⟩
    | cons bi rest' ih =>
      intro hmem st
      have hstep := denseIFPrepBi_spec facts sc1 bis bi (hmem bi (List.mem_cons_self ..)) st
      obtain ⟨h1, h2⟩ := ih (fun b hb => hmem b (List.mem_cons_of_mem _ hb))
        (denseIFPrepBi bs facts sc1 st bi)
      refine ⟨fun eB h => ?_, fun x B h => ?_⟩
      · rcases h1 eB (by simpa using h) with h' | h'
        · exact hstep.1 eB h'
        · exact Or.inr h'
      · rcases h2 x B (by simpa using h) with h' | h'
        · exact hstep.2 x B h'
        · exact Or.inr h'
  obtain ⟨h1, h2⟩ := go bis (fun _ h => h) ⟨[], ∅⟩
  refine ⟨fun eB h => ?_, fun x B h => ?_⟩
  · rcases h1 eB h with h' | h'
    · exact absurd h' (by simp)
    · exact h'
  · rcases h2 x B h with h' | h'
    · rw [Std.HashMap.getElem?_empty] at h'; exact absurd h' (by simp)
    · exact h'

/-! ## The two seed folds -/

theorem denseIFSlots_keys (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) :
    ∀ (l : List (DenseExpr p × Nat)) (st : DenseIFAcc),
      ∀ k ∈ (denseIFSlots half pI idx l st).keys,
        k ∈ st.keys ∨ ∃ eB ∈ l,
          (⟨k.a⟩ : VarId) ∈ eB.1.vars ∧ (k.b = 0 ∨ (⟨k.b - 1⟩ : VarId) ∈ eB.1.vars) := by
  intro l
  induction l with
  | nil => intro st k hk; exact Or.inl hk
  | cons eB rest ih =>
    intro st k hk
    rw [denseIFSlots] at hk
    rcases ih _ k hk with h | ⟨eB', hmem, h⟩
    · rcases denseIFSlot_vars half pI idx eB.2 eB.1 st k h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨eB, List.mem_cons_self .., h'⟩
    · exact Or.inr ⟨eB', List.mem_cons_of_mem _ hmem, h⟩

theorem denseIFSlots_sound [NeZero p] (idx : Std.HashMap VarId Nat) (denv : VarId → ZMod p)
    (hidx : ∀ v b, idx[v]? = some b → (denv v).val < b) :
    ∀ (l : List (DenseExpr p × Nat)), (∀ eB ∈ l, (eB.1.eval denv).val < eB.2) →
      ∀ st : DenseIFAcc,
        ∀ k ∈ (denseIFSlots ((p - 1) / 2) (p : Int) idx l st).keys,
          k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  intro l
  induction l with
  | nil => intro _ st k hk; exact Or.inl hk
  | cons eB rest ih =>
    intro hb st k hk
    rw [denseIFSlots] at hk
    rcases ih (fun e' he' => hb e' (List.mem_cons_of_mem _ he')) _ k hk with h | h
    · exact denseIFSlot_sound idx eB.2 eB.1 denv hidx (hb eB (List.mem_cons_self ..)) st k h
    · exact Or.inr h

theorem denseIFConstraintSeeds_keys (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) :
    ∀ (l : List (DenseExpr p)) (st : DenseIFAcc),
      ∀ k ∈ (denseIFConstraintSeeds half pI idx l st).keys,
        k ∈ st.keys ∨ ∃ c ∈ l,
          (⟨k.a⟩ : VarId) ∈ c.vars ∧ (k.b = 0 ∨ (⟨k.b - 1⟩ : VarId) ∈ c.vars) := by
  intro l
  induction l with
  | nil => intro st k hk; exact Or.inl hk
  | cons c rest ih =>
    intro st k hk
    rw [denseIFConstraintSeeds] at hk
    rcases ih _ k hk with h | ⟨c', hmem, h⟩
    · rcases denseIFSlot_vars half pI idx 1 c st k h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨c, List.mem_cons_self .., h'⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hmem, h⟩

theorem denseIFConstraintSeeds_sound [NeZero p] (idx : Std.HashMap VarId Nat)
    (denv : VarId → ZMod p) (hidx : ∀ v b, idx[v]? = some b → (denv v).val < b) :
    ∀ (l : List (DenseExpr p)), (∀ c ∈ l, c.eval denv = 0) → ∀ st : DenseIFAcc,
      ∀ k ∈ (denseIFConstraintSeeds ((p - 1) / 2) (p : Int) idx l st).keys,
        k ∈ st.keys ∨ DenseIFKeyHolds denv k := by
  intro l
  induction l with
  | nil => intro _ st k hk; exact Or.inl hk
  | cons c rest ih =>
    intro hc st k hk
    rw [denseIFConstraintSeeds] at hk
    rcases ih (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) _ k hk with h | h
    · have h1 : (c.eval denv).val < 1 := by
        rw [hc c (List.mem_cons_self ..), ZMod.val_zero]
        omega
      exact denseIFSlot_sound idx 1 c denv hidx h1 st k h
    · exact Or.inr h

/-! ## Materializing a key -/

theorem denseIFExprOf_vars (negOne : ZMod p) (k : DenseIFKey) :
    ∀ z ∈ (denseIFExprOf negOne k : DenseExpr p).vars,
      z = (⟨k.a⟩ : VarId) ∨ (k.b ≠ 0 ∧ z = (⟨k.b - 1⟩ : VarId)) := by
  intro z hz
  unfold denseIFExprOf at hz
  split_ifs at hz with hb
  · simp only [DenseExpr.vars, List.mem_singleton] at hz
    exact Or.inl hz
  · simp only [DenseExpr.vars, List.mem_append, List.mem_singleton, List.nil_append] at hz
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hb, h⟩

theorem denseIFExprOf_eval [NeZero p] (denv : VarId → ZMod p) (k : DenseIFKey)
    (h : DenseIFKeyHolds denv k) :
    (denseIFExprOf (zmodNegOneP p) k : DenseExpr p).eval denv = 0 := by
  unfold denseIFExprOf
  split_ifs with hb
  · show denv ⟨k.a⟩ = 0
    exact h.1 hb
  · show denv ⟨k.a⟩ + (zmodNegOneP p) * denv ⟨k.b - 1⟩ = 0
    rw [zmodNegOneP_eq, h.2 hb]
    ring

/-! ## The pass -/

theorem denseIFKeys_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ k ∈ denseIFKeys bs facts d,
      (⟨k.a⟩ : VarId) ∈ d.occ ∧ (k.b = 0 ∨ (⟨k.b - 1⟩ : VarId) ∈ d.occ) := by
  intro k hk
  rw [denseIFKeys] at hk
  have hk' := List.mem_reverse.1 hk
  have hbus : ∀ e : DenseExpr p, (∃ bi ∈ d.busInteractions, e ∈ bi.payload) →
      ∀ y ∈ e.vars, y ∈ d.occ := by
    intro e he y hy
    obtain ⟨bi, hbi, hep⟩ := he
    exact List.mem_append_right _ (List.mem_flatMap.2
      ⟨bi, hbi, List.mem_append_right _ (List.mem_flatMap.2 ⟨e, hep, hy⟩)⟩)
  have hcs : ∀ e : DenseExpr p, e ∈ d.algebraicConstraints → ∀ y ∈ e.vars, y ∈ d.occ := by
    intro e he y hy
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨e, he, hy⟩)
  rcases denseIFConstraintSeeds_keys _ _ _ d.algebraicConstraints _ k hk' with h | ⟨e, he, h⟩
  · rcases denseIFSlots_keys _ _ _ _ _ k h with h' | ⟨eB, heB, h'⟩
    · exact absurd h' (by simp)
    · have hwit := (denseIFPrep_spec facts (denseIFSrep ((p - 1) / 2) (zmodOneP p))
        d.busInteractions).1 eB (List.mem_reverse.1 heB)
      have hmem := denseIFSlotWit_mem facts d.busInteractions eB.1 eB.2 hwit
      exact ⟨hbus eB.1 hmem _ h'.1, h'.2.imp id (fun hh => hbus eB.1 hmem _ hh)⟩
  · exact ⟨hcs e he _ h.1, h.2.imp id (fun hh => hcs e he _ hh)⟩

theorem denseIFKeys_sound [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    ∀ k ∈ denseIFKeys bs facts d, DenseIFKeyHolds denv k := by
  intro k hk
  rw [denseIFKeys] at hk
  have hk' := List.mem_reverse.1 hk
  have hbus : ∀ bi ∈ d.busInteractions, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.accepts (denseBIEval bi denv) := fun bi hbi => hsat.2 bi hbi
  have hidx : ∀ v b,
      (denseIFPrep bs facts (denseIFSrep ((p - 1) / 2) (zmodOneP p)) d.busInteractions).idx[v]?
        = some b → (denv v).val < b := by
    intro v b hb
    exact denseIFSlotWit_bound facts d.busInteractions denv hbus (DenseExpr.var v) b
      ((denseIFPrep_spec facts (denseIFSrep ((p - 1) / 2) (zmodOneP p)) d.busInteractions).2 v b hb)
  have hslots : ∀ eB ∈ (denseIFPrep bs facts (denseIFSrep ((p - 1) / 2) (zmodOneP p))
      d.busInteractions).slots.reverse, (eB.1.eval denv).val < eB.2 := fun eB heB =>
    denseIFSlotWit_bound facts d.busInteractions denv hbus eB.1 eB.2
      ((denseIFPrep_spec facts (denseIFSrep ((p - 1) / 2) (zmodOneP p)) d.busInteractions).1 eB
        (List.mem_reverse.1 heB))
  rcases denseIFConstraintSeeds_sound _ denv hidx d.algebraicConstraints
    (fun c' hc' => hsat.1 c' hc') _ k hk' with h | h
  · rcases denseIFSlots_sound _ denv hidx _ hslots _ k h with h' | h'
    · exact absurd h' (by simp)
    · exact h'
  · exact h

theorem denseIntervalForceNew_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseIntervalForceNew bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  simp only [denseIntervalForceNew] at hc
  split_ifs at hc with hp0 hempty
  · exact absurd hc (by simp)
  · exact absurd hc (by simp)
  obtain ⟨k, hkmem, rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2⟩ := denseIFKeys_vars bs facts d k (List.mem_of_mem_filter hkmem)
  rcases denseIFExprOf_vars (zmodNegOneP p) k z hz with rfl | ⟨hbne, rfl⟩
  · exact h1
  · exact h2.resolve_left hbne

theorem denseIntervalForceNew_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseIntervalForceNew bs facts d, c.eval denv = 0 := by
  intro c hc
  simp only [denseIntervalForceNew] at hc
  split_ifs at hc with hp0 hempty
  · exact absurd hc (by simp)
  · exact absurd hc (by simp)
  haveI : NeZero p := ⟨hp0⟩
  obtain ⟨k, hkmem, rfl⟩ := List.mem_map.1 hc
  exact denseIFExprOf_eval denv k
    (denseIFKeys_sound bs facts d denv hsat k (List.mem_of_mem_filter hkmem))

/-- The dense `intervalForce` pass: appends the entailed interval-forcing seeds. -/
def denseIntervalForcePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofAddConstraints denseIntervalForceNew denseIntervalForceNew_vars
    (fun bs facts d denv _ hsat => denseIntervalForceNew_sound bs facts d denv hsat)

end ApcOptimizer.Dense
