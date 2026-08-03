import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup

set_option autoImplicit false

/-! # Dense interval forcing (runtime, impl-only): integer-window analysis of bounded affine
slots. No soundness lemma here; the proof and wiring live in `Proofs/IntervalForce.lean`. -/

namespace IntervalForce

variable {p : ℕ}

/-! ## Signed-representative and window arithmetic (representation-independent) -/

/-- Signed minimal-magnitude integer representative: `c.val` when `c.val ≤ (p−1)/2`, else
    `c.val − p`. Gives scaled differences small-magnitude coefficients like `(256, −256)`. -/
def srep (c : ZMod p) : Int :=
  if c.val ≤ (p - 1) / 2 then (c.val : Int) else (c.val : Int) - (p : Int)

theorem srep_cast [NeZero p] (c : ZMod p) : ((srep c : Int) : ZMod p) = c := by
  unfold srep
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  · push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_self, sub_zero]

/-- Each term's signed value lies in the window `[min (sc·(B−1)) 0, max (sc·(B−1)) 0]`. -/
theorem term_window (sc d B : Int) (h0 : 0 ≤ d) (hd : d < B) :
    min (sc * (B - 1)) 0 ≤ sc * d ∧ sc * d ≤ max (sc * (B - 1)) 0 := by
  rcases le_or_gt 0 sc with hsc | hsc
  · exact ⟨le_trans (min_le_right _ _) (mul_nonneg hsc h0),
      le_trans (mul_le_mul_of_nonneg_left (by omega) hsc) (le_max_left _ _)⟩
  · refine ⟨le_trans (min_le_left _ _)
      (mul_le_mul_of_nonpos_left (by omega) (le_of_lt hsc)), ?_⟩
    have h1 : sc * d ≤ sc * 0 := mul_le_mul_of_nonpos_left h0 (le_of_lt hsc)
    rw [mul_zero] at h1
    exact le_trans h1 (le_max_right _ _)

/-- If the signed-representative integer value `S` reduces to a field element `x` with
    `x.val < B`, and the window `[lo, hi] ∋ S` satisfies `hi ≤ p − 1` and `lo ≥ B − p`, then
    `S = x.val` holds over ℤ — in particular `0 ≤ S < B`. -/
theorem int_window [NeZero p] (S : Int) (B : Nat) (x : ZMod p)
    (hcast : ((S : Int) : ZMod p) = x) (hx : x.val < B)
    (hlo : (B : Int) - (p : Int) ≤ S) (hhi : S ≤ (p : Int) - 1) : S = (x.val : Int) := by
  have hdvd : (p : Int) ∣ (S - (x.val : Int)) := by
    have hz : ((S - (x.val : Int) : Int) : ZMod p) = 0 := by
      push_cast
      rw [hcast, ZMod.natCast_val, ZMod.cast_id, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  obtain ⟨k, hk⟩ := hdvd
  have hxv : (0 : Int) ≤ (x.val : Int) := Int.natCast_nonneg _
  have hxvB : ((x.val : Int)) < (B : Int) := by exact_mod_cast hx
  have hp : (0 : Int) < (p : Int) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  -- `S − x.val = p·k` with `S − x.val ∈ (−p, p)` forces `k = 0`.
  rcases lt_trichotomy k 0 with hkn | rfl | hkp
  · exfalso
    have h2 : (p : Int) * k ≤ (p : Int) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_neg_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega
  · omega
  · exfalso
    have h2 : (p : Int) * 1 ≤ (p : Int) * k :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    rw [mul_one] at h2
    generalize hX : (p : Int) * k = X at hk h2
    omega

/-- Cap on the number of affine terms analyzed per slot. -/
def maxTerms : Nat := 32

end IntervalForce

namespace ApcOptimizer.Dense

open IntervalForce

variable {p : ℕ}

/-! ## Seed keys

A forced seed is only ever `x = 0` or `x − y = 0`, so it is carried as a key and turned into a
`DenseExpr` once, at the end, for the survivors only. `b = 0` is the zero arm on `⟨a⟩`;
`b = w + 1` is the pair arm `⟨a⟩ − ⟨w⟩`. -/

structure DenseIFKey where
  a : Nat
  b : Nat
deriving BEq, Hashable, DecidableEq, Inhabited

/-- The emitted keys in reverse emission order, with the same set mirrored for dedup. -/
structure DenseIFAcc where
  keys : List DenseIFKey
  seen : Std.HashSet DenseIFKey

def denseIFPush (st : DenseIFAcc) (k : DenseIFKey) : DenseIFAcc :=
  if st.seen.contains k then st else ⟨k :: st.keys, st.seen.insert k⟩

/-! ## Linearization with an early-aborting product

`denseIFLin` is `denseLinearizeAcc` (`Affine.lean`) with one change: when the left factor of a
product has terms, the right one only has to be *variable-free*, which `denseIFConst` decides by
aborting at the first `.var` instead of linearizing it. A product of two variables now fails after
one variable rather than after linearizing both factors. Proven equal in
`Proofs/IntervalForce.lean`. -/

/-- The constant value of a variable-free expression; `none` at the first `.var`. A `.var` leaf of a
    linearizable expression always contributes a raw term, even under a zero coefficient, so this is
    exactly `denseLinearize`'s "the other factor's term list is empty" test. -/
def denseIFConst : DenseExpr p → Option (ZMod p)
  | .const n => some n
  | .var _ => none
  | .add a b =>
    match denseIFConst a with
    | none => none
    | some x =>
      match denseIFConst b with
      | none => none
      | some y => some (zmodAdd x y)
  | .mul a b =>
    match denseIFConst a with
    | none => none
    | some x =>
      match denseIFConst b with
      | none => none
      | some y => some (zmodMul x y)

def denseIFLin : DenseExpr p → List (VarId × ZMod p) →
    Option (ZMod p × List (VarId × ZMod p))
  | .const n, acc => some (n, acc)
  | .var i, acc => some (zmodZeroP p, (i, zmodOneP p) :: acc)
  | .add a b, acc =>
    match denseIFLin b acc with
    | none => none
    | some (cb, acc') =>
      match denseIFLin a acc' with
      | none => none
      | some (ca, acc'') => some (zmodAdd ca cb, acc'')
  | .mul a b, acc =>
    match denseIFLin a [] with
    | none => none
    | some (ca, ta) =>
      if ta.isEmpty then
        match denseIFLin b [] with
        | none => none
        | some (cb, tb) => some (zmodMul ca cb, denseScaleAppend ca tb acc)
      else
        match denseIFConst b with
        | none => none
        | some cb => some (zmodMul cb ca, denseScaleAppend cb ta acc)

/-! ## Processed terms -/

/-- One merged term with its window contributions `mn = min (sc·(B−1)) 0`,
    `mx = max (sc·(B−1)) 0`, where `B` is the term variable's own bound. -/
structure DenseIFTerm where
  sc : Int
  mn : Int
  mx : Int
  v : VarId
deriving Inhabited, DecidableEq

/-- `srep` with `(p−1)/2` supplied by the caller. -/
def denseIFSrep (half : Nat) (c : ZMod p) : Int :=
  let v := c.val
  if v ≤ half then (v : Int) else (v : Int) - (p : Int)

def denseIFTermOf (half : Nat) (c : ZMod p) (Bv : Nat) (v : VarId) : DenseIFTerm :=
  let sc := denseIFSrep half c
  let w := sc * ((Bv : Int) - 1)
  ⟨sc, if w < 0 then w else 0, if 0 < w then w else 0, v⟩

/-- Pair every merged nonzero term with its variable's bound. `none` when more than `maxTerms`
    terms survive or a variable is unbounded — aborting at the first one, rather than processing
    the tail first. -/
def denseIFProc (half : Nat) (idx : Std.HashMap VarId Nat) (n : Nat) :
    List (VarId × ZMod p) → Option (List DenseIFTerm)
  | [] => some []
  | (v, c) :: rest =>
    if zmodIsZero c then denseIFProc half idx n rest
    else if maxTerms ≤ n then none
    else
      match idx[v]? with
      | none => none
      | some Bv =>
        match denseIFProc half idx (n + 1) rest with
        | none => none
        | some ts => some (denseIFTermOf half c Bv v :: ts)

/-! ## The window walk

`denseMinSum (seen ++ rest)` and its `max` twin are the *totals* minus the excluded terms, so with
`m = Σ mn` and `M = Σ mx` taken once every arm is O(1) arithmetic and the walk never rebuilds a
term list. The partner search keeps the first-match order of `seen ++ rest` by scanning `seen`
before `rest`. -/

def denseIFSumMn : List DenseIFTerm → Int
  | [] => 0
  | t :: rest => t.mn + denseIFSumMn rest

def denseIFSumMx : List DenseIFTerm → Int
  | [] => 0
  | t :: rest => t.mx + denseIFSumMx rest

def denseIFPartner (g : Int) : List DenseIFTerm → Option DenseIFTerm
  | [] => none
  | t :: rest => if t.sc == g then some t else denseIFPartner g rest

/-- `t` alone cannot be nonzero without pushing the sum out of `[0, B)`. -/
def denseIFZeroArm (B : Nat) (c0 m M : Int) (t : DenseIFTerm) (st : DenseIFAcc) : DenseIFAcc :=
  if (0 < t.sc ∧ (B : Int) ≤ t.sc + (c0 + (m - t.mn))) ∨
     (t.sc < 0 ∧ c0 + (M - t.mx) + t.sc < 0) then
    denseIFPush st ⟨t.v.index, 0⟩
  else st

/-- `t` and the first other term with coefficient `−t.sc` cannot differ without the same
    overflow. -/
def denseIFPairArm (B : Nat) (c0 m M : Int) (t : DenseIFTerm) (seen rest : List DenseIFTerm)
    (st : DenseIFAcc) : DenseIFAcc :=
  if 0 < t.sc then
    match (denseIFPartner (-t.sc) seen).or (denseIFPartner (-t.sc) rest) with
    | some u =>
      if (B : Int) ≤ t.sc + (c0 + (m - t.mn - u.mn)) ∧
         c0 + (M - t.mx - u.mx) - t.sc < 0 ∧ t.v ≠ u.v then
        denseIFPush st ⟨t.v.index, u.v.index + 1⟩
      else st
    | none => st
  else st

def denseIFStep (B : Nat) (c0 m M : Int) (t : DenseIFTerm) (seen rest : List DenseIFTerm)
    (st : DenseIFAcc) : DenseIFAcc :=
  denseIFPairArm B c0 m M t seen rest (denseIFZeroArm B c0 m M t st)

def denseIFWalk (B : Nat) (c0 m M : Int) :
    List DenseIFTerm → List DenseIFTerm → DenseIFAcc → DenseIFAcc
  | _, [], st => st
  | seen, t :: rest, st =>
    denseIFWalk B c0 m M (t :: seen) rest (denseIFStep B c0 m M t seen rest st)

/-- The integer-window gate plus the walk, shared by the general and the bare-variable slot arms. -/
def denseIFRun (pI : Int) (B : Nat) (c0 : Int) (ts : List DenseIFTerm) (st : DenseIFAcc) :
    DenseIFAcc :=
  if c0 + denseIFSumMx ts ≤ pI - 1 ∧ (B : Int) - pI ≤ c0 + denseIFSumMn ts then
    denseIFWalk B c0 (denseIFSumMn ts) (denseIFSumMx ts) [] ts st
  else st

/-- All seeds forced by one slot bounded by `B`: linearize, merge like terms, pair each variable
    with its own bound, check the integer window, and extract the zero/pair arms. For a slot that
    is a bare variable the term list is a singleton and is built directly. -/
def denseIFSlot (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) (B : Nat) (e : DenseExpr p)
    (st : DenseIFAcc) : DenseIFAcc :=
  match e with
  | .const _ => st
  | .var x =>
    match idx[x]? with
    | none => st
    | some Bv => denseIFRun pI B 0 [denseIFTermOf half (zmodOneP p) Bv x] st
  | _ =>
    match denseIFLin e [] with
    | none => st
    | some (c, raw) =>
      match denseIFProc half idx 0 (denseMergeTerms raw) with
      | none => st
      | some ts => denseIFRun pI B (denseIFSrep half c) ts st

/-! ## The prepared interaction sweep

One walk over the interactions computes the constant multiplicity and the constant-payload pattern
once per interaction and calls `slotBound` once per slot — the union of what the bounds index (bare
variable slots) and the seed sweep (every slot) each used to recompute for themselves. The bounded
slots are collected for the seed pass, which cannot start before the *whole* index is known. -/

structure DenseIFPrep (p : ℕ) where
  /-- Bounded slots as `(slot expression, bound)`, in reverse collection order. -/
  slots : List (DenseExpr p × Nat)
  idx : Std.HashMap VarId Nat

/-- A one-term walk has no partner, so only its zero arm can fire, and on coefficient
    `sc1 = srep 1` that arm's test does not mention the variable's own bound. A bare-variable slot
    failing this emits nothing and need not be collected — which is every `256`-bounded memory
    limb. -/
def denseIFVarLive (sc1 : Int) (B : Nat) : Bool :=
  (0 < sc1 ∧ (B : Int) ≤ sc1) ∨ sc1 < 0

/-- `true` when no slot before index `i` is literally `.var x` — `denseVarSlot`'s first-match
    semantics, which is the slot whose bound the index records for `x`. -/
def denseIFFirstAt (x : VarId) : List (DenseExpr p) → Nat → Bool
  | _, 0 => true
  | [], _ => true
  | e :: rest, n + 1 => if denseIsVarOf x e then false else denseIFFirstAt x rest n

/-- Record the bound for `x`, keeping the smaller of duplicates. -/
def denseIFIdxInsert (idx : Std.HashMap VarId Nat) (x : VarId) (B : Nat) :
    Std.HashMap VarId Nat :=
  match idx[x]? with
  | some old => if B < old then idx.insert x B else idx
  | none => idx.insert x B

/-- One payload slot. A literal constant slot linearizes to a term-free form: it is no seed and no
    index entry, so its bound is never asked for. -/
def denseIFPrepSlot (bs : BusSemantics p) (facts : BusFacts p bs) (sc1 : Int) (busId : Nat)
    (mval : ZMod p) (pat : List (Option (ZMod p))) (payload : List (DenseExpr p))
    (e : DenseExpr p) (i : Nat) (st : DenseIFPrep p) : DenseIFPrep p :=
  match e with
  | .const _ => st
  | _ =>
    match facts.slotBound busId mval pat i with
    | none => st
    | some B =>
      match e with
      | .var x =>
        let sl := if denseIFVarLive sc1 B then (e, B) :: st.slots else st.slots
        if denseIFFirstAt x payload i then ⟨sl, denseIFIdxInsert st.idx x B⟩
        else ⟨sl, st.idx⟩
      | _ => ⟨(e, B) :: st.slots, st.idx⟩

def denseIFPrepGo (bs : BusSemantics p) (facts : BusFacts p bs) (sc1 : Int) (busId : Nat)
    (mval : ZMod p) (pat : List (Option (ZMod p))) (payload : List (DenseExpr p)) :
    List (DenseExpr p) → Nat → DenseIFPrep p → DenseIFPrep p
  | [], _, st => st
  | e :: rest, i, st =>
    denseIFPrepGo bs facts sc1 busId mval pat payload rest (i + 1)
      (denseIFPrepSlot bs facts sc1 busId mval pat payload e i st)

def denseIFPrepBi (bs : BusSemantics p) (facts : BusFacts p bs) (sc1 : Int) (st : DenseIFPrep p)
    (bi : BusInteraction (DenseExpr p)) : DenseIFPrep p :=
  match bi.multiplicity.constValue? with
  | none => st
  | some mval =>
    if zmodIsZero mval then st
    else
      denseIFPrepGo bs facts sc1 bi.busId mval (bi.payload.map DenseExpr.constValue?) bi.payload
        bi.payload 0 st

def denseIFPrep (bs : BusSemantics p) (facts : BusFacts p bs) (sc1 : Int)
    (bis : List (BusInteraction (DenseExpr p))) : DenseIFPrep p :=
  bis.foldl (denseIFPrepBi bs facts sc1) ⟨[], ∅⟩

/-! ## The pass -/

def denseIFSlots (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) :
    List (DenseExpr p × Nat) → DenseIFAcc → DenseIFAcc
  | [], st => st
  | (e, B) :: rest, st => denseIFSlots half pI idx rest (denseIFSlot half pI idx B e st)

def denseIFConstraintSeeds (half : Nat) (pI : Int) (idx : Std.HashMap VarId Nat) :
    List (DenseExpr p) → DenseIFAcc → DenseIFAcc
  | [], st => st
  | c :: rest, st => denseIFConstraintSeeds half pI idx rest (denseIFSlot half pI idx 1 c st)

/-- The key of an algebraic constraint that already *is* a seed shape (`x` or `x − y`); `none`
    otherwise, decided at the top node. -/
def denseIFCsKey (negOneVal : Nat) : DenseExpr p → Option DenseIFKey
  | .var v => some ⟨v.index, 0⟩
  | .add (.var v) (.mul (.const c) (.var w)) =>
    if c.val == negOneVal then some ⟨v.index, w.index + 1⟩ else none
  | _ => none

def denseIFCsKeys (negOneVal : Nat) :
    List (DenseExpr p) → Std.HashSet DenseIFKey → Std.HashSet DenseIFKey
  | [], s => s
  | c :: rest, s =>
    match denseIFCsKey negOneVal c with
    | none => denseIFCsKeys negOneVal rest s
    | some k => denseIFCsKeys negOneVal rest (s.insert k)

/-- The dense expression a key stands for (`densePairDiff`'s shape for the pair arm). -/
def denseIFExprOf (negOne : ZMod p) (k : DenseIFKey) : DenseExpr p :=
  if k.b = 0 then .var ⟨k.a⟩
  else .add (.var ⟨k.a⟩) (.mul (.const negOne) (.var ⟨k.b - 1⟩))

/-- Every forced key of the system, in emission order: the bounded bus slots, then the algebraic
    constraints (each bounded by `1`). -/
def denseIFKeys (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List DenseIFKey :=
  let half := (p - 1) / 2
  let prep := denseIFPrep bs facts (denseIFSrep half (zmodOneP p)) d.busInteractions
  (denseIFConstraintSeeds half (p : Int) prep.idx d.algebraicConstraints
    (denseIFSlots half (p : Int) prep.idx prep.slots.reverse ⟨[], ∅⟩)).keys.reverse

/-- The entailed interval-forcing seeds: every slot bounded by a `BusFacts` fact — and every
    algebraic constraint, which is bounded by `1` — analyzed over the integers, deduplicated, and
    filtered against the constraints already present. Appended by the pass
    (`Proofs/IntervalForce.lean`). Every seed variable comes from a term of an item of `d`, so the
    occurrence test the obligation asks for needs no index. -/
def denseIntervalForceNew (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  if p = 0 then []
  else
    let ks := denseIFKeys bs facts d
    if ks.isEmpty then []
    else
      let cs := denseIFCsKeys (p - 1) d.algebraicConstraints ∅
      (ks.filter (fun k => !cs.contains k)).map (denseIFExprOf (zmodNegOneP p))

end ApcOptimizer.Dense
