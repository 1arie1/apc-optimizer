import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets

set_option autoImplicit false

/-! # Dense flagFold drop certificates: box tautology + pointwise duplicate

The two trusted certificates `flagFold` parts C and D read (`FlagFold.lean` assembles them;
soundness in `Proofs/FlagFoldDrops.lean`). `denseBtCert`'s `domOf` and `densePdKeep`'s `domIdx` are
both untrusted — the caller justifies the domains they report. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part B: box-tautology replacement (dense) -/

/-- The single-variable constraints of a list (the only `findDomainAlg` sources). -/
def denseSingleVarCs (all : List (DenseExpr p)) : List (DenseExpr p) :=
  all.filter (fun c => (HashedDedup.hashedEraseDups (hash ·) c.vars).length == 1)

def denseBtCertImpl (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p) : Bool :=
  let vs := HashedDedup.hashedEraseDups (hash ·) c.vars
  2 ≤ vs.length &&
  (let doms := vs.filterMap (fun v => (domOf v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = vs) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => zmodIsZero (c.eval (denseEnvOfFast pt))))

/-- Certificate: `c` mentions ≥ 2 distinct variables, `domOf` reports a finite domain for every
    one of them, the joint box is small, and `c` vanishes on all of it. `domOf` is untrusted here —
    soundness comes from the caller's justification of the domains it reports
    (`boxTautoReplace_denseCorrect`'s `hdomOf`). -/
def denseBtCert (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p) : Bool :=
  let vs := HashedDedup.hashedEraseDups (hash ·) c.vars
  2 ≤ vs.length &&
  (let doms := vs.filterMap (fun v => (domOf v).map (fun d => (v, d)))
   decide (doms.map Prod.fst = vs) &&
   decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
   (denseAssignments doms).all (fun pt => decide (c.eval (denseEnvOfFast pt) = 0)))

@[csimp] theorem denseBtCert_eq_impl : @denseBtCert = @denseBtCertImpl := by
  funext q domOf c
  simp [denseBtCert, denseBtCertImpl]

/-- Replace certified box tautologies by the trivial constraint `0`. -/
def DenseConstraintSystem.boxTautoReplaceWith (d : DenseConstraintSystem p)
    (domOf : VarId → Option (List (ZMod p))) : DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map (fun c =>
      if denseBtCert domOf c then DenseExpr.const 0 else c) }

/-! ## Part C: pointwise-duplicate stateless check removal (dense) -/

/-- Joint-box agreement: every joint variable of `R`/`R'` has a proven finite domain, the box is
    small, and the two expressions agree at every box point. -/
def denseBoxAgree (domIdx : Std.HashMap VarId (List (DenseExpr p))) (R R' : DenseExpr p) : Bool :=
  let jv := (R.vars ++ R'.vars).eraseDups
  let doms := jv.filterMap (fun v =>
    (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun d => (v, d)))
  decide (doms.map Prod.fst = jv) &&
  decide ((doms.map (fun vd => vd.2.length)).prod ≤ 32) &&
  (denseAssignments doms).all (fun pt =>
    decide (R.eval (denseEnvOfFast pt) = R'.eval (denseEnvOfFast pt)))

/-- Slot-pair certificate: the two expressions are syntactically equal, or decompose over the same
    carrier with the same constant coefficient and offsets agreeing on the joint domain box. -/
def denseSlotEqCert (domIdx : Std.HashMap VarId (List (DenseExpr p))) (e e' : DenseExpr p) : Bool :=
  e == e' ||
  e.vars.eraseDups.any (fun x =>
    e'.mentions x &&
    match e.splitAt x, e'.splitAt x with
    | some (k, R), some (k2, R') => k2 == k && denseBoxAgree domIdx R R'
    | _, _ => false)

/-- Full-message certificate: same bus, same constant multiplicity, pointwise-equal payloads. -/
def denseMsgEqCert (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (bi bi' : BusInteraction (DenseExpr p)) : Bool :=
  bi.busId == bi'.busId &&
  (match bi.multiplicity.constValue?, bi'.multiplicity.constValue? with
   | some m, some m' => m == m'
   | _, _ => false) &&
  bi.payload.length == bi'.payload.length &&
  (bi.payload.zip bi'.payload).all (fun ee => denseSlotEqCert domIdx ee.1 ee.2)

/-- Is `bi` the first of its pointwise class (no earlier certified twin)? -/
def densePdFirst (bs : BusSemantics p) (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match bis.findIdx? (fun b => b == bi) with
  | none => true
  | some i => (bis.take i).all (fun b => bs.isStateful b.busId || !(denseMsgEqCert domIdx b bi))

/-- Keep unless a *first-of-class* earlier stateless twin exists (depth-1 rule: the twin that
    justifies a drop is itself provably kept, so no chain induction is needed). -/
def densePdKeep (bs : BusSemantics p) (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId ||
  (match bis.findIdx? (fun b => b == bi) with
   | none => true
   | some i =>
     !((bis.take i).any (fun b => !bs.isStateful b.busId && denseMsgEqCert domIdx b bi
         && densePdFirst bs domIdx bis b)))

/-- Full-value hash of an interaction, for the dropped-value buckets. -/
def densePdValHash (bi : BusInteraction (DenseExpr p)) : UInt64 :=
  mixHash (hash bi.busId) (mixHash bi.multiplicity.bHash
    (bi.payload.foldl (fun h e => mixHash h e.bHash) 7))

/-- Drop `bi` iff its value bucket holds a certified dropped twin. The `{b // densePdKeep … = false}`
    subtype is load-bearing: each stored entry carries its own `densePdKeep = false` proof. -/
def densePdVerdictKeep {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match verdicts[densePdValHash bi]? with
  | some l => !(l.any (fun b => decide (b.val = bi)))
  | none => true

/-- A `densePdVerdictKeep` drop carries its certificate (the bucket entry equals `bi`). -/
theorem densePdVerdictKeep_false {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) (h : densePdVerdictKeep verdicts bi = false) : P bi := by
  unfold densePdVerdictKeep at h
  cases hv : verdicts[densePdValHash bi]? with
  | none => rw [hv] at h; simp at h
  | some l =>
    rw [hv] at h
    simp only [Bool.not_eq_false'] at h
    obtain ⟨b, _hb, hbe⟩ := List.any_eq_true.1 h
    exact of_decide_eq_true hbe ▸ b.property

end ApcOptimizer.Dense
