import ApcOptimizer.Implementation.OptimizerPasses.Rewrite

set_option autoImplicit false

/-! # Entailed-check rewriting: the generic transform

Several passes share one shape: recognize a stateless check whose acceptance is exactly the
vanishing of an entailed algebraic constraint, append those constraints, and drop the recognized
checks. `denseCheckRewriteF` is that transform over a recognizer list; the correctness skeleton
and the pass builders (`DenseVerifiedPassW.ofCheckRules`, `DenseVerifiedPassW.ofAddConstraints`)
live in `Proofs/EntailedCheck.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The recognizers' finds, grouped: recognizer `k` runs on the interactions unmatched by the
    recognizers before it, and its constraints are listed after all of recognizer `k−1`'s — the
    order sequential per-recognizer passes would produce. -/
def denseGroupEmit (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  match recs with
  | [] => []
  | r :: rest => bis.filterMap r ++ denseGroupEmit rest (bis.filter (fun bi => (r bi).isNone))

/-- Append every recognized check's entailed constraint (grouped per recognizer), then drop the
    recognized checks. -/
def denseCheckRewriteF (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  ({ d with algebraicConstraints :=
      d.algebraicConstraints ++ denseGroupEmit recs d.busInteractions }
    : DenseConstraintSystem p).filterBus (fun bi => recs.all (fun r => (r bi).isNone))

/-! ## The fused single-sweep twin

`denseGroupEmit` runs each recognizer twice (`filterMap`, then `filter` to shrink the input of the
next one) and `filterBus` runs the whole set once more, so a two-rule pass applies five recognizers
per interaction. One sweep recording the first recognizer to fire carries all three answers. -/

/-- Index of the first recognizer that fires on `bi`, with its constraint; `k` is the index of the
    head of `recs`. -/
def denseFirstHit (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p))) (k : Nat)
    (bi : BusInteraction (DenseExpr p)) : Option (Nat × DenseExpr p) :=
  match recs with
  | [] => none
  | r :: rest =>
    match r bi with
    | some e => some (k, e)
    | none => denseFirstHit rest (k + 1) bi

/-- The hits over `bis`, in reverse interaction order; interactions no recognizer claims allocate
    nothing, which is the whole point on a pass that recognizes nothing in most invocations. -/
def denseScanHits (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) (acc : List (Nat × DenseExpr p)) :
    List (Nat × DenseExpr p) :=
  match bis with
  | [] => acc
  | bi :: rest =>
    match denseFirstHit recs 0 bi with
    | some ke => denseScanHits recs rest (ke :: acc)
    | none => denseScanHits recs rest acc

/-- Constraints of the hits claimed by the head recognizer. -/
def denseTakeHead (hits : List (Nat × DenseExpr p)) : List (DenseExpr p) :=
  hits.filterMap fun ke => if ke.1 = 0 then some ke.2 else none

/-- Drop the head recognizer's hits and renumber the rest, so the hits of `r :: rest` over `bis`
    become the hits of `rest` over the interactions `r` left behind (`denseUnshift_hits`). -/
def denseUnshift (hits : List (Nat × DenseExpr p)) : List (Nat × DenseExpr p) :=
  hits.filterMap fun ke => match ke.1 with | 0 => none | j + 1 => some (j, ke.2)

/-- Regroup interaction-ordered hits by recognizer, restoring `denseGroupEmit`'s order over a list
    as long as the number of hits rather than of interactions. -/
def denseRegroup (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (hits : List (Nat × DenseExpr p)) : List (DenseExpr p) :=
  match recs with
  | [] => []
  | _ :: rest => denseTakeHead hits ++ denseRegroup rest (denseUnshift hits)

def denseCheckRewriteFImpl (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  match denseScanHits recs d.busInteractions [] with
  | [] => d
  | hits =>
    { algebraicConstraints := d.algebraicConstraints ++ denseRegroup recs hits.reverse,
      busInteractions := d.busInteractions.filter fun bi => (denseFirstHit recs 0 bi).isNone }

/-! ### `denseCheckRewriteF = denseCheckRewriteFImpl` -/

/-- The hits over `bis` in interaction order — what `denseScanHits` accumulates reversed. -/
def denseHitsFrom (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p))) (k : Nat)
    (bis : List (BusInteraction (DenseExpr p))) : List (Nat × DenseExpr p) :=
  bis.filterMap (denseFirstHit recs k)

/-- Starting the numbering one higher shifts every index by one. -/
theorem denseFirstHit_succ (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (k : Nat) (bi : BusInteraction (DenseExpr p)) :
    denseFirstHit recs (k + 1) bi
      = (denseFirstHit recs k bi).map (fun ke => (ke.1 + 1, ke.2)) := by
  induction recs generalizing k with
  | nil => rfl
  | cons r rest ih =>
    rw [denseFirstHit, denseFirstHit]
    cases r bi with
    | none => exact ih (k + 1)
    | some e => rfl

theorem denseScanHits_eq (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) (acc : List (Nat × DenseExpr p)) :
    denseScanHits recs bis acc = (denseHitsFrom recs 0 bis).reverse ++ acc := by
  induction bis generalizing acc with
  | nil => rfl
  | cons bi rest ih =>
    rw [denseScanHits, denseHitsFrom, List.filterMap_cons]
    cases denseFirstHit recs 0 bi with
    | none => simpa [denseHitsFrom] using ih acc
    | some ke => simpa [denseHitsFrom, List.reverse_cons] using ih (ke :: acc)

theorem denseTakeHead_hits (r : BusInteraction (DenseExpr p) → Option (DenseExpr p))
    (rest : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) :
    denseTakeHead (denseHitsFrom (r :: rest) 0 bis) = bis.filterMap r := by
  induction bis with
  | nil => rfl
  | cons bi tail ih =>
    rw [denseHitsFrom, List.filterMap_cons, denseFirstHit, List.filterMap_cons]
    cases hr : r bi with
    | some e => simpa [denseTakeHead] using ih
    | none =>
      rw [denseFirstHit_succ]
      cases denseFirstHit rest 0 bi with
      | none => simpa [denseTakeHead] using ih
      | some ke => simpa [denseTakeHead] using ih

theorem denseUnshift_hits (r : BusInteraction (DenseExpr p) → Option (DenseExpr p))
    (rest : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) :
    denseUnshift (denseHitsFrom (r :: rest) 0 bis)
      = denseHitsFrom rest 0 (bis.filter fun bi => (r bi).isNone) := by
  induction bis with
  | nil => rfl
  | cons bi tail ih =>
    rw [denseHitsFrom, List.filterMap_cons, denseFirstHit]
    cases hr : r bi with
    | some e => simpa [denseUnshift, List.filter_cons, hr] using ih
    | none =>
      rw [denseFirstHit_succ, List.filter_cons_of_pos (by simp [hr])]
      cases hf : denseFirstHit rest 0 bi with
      | none => simpa [denseUnshift, denseHitsFrom, hf] using ih
      | some ke => simpa [denseUnshift, denseHitsFrom, hf] using ih

theorem denseRegroup_hits (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) :
    denseRegroup recs (denseHitsFrom recs 0 bis) = denseGroupEmit recs bis := by
  induction recs generalizing bis with
  | nil => rfl
  | cons r rest ih =>
    rw [denseRegroup, denseGroupEmit, denseTakeHead_hits, denseUnshift_hits, ih]

/-- `recs.all` over the recognizers is the sweep's own miss test. -/
theorem denseFirstHit_isNone (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p)))
    (k : Nat) (bi : BusInteraction (DenseExpr p)) :
    (denseFirstHit recs k bi).isNone = recs.all fun r => (r bi).isNone := by
  induction recs generalizing k with
  | nil => rfl
  | cons r rest ih =>
    rw [denseFirstHit, List.all_cons]
    cases r bi with
    | none => simpa using ih (k + 1)
    | some e => rfl

theorem denseRegroup_nil (recs : List (BusInteraction (DenseExpr p) → Option (DenseExpr p))) :
    denseRegroup recs ([] : List (Nat × DenseExpr p)) = [] := by
  induction recs with
  | nil => rfl
  | cons r rest ih => rw [denseRegroup, denseTakeHead, denseUnshift]; simpa using ih

@[csimp] theorem denseCheckRewriteF_eq_impl : @denseCheckRewriteF = @denseCheckRewriteFImpl := by
  funext q recs d
  rw [denseCheckRewriteFImpl, denseScanHits_eq, List.append_nil]
  have hkeep : (fun bi => recs.all fun r => (r bi).isNone)
      = fun bi => (denseFirstHit recs 0 bi).isNone :=
    funext fun bi => (denseFirstHit_isNone recs 0 bi).symm
  cases hh : (denseHitsFrom recs 0 d.busInteractions).reverse with
  | cons a t =>
    have hrev : (a :: t).reverse = denseHitsFrom recs 0 d.busInteractions := by
      rw [← hh, List.reverse_reverse]
    show denseCheckRewriteF recs d
      = { algebraicConstraints := d.algebraicConstraints ++ denseRegroup recs (a :: t).reverse,
          busInteractions := d.busInteractions.filter fun bi => (denseFirstHit recs 0 bi).isNone }
    rw [hrev, denseRegroup_hits, denseCheckRewriteF, DenseConstraintSystem.filterBus, hkeep]
  | nil =>
    have hnil : denseHitsFrom recs 0 d.busInteractions = [] := by
      simpa using congrArg List.reverse hh
    have hall : ∀ bi ∈ d.busInteractions, (recs.all fun r => (r bi).isNone) = true := by
      intro bi hbi
      rw [← denseFirstHit_isNone]
      have := List.filterMap_eq_nil_iff.1 (by simpa [denseHitsFrom] using hnil)
      simpa using this bi hbi
    show denseCheckRewriteF recs d = d
    rw [denseCheckRewriteF, DenseConstraintSystem.filterBus,
      List.filter_eq_self.2 hall, ← denseRegroup_hits, hnil, denseRegroup_nil, List.append_nil]

end ApcOptimizer.Dense
