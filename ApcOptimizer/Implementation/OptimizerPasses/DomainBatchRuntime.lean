import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch

set_option autoImplicit false

/-! # Dense `domainBatch`, with value-only box points

Box enumeration, the compiled survivor predicate, and the scan use **value-only points**
(`List (ZMod p)`, positionally aligned with a `keys : List VarId` computed once per target): nothing
on the enumeration path reads a key from a point, so carrying one would only cost a per-point key
scan. The shrinking candidate set is a fixed-length mask `List (Option (ZMod p))` aligned with
`keys`; `denseForcedOverV` zips it back with `keys` once at the end. Everything off the per-point
path (domain table, inverted index, compiler, dedup key, substitution) is reused from
`DomainBatch.lean` and `Gauss.lean`. Runtime-only: no proof obligations here. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Value-only positional lookup and compiled evaluation -/

/-- Positional lookup in a value-only point (position alone determines the value). -/
def denseLookupIxV (zero : ZMod p) : List (ZMod p) → Nat → ZMod p
  | [], _ => zero
  | v :: _, 0 => v
  | _ :: rest, i + 1 => denseLookupIxV zero rest i

/-- `IExpr.evalWith`, over a value-only point (hoisted `add`/`mul`). -/
def denseIExprEvalWithV (ops : DenseZModOps p) (pt : List (ZMod p)) :
    IExpr p → ZMod p
  | .const n => n
  | .ix i => denseLookupIxV ops.zero pt i
  | .add a b => ops.add (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)
  | .mul a b => ops.mul (denseIExprEvalWithV ops pt a) (denseIExprEvalWithV ops pt b)

def DenseBytePredKind.Holds (kind : DenseBytePredKind) (a b r : ZMod p) : Prop :=
  match kind with
  | .xor => r.val = Nat.xor a.val b.val
  | .pair => r = 0
  | .or => r.val = Nat.lor a.val b.val
  | .and => r.val = Nat.land a.val b.val

def denseBytePredRelationV (isZero : ZMod p → Bool) (kind : DenseBytePredKind)
    (a b r : ZMod p) : Bool :=
  match kind with
  | .xor => decide (r.val = Nat.xor a.val b.val)
  | .pair => isZero r
  | .or => decide (r.val = Nat.lor a.val b.val)
  | .and => decide (r.val = Nat.land a.val b.val)

/-- A compiled bus obligation. Supported exact facts evaluate scalar slots directly; `fallback`
    retains the opaque semantics for every other bus. -/
inductive DenseCBiPred (p : ℕ) where
  | always
  | varRange (mult x width : IExpr p)
  | varRangeConst (mult x : IExpr p) (bound : Nat)
  | tupleRange (mult x y : IExpr p) (boundX boundY : Nat)
  | fixedRange (mult value : IExpr p) (bound : Nat)
  | byte (mult o1 o2 result : IExpr p) (bound : Nat) (kind : DenseBytePredKind)
  | fallback (cbi : CBi p)

def denseCompileRangeCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (compiledMult : IExpr p) : Option (DenseCBiPred p) :=
  match bi.multiplicity.constValue? with
  | some mult =>
    if mult = 1 then
      match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some value => (denseCompileE keys value).map (fun iv => .fixedRange compiledMult iv bound)
        | none => none
      | none => none
    else none
  | none => none

def denseCompileByteCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) : Option (DenseCBiPred p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | none => none
    | some (op, o1, o2, result) =>
      match op.constValue?, denseCompileE keys o1, denseCompileE keys o2,
          denseCompileE keys result with
      | some opValue, some io1, some io2, some iresult =>
        if opValue = spec.xorOp then some (.byte mult io1 io2 iresult spec.bound .xor)
        else if opValue = spec.pairOp then some (.byte mult io1 io2 iresult spec.bound .pair)
        else
          match spec.orOp, spec.andOp with
          | some orOp, _ =>
            if opValue = orOp then some (.byte mult io1 io2 iresult spec.bound .or)
            else match spec.andOp with
              | some andOp =>
                if opValue = andOp then some (.byte mult io1 io2 iresult spec.bound .and) else none
              | none => none
          | none, some andOp =>
            if opValue = andOp then some (.byte mult io1 io2 iresult spec.bound .and) else none
          | none, none => none
      | _, _, _, _ => none

def denseCompileOtherCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) : Option (DenseCBiPred p) :=
  match denseCompileRangeCBiPredV facts keys bi mult with
  | some pred => some pred
  | none =>
    match denseCompileByteCBiPredV facts keys bi mult with
    | some pred => some pred
    | none => (denseCompileEs keys bi.payload).map (fun payload =>
        .fallback ⟨bi.busId, mult, payload⟩)

def denseCompilePairCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) (x width : DenseExpr p) :
    Option (DenseCBiPred p) :=
  match denseCompileE keys x, denseCompileE keys width with
  | some ix, some iwidth =>
    if facts.varRangeBus bi.busId then
      match width.constValue? with
      | some widthValue =>
        if widthValue.val ≤ 17 then some (.varRangeConst mult ix (2 ^ widthValue.val))
        else some (.varRange mult ix iwidth)
      | none => some (.varRange mult ix iwidth)
    else
      match facts.tupleRangeBus bi.busId with
      | some (boundX, boundY) => some (.tupleRange mult ix iwidth boundX boundY)
      | none => denseCompileOtherCBiPredV facts keys bi mult
  | _, _ => denseCompileOtherCBiPredV facts keys bi mult

def denseCompilePayloadCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs)
    (keys : List VarId) (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) :
    List (DenseExpr p) → Option (DenseCBiPred p)
  | [x, width] => denseCompilePairCBiPredV facts keys bi mult x width
  | _ => denseCompileOtherCBiPredV facts keys bi mult

/-- An interaction whose obligation is discharged for every point: a bus that never violates, or one
    checked for arity only (the VMs' instruction-table lookups) at its declared arity. Compiling
    these to `.always` keeps the opaque `bs.violatesConstraint` — a payload list and a message record
    per enumerated point — out of the scan. -/
def denseBiAlwaysOk {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  facts.neverViolates bi.busId || facts.neverViolatesArity bi.busId bi.payload.length

def denseCompileCBiPredV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseCBiPred p) :=
  if denseBiAlwaysOk facts bi then some .always
  else
    match denseCompileE keys bi.multiplicity with
    | none => none
    | some mult => denseCompilePayloadCBiPredV facts keys bi mult bi.payload

def denseCompileCBiPredsV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId) :
    List (BusInteraction (DenseExpr p)) → Option (List (DenseCBiPred p))
  | [] => some []
  | bi :: rest =>
    match denseCompileCBiPredV facts keys bi, denseCompileCBiPredsV facts keys rest with
    | some pred, some preds => some (pred :: preds)
    | _, _ => none

/-! ### The keys-free half of the compilation

`denseCompileCBiPredV` queries `facts` and re-decodes the payload for every gathered interaction of
every target, although only the `denseCompileE keys …` of a few slots depends on the target.
`denseClassifyBi` resolves the target-independent half once per interaction (in `denseBusPlansV`) and
`denseCompileBiShapeV` finishes it per target; `denseCompileBiShapeV_eq` (`Proofs/DomainBatch.lean`)
proves the two compose to `denseCompileCBiPredV`, so the compiled predicate — and the scan — is
unchanged. -/

def denseClassifyRange {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p × Nat) :=
  match bi.multiplicity.constValue? with
  | some mult =>
    if mult = 1 then
      match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some value => some (value, bound)
        | none => none
      | none => none
    else none
  | none => none

/-- The byte relation a constant op selects, or `none` if it selects no recognized relation. The
    arm order is `denseCompileByteCBiPredV`'s (`denseByteKindOf_eq` bridges the two). -/
def denseByteKindOf (spec : ByteXorSpec p) (opValue : ZMod p) : Option DenseBytePredKind :=
  if opValue = spec.xorOp then some .xor
  else if opValue = spec.pairOp then some .pair
  else
    match spec.orOp, spec.andOp with
    | some orOp, _ =>
      if opValue = orOp then some .or
      else match spec.andOp with
        | some andOp => if opValue = andOp then some .and else none
        | none => none
    | none, some andOp => if opValue = andOp then some .and else none
    | none, none => none

def denseClassifyByte {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) :
    Option (DenseExpr p × DenseExpr p × DenseExpr p × Nat × DenseBytePredKind) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | none => none
    | some (op, o1, o2, result) =>
      match op.constValue? with
      | none => none
      | some opValue =>
        (denseByteKindOf spec opValue).map (fun kind => (o1, o2, result, spec.bound, kind))

def denseClassifyOther {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : DenseBiOtherShape p :=
  { busId := bi.busId, range := denseClassifyRange facts bi, byte := denseClassifyByte facts bi,
    payload := bi.payload }

def denseClassifyBi {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : DenseBiPredShape p :=
  if denseBiAlwaysOk facts bi then .always
  else
    match bi.payload with
    | [x, width] =>
      if facts.varRangeBus bi.busId then
        .varRange x width
          (match width.constValue? with
           | some widthValue => if widthValue.val ≤ 17 then some (2 ^ widthValue.val) else none
           | none => none)
      else
        match facts.tupleRangeBus bi.busId with
        | some (boundX, boundY) => .tupleRange x width boundX boundY
        | none => .other (denseClassifyOther facts bi)
    | _ => .other (denseClassifyOther facts bi)

/-- Compile a decoded byte relation's three operand slots. -/
def denseCompileByteShapeV (keys : List VarId) (mult : IExpr p)
    (t : DenseExpr p × DenseExpr p × DenseExpr p × Nat × DenseBytePredKind) :
    Option (DenseCBiPred p) :=
  match denseCompileE keys t.1, denseCompileE keys t.2.1, denseCompileE keys t.2.2.1 with
  | some io1, some io2, some iresult => some (.byte mult io1 io2 iresult t.2.2.2.1 t.2.2.2.2)
  | _, _, _ => none

def denseCompileOtherShapeV (keys : List VarId) (mult : IExpr p) (o : DenseBiOtherShape p) :
    Option (DenseCBiPred p) :=
  match o.range.bind (fun vb =>
      (denseCompileE keys vb.1).map (fun iv => .fixedRange mult iv vb.2)) with
  | some pred => some pred
  | none =>
    match o.byte.bind (denseCompileByteShapeV keys mult) with
    | some pred => some pred
    | none => (denseCompileEs keys o.payload).map (fun payload =>
        .fallback ⟨o.busId, mult, payload⟩)

def denseCompileShapeV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (mult : IExpr p) :
    DenseBiPredShape p → Option (DenseCBiPred p)
  | .always => some .always
  | .varRange x width constBound =>
    match denseCompileE keys x, denseCompileE keys width with
    | some ix, some iwidth =>
      match constBound with
      | some bound => some (.varRangeConst mult ix bound)
      | none => some (.varRange mult ix iwidth)
    | _, _ => denseCompileOtherCBiPredV facts keys bi mult
  | .tupleRange x y boundX boundY =>
    match denseCompileE keys x, denseCompileE keys y with
    | some ix, some iy => some (.tupleRange mult ix iy boundX boundY)
    | _, _ => denseCompileOtherCBiPredV facts keys bi mult
  | .other o => denseCompileOtherShapeV keys mult o

/-- The per-target half: compile the slots a classified interaction needs against `keys`. -/
def denseCompileBiShapeV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId)
    (bi : BusInteraction (DenseExpr p)) (sh : DenseBiPredShape p) : Option (DenseCBiPred p) :=
  match sh with
  | .always => some .always
  | _ =>
    match denseCompileE keys bi.multiplicity with
    | none => none
    | some mult => denseCompileShapeV facts keys bi mult sh

/-- The gathered interactions and their classifications, walked in lockstep. -/
def denseCompileShapesV {bs : BusSemantics p} (facts : BusFacts p bs) (keys : List VarId) :
    List (BusInteraction (DenseExpr p)) → List (DenseBiPredShape p) →
    Option (List (DenseCBiPred p))
  | [], _ => some []
  | bi :: rest, sh :: shs =>
    match denseCompileBiShapeV facts keys bi sh, denseCompileShapesV facts keys rest shs with
    | some pred, some preds => some (pred :: preds)
    | _, _ => none
  | _ :: _, [] => none

def denseCBiPredEvalV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    {bs : BusSemantics p} (facts : BusFacts p bs) (pt : List (ZMod p)) : DenseCBiPred p → Bool
  | .always => true
  | .varRange mult x width =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else
      let xValue := denseIExprEvalWithV ops pt x
      let widthValue := denseIExprEvalWithV ops pt width
      decide (widthValue.val ≤ 17 ∧ xValue.val < 2 ^ widthValue.val)
  | .varRangeConst mult x bound =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt x).val < bound)
  | .tupleRange mult x y boundX boundY =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt x).val < boundX ∧
      (denseIExprEvalWithV ops pt y).val < boundY)
  | .fixedRange mult value bound =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else decide ((denseIExprEvalWithV ops pt value).val < bound)
  | .byte mult o1 o2 result bound kind =>
    let multValue := denseIExprEvalWithV ops pt mult
    if isZero multValue then true
    else
      let a := denseIExprEvalWithV ops pt o1
      let b := denseIExprEvalWithV ops pt o2
      let r := denseIExprEvalWithV ops pt result
      decide (a.val < bound ∧ b.val < bound) && denseBytePredRelationV isZero kind a b r
  | .fallback cbi =>
    let multValue := denseIExprEvalWithV ops pt cbi.mult
    if isZero multValue then true
    else
      facts.acceptsDec
        { busId := cbi.busId,
          multiplicity := multValue,
          payload := cbi.payload.map (fun ie => denseIExprEvalWithV ops pt ie) }

/-- `survivesAllCW`, over a value-only point: compiled items' zero test plus interactions'
    obligation check. -/
def denseSurvivesAllCWV (ops : DenseZModOps p) (isZero : ZMod p → Bool)
    {bs : BusSemantics p} (facts : BusFacts p bs) (ces : List (IExpr p))
    (cbis : List (DenseCBiPred p)) (pt : List (ZMod p)) : Bool :=
  ces.all (fun ie => isZero (denseIExprEvalWithV ops pt ie)) &&
    cbis.all (denseCBiPredEvalV ops isZero facts pt)

/-! ### The uncompiled fallback

Reached only if compilation fails — never for the covered items this pass compiles, so dead code
kept for totality. -/

/-- Value-only environment lookup against an explicit key list (fallback only; see above). -/
def denseEnvOfKeysV (keys : List VarId) (pt : List (ZMod p)) (y : VarId) : ZMod p :=
  match keys, pt with
  | [], _ => 0
  | _, [] => 0
  | x :: ks, v :: vs => if y == x then v else denseEnvOfKeysV ks vs y

/-- One source interaction's obligation over a value-only point. -/
def denseBiObligationV {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  let mult := bi.multiplicity.eval (denseEnvOfKeysV keys pt)
  if decide (mult = 0) then true
  else
    facts.acceptsDec
      { busId := bi.busId,
        multiplicity := mult,
        payload := bi.payload.map (fun e => e.eval (denseEnvOfKeysV keys pt)) }

/-- Fallback survivor predicate (see the fallback note above). -/
def denseSurvivesAllMV {bs : BusSemantics p} (facts : BusFacts p bs) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (keys : List VarId) (pt : List (ZMod p)) : Bool :=
  es.all (fun e => decide (e.eval (denseEnvOfKeysV keys pt) = 0)) &&
    bis.all (fun bi => denseBiObligationV facts bi keys pt)

/-- A per-target survivor predicate, boxed in a one-field structure so its setup (ring instances,
    compilation, `isZero` closure) runs once per target rather than being eta-expanded into the
    per-point call path. -/
structure DenseSurvV (p : ℕ) where
  /-- The per-point survivor test (see `DenseSurvV`). -/
  run : List (ZMod p) → Bool

/-- The per-point survivor predicate for a target over value-only points: compiles the covered
    items against `keys` once, hoisting ring ops and the zero test, with the uncompiled fallback if
    compilation fails. Boxed in `DenseSurvV` (see there). -/
def denseCompiledSurvV (bs : BusSemantics p) (facts : BusFacts p bs) (es : List (DenseExpr p))
    (bis : List (BusInteraction (DenseExpr p))) (shapes : List (DenseBiPredShape p))
    (keys : List VarId) :
    DenseSurvV p :=
  match denseCompileEs keys es, denseCompileShapesV facts keys bis shapes with
  | some ces, some cbis =>
    let ops : DenseZModOps p := denseZModOps
    let dec : DecidableEq (ZMod p) := inferInstance
    let isZero : ZMod p → Bool := fun v => @decide (v = ops.zero) (dec v ops.zero)
    ⟨fun pt => denseSurvivesAllCWV ops isZero facts ces cbis pt⟩
  | _, _ => ⟨denseSurvivesAllMV facts es bis keys⟩

/-! ## Value-only lazy box enumeration -/

/-- Stream the Cartesian product of the domains into `f` as value-only points (in `keys` order). -/
def denseBoxFoldV {β : Type} (ops : DenseZModOps p) (f : β → List (ZMod p) → β)
    (stop : β → Bool) :
    List (FiniteDomain p) → β → β
  | [], acc => if stop acc then acc else f acc []
  | d :: rest, acc =>
    denseBoxFoldV ops (fun acc' a =>
      d.foldElts ops.zero (fun v => ops.add v ops.one)
        (fun acc'' v => f acc'' (v :: a)) stop acc') stop rest acc

/-- `(assignments doms).all pred`, value-only (used by `denseConstraintRedundantV`). -/
def denseAllBoxV (pred : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) : Bool :=
  let ops : DenseZModOps p := denseZModOps
  denseBoxFoldV ops (fun acc pt => acc && pred pt) (fun acc => !acc) doms true

/-! ### The value-only box scan

The tracked candidate set is a fixed-length mask `List (Option (ZMod p))` aligned with `keys`:
`some c` while that position is still forced to `c` by every survivor so far, `none` once some
survivor disagreed. Ruling a candidate out is a positional `List.zipWith` turning its slot to
`none`; the scan aborts once every slot is `none`. -/

/-- The scan's tracked candidates: a fixed-length mask aligned with `keys`. -/
abbrev DenseCandsV (p : ℕ) := List (Option (ZMod p))

/-- One scan step: `none` while hunting the first survivor (initializes the mask from its point);
    `some cands` intersects the mask against a surviving point, unchanged otherwise. -/
def denseScanStepV (surv : List (ZMod p) → Bool) :
    Option (DenseCandsV p) → List (ZMod p) → Option (DenseCandsV p)
  | none, pt => if surv pt = true then some (pt.map some) else none
  | some cands, pt =>
    if surv pt = true then
      some (cands.zipWith
        (fun c v => match c with | some cv => if cv = v then some cv else none | none => none) pt)
    else some cands

/-- The dense scan aborts once every tracked candidate has been ruled out. -/
def denseScanStopV : Option (DenseCandsV p) → Bool
  | none => false
  | some cands => cands.all Option.isNone

/-- The value-only box scan, streamed lazily over the symbolic domains; the caller
    (`denseForcedOverV`) zips the final mask with `keys` once, after the scan finishes. -/
def denseScanBoxV (surv : List (ZMod p) → Bool) (doms : List (FiniteDomain p)) :
    Option (DenseCandsV p) :=
  let ops : DenseZModOps p := denseZModOps
  denseBoxFoldV ops (denseScanStepV surv) denseScanStopV doms none

/-! ## Redundancy check, value-only -/

/-- Is this constraint redundant for enumeration — identically zero on the box of its own
    variables' domains? -/
def denseConstraintRedundantV (T : DenseDomainTable p) (c : DenseExpr p) : Bool :=
  match T.doms (HashedDedup.hashedDedup (hash ·) c.vars) with
  | none => false
  | some d =>
    (d.map (fun yd => yd.2.size)).prod ≤ maxEnumSize &&
      match denseCompileE (d.map Prod.fst) c with
      | some ic =>
        let ops : DenseZModOps p := denseZModOps
        let dec : DecidableEq (ZMod p) := inferInstance
        denseAllBoxV
          (fun a => @decide (denseIExprEvalWithV ops a ic = ops.zero) (dec _ ops.zero))
          (d.map Prod.snd)
      | none =>
        denseAllBoxV (fun a => decide (c.eval (denseEnvOfKeysV (d.map Prod.fst) a) = 0))
          (d.map Prod.snd)

def denseDomainBelowV (d : FiniteDomain p) (bound : Nat) : Bool :=
  match d with
  | .explicit vs => vs.all (fun v => decide (v.val < bound))
  | .range size => decide (size ≤ bound)

def denseExprDomainBelowV (T : DenseDomainTable p) (e : DenseExpr p) (bound : Nat) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    match e with
    | .var i => match T.map[i]? with | some d => denseDomainBelowV d bound | none => false
    | _ => false

def denseRangeCheckDomainRedundantV {bs : BusSemantics p} (facts : BusFacts p bs)
    (T : DenseDomainTable p)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match bi.multiplicity.constValue? with
  | some mult =>
    if mult = 0 then true
    else if mult = 1 then
      match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some e => denseExprDomainBelowV T e bound
        | none => false
      | none => false
    else false
  | none => false

def denseConstBiV? (bi : BusInteraction (DenseExpr p)) : Option (BusInteraction (ZMod p)) := do
  let mult ← bi.multiplicity.constValue?
  let payload ← bi.payload.mapM DenseExpr.constValue?
  pure { busId := bi.busId, multiplicity := mult, payload }

def denseBytePairDomainRedundantV {bs : BusSemantics p} (facts : BusFacts p bs)
    (T : DenseDomainTable p) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec bi.busId with
  | none => false
  | some spec =>
    match spec.decode bi.payload with
    | none => false
    | some (op, o1, o2, result) =>
      match op.constValue?, result.constValue? with
      | some opValue, some resultValue =>
        opValue = spec.pairOp && resultValue = 0 &&
          denseExprDomainBelowV T o1 spec.bound && denseExprDomainBelowV T o2 spec.bound
      | _, _ => false

def denseBiDomainRedundantV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match denseConstBiV? bi with
  | some value => value.multiplicity = 0 || facts.acceptsDec value
  | none =>
    if facts.neverViolates bi.busId then true
    else
      match bi.payload with
      | [x, b] =>
        if facts.varRangeBus bi.busId then
          match b.constValue? with
          | some width =>
            if width.val ≤ 17 then denseExprDomainBelowV T x (2 ^ width.val) else false
          | none => false
        else
          match facts.tupleRangeBus bi.busId with
          | some (boundX, boundB) =>
            denseExprDomainBelowV T x boundX && denseExprDomainBelowV T b boundB
          | none => denseRangeCheckDomainRedundantV facts T bi ||
              denseBytePairDomainRedundantV facts T bi
      | _ => denseRangeCheckDomainRedundantV facts T bi ||
          denseBytePairDomainRedundantV facts T bi

def denseDomainConstantValueV? (d : FiniteDomain p) : Option (ZMod p) :=
  match d with
  | .explicit [] => none
  | .explicit (v :: vs) => if vs.all (fun w => decide (w = v)) then some v else none
  | .range size => if size = 1 then some 0 else none

def denseConstantDomainsV (fdoms : List (VarId × FiniteDomain p)) : List (VarId × ZMod p) :=
  fdoms.filterMap fun xd => (denseDomainConstantValueV? xd.2).map (fun c => (xd.1, c))

/-! ## `forcedOver`, value-only -/

structure DenseConstraintGatherV (p : ℕ) where
  fullCount : Nat
  active : List (DenseExpr p)

def denseGatherConstraintAtV (arr : Array (DenseConstraintPlan p)) (xs : List VarId)
    (acc : DenseConstraintGatherV p) (i : Nat) : DenseConstraintGatherV p :=
  if h : i < arr.size then
    let plan := arr[i]
    if denseVarsInListF xs plan.vars then
      { fullCount := acc.fullCount + 1,
        active := if plan.active then plan.expr :: acc.active else acc.active }
    else acc
  else acc

def denseGatherConstraintArrayV (arr : Array (DenseConstraintPlan p)) (xs : List VarId)
    (positions : Array Nat) (acc : DenseConstraintGatherV p) : DenseConstraintGatherV p :=
  positions.foldl (denseGatherConstraintAtV arr xs) acc

def denseGatherConstraintsV (fidx : DenseForcedIdx p) (xs : List VarId) :
    DenseConstraintGatherV p :=
  let acc := xs.foldl (fun acc v =>
    denseGatherConstraintArrayV fidx.arrCs xs (fidx.csIdx.buckets.getD v #[]) acc)
    ⟨fidx.csIdx.inactiveVarlessCount, []⟩
  denseGatherConstraintArrayV fidx.arrCs xs fidx.csIdx.activeVarless acc

structure DenseBusGatherV (p : ℕ) where
  count : Nat
  informative : Bool
  allDomainRedundant : Bool
  interactions : List (BusInteraction (DenseExpr p))
  /-- The gathered interactions' classifications, in the same order (`denseCompileShapesV`). -/
  shapes : List (DenseBiPredShape p)

def denseGatherBusAtV (arr : Array (DenseBusPlan p)) (xs : List VarId)
    (acc : DenseBusGatherV p) (i : Nat) : DenseBusGatherV p :=
  if h : i < arr.size then
    let plan := arr[i]
    if plan.usable && denseVarsInListF xs plan.vars then
      { count := acc.count + 1,
        informative := acc.informative || plan.informative,
        allDomainRedundant := acc.allDomainRedundant && plan.domainRedundant,
        interactions := plan.interaction :: acc.interactions,
        shapes := plan.predShape :: acc.shapes }
    else acc
  else acc

def denseGatherBusArrayV (arr : Array (DenseBusPlan p)) (xs : List VarId)
    (positions : Array Nat) (acc : DenseBusGatherV p) : DenseBusGatherV p :=
  positions.foldl (denseGatherBusAtV arr xs) acc

def denseGatherBusesV (fidx : DenseForcedIdx p) (xs : List VarId) : DenseBusGatherV p :=
  let acc := xs.foldl (fun acc v =>
    denseGatherBusArrayV fidx.arrBis xs (fidx.bisIdx.buckets.getD v #[]) acc)
    ⟨0, false, true, [], []⟩
  denseGatherBusArrayV fidx.arrBis xs fidx.bisIdx.varless acc

structure DenseForcedScanV (p : ℕ) where
  keys : List VarId
  doms : List (FiniteDomain p)
  active : List (DenseExpr p)
  interactions : List (BusInteraction (DenseExpr p))
  shapes : List (DenseBiPredShape p)
  work : Nat

inductive DenseForcedPlanV (p : ℕ) where
  | done (forced : List (VarId × ZMod p))
  | scan (job : DenseForcedScanV p)

def DenseForcedPlanV.work : DenseForcedPlanV p → Nat
  | .done _ => 0
  | .scan job => job.work

def DenseForcedPlanV.needsScan : DenseForcedPlanV p → Bool
  | .done _ => false
  | .scan _ => true

/-- Apply every per-target gate before scheduling and retain only immediate results or real scans. -/
def denseForcedPreflightV (T : DenseDomainTable p) (fidx : DenseForcedIdx p)
    (xs : List VarId) : Option (DenseForcedPlanV p) :=
  match T.doms xs with
  | none => none
  | some fdoms =>
    let boxSize := (fdoms.map (fun yd => yd.2.size)).prod
    if boxSize ≤ maxEnumSize then
      let cs := denseGatherConstraintsV fidx xs
      let bis := denseGatherBusesV fidx xs
      let informative := cs.fullCount != 0 || bis.informative
      if informative && boxSize * (cs.fullCount + bis.count) ≤ maxEnumWork then
        let keys := fdoms.map Prod.fst
        let doms := fdoms.map Prod.snd
        if cs.active.isEmpty && bis.allDomainRedundant &&
            doms.all (fun d => d.size != 0) then
          some (.done (denseConstantDomainsV fdoms))
        else
          some (.scan {
            keys,
            doms,
            active := cs.active,
            interactions := bis.interactions,
            shapes := bis.shapes,
            work := boxSize * (cs.active.length + bis.count + keys.length) })
      else none
    else none

def denseRunForcedScanV (bs : BusSemantics p) (facts : BusFacts p bs)
    (job : DenseForcedScanV p) : List (VarId × ZMod p) :=
  let survC := denseCompiledSurvV bs facts job.active job.interactions job.shapes job.keys
  match denseScanBoxV survC.run job.doms with
  | none => job.keys.map (fun x => (x, (0 : ZMod p)))
  | some cands =>
    (job.keys.zip cands).filterMap (fun xc => xc.2.map (fun c => (xc.1, c)))

def denseRunForcedPlanV (bs : BusSemantics p) (facts : BusFacts p bs) :
    DenseForcedPlanV p → List (VarId × ZMod p)
  | .done forced => forced
  | .scan job => denseRunForcedScanV bs facts job

/-- All checked forced constants over `xs`, factored through the scheduler's preflight plan. -/
def denseForcedOverV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (fidx : DenseForcedIdx p) (xs : List VarId) : List (VarId × ZMod p) :=
  match denseForcedPreflightV T fidx xs with
  | none => []
  | some plan => denseRunForcedPlanV bs facts plan

/-! ## `collectForced`, value-only

Targets are deduplicated (`denseVarSetKey`) then folded in order; the independent per-target
enumerations can be spawned in parallel on large systems. -/

/-- The `seen`-deduplicated target list, keyed by `denseVarSetKey`: keeps the first target with
    each distinct variable set and drops later repeats. -/
def denseDedupTargetsV :
    List (List VarId) → Std.HashSet (List VarId) → List (List VarId)
  | [], _ => []
  | xs :: rest, seen =>
    let key := denseVarSetKey xs
    if seen.contains key then denseDedupTargetsV rest seen
    else xs :: denseDedupTargetsV rest (seen.insert key)

-- `denseDedupTargetsV` keeps both variables with equal names but distinct `VarId`s (distinct keys).
private def ddRegA : VarRegistry × VarId :=
  VarRegistry.empty.register { name := "x", powdrId? := some 1 }
private def ddRegB : VarRegistry × VarId :=
  ddRegA.1.register { name := "x", powdrId? := some 2 }
#guard denseDedupTargetsV [[ddRegA.2], [ddRegB.2]] ∅ == [[ddRegA.2], [ddRegB.2]]

def domainBatchParallelChunks : Nat := 64

def denseTakeForcedChunkV (budget : Nat) :
    List (DenseForcedPlanV p) → Nat → List (DenseForcedPlanV p) × List (DenseForcedPlanV p)
  | [], _ => ([], [])
  | plan :: rest, used =>
    if used != 0 && budget < used + plan.work then ([], plan :: rest)
    else
      let tail := denseTakeForcedChunkV budget rest (used + plan.work)
      (plan :: tail.1, tail.2)

def denseForcedChunksV (budget : Nat) : Nat → List (DenseForcedPlanV p) →
    List (List (DenseForcedPlanV p))
  | _, [] => []
  | 0, plans => [plans]
  | splits + 1, plans =>
    let chunk := denseTakeForcedChunkV budget plans 0
    chunk.1 :: denseForcedChunksV budget splits chunk.2

def denseRunForcedChunkV (bs : BusSemantics p) (facts : BusFacts p bs)
    (chunk : List (DenseForcedPlanV p)) : List (List (VarId × ZMod p)) :=
  chunk.map (denseRunForcedPlanV bs facts)

def denseForcedChunkTaskV (bs : BusSemantics p) (facts : BusFacts p bs)
    (chunk : List (DenseForcedPlanV p)) : Task (List (List (VarId × ZMod p))) :=
  if chunk.any DenseForcedPlanV.needsScan then
    Task.spawn fun _ => denseRunForcedChunkV bs facts chunk
  else
    Task.pure (denseRunForcedChunkV bs facts chunk)

def denseInsertForcedV (dσ : DenseSolved p) (forced : List (VarId × ZMod p)) : DenseSolved p :=
  dσ.insertAll (forced.map (fun f => (f.1, DenseExpr.const f.2)))

/-- Preflight targets, then run real scans in at most `domainBatchParallelChunks` ordered tasks. -/
def denseCollectForcedV (bs : BusSemantics p) (facts : BusFacts p bs)
    (T : DenseDomainTable p) (fidx : DenseForcedIdx p) (parallel : Bool)
    (targets : List (List VarId)) (seen : Std.HashSet (List VarId)) (dσ0 : DenseSolved p) :
    DenseSolved p :=
  let uniq := denseDedupTargetsV targets seen
  let plans := uniq.filterMap (denseForcedPreflightV T fidx)
  if parallel then
    let totalWork := plans.foldl (fun total plan => total + plan.work) 0
    let budget := max 1 ((totalWork + domainBatchParallelChunks - 1) /
      domainBatchParallelChunks)
    let chunks := denseForcedChunksV budget (domainBatchParallelChunks - 1) plans
    let tasks := chunks.map (denseForcedChunkTaskV bs facts)
    (tasks.flatMap Task.get).foldl denseInsertForcedV dσ0
  else
    plans.foldl (fun dσ plan => denseInsertForcedV dσ (denseRunForcedPlanV bs facts plan)) dσ0

/-! ## The pass transform, value-only -/

def denseConstraintPlansV (T : DenseDomainTable p) (cs : List (DenseExpr p)) :
    List (DenseConstraintPlan p) :=
  cs.map fun c =>
    { expr := c,
      vars := HashedDedup.hashedDedup (hash ·) c.vars,
      active := !denseConstraintRedundantV T c }

def denseBusPlansV (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseDomainTable p)
    (bis : List (BusInteraction (DenseExpr p))) : List (DenseBusPlan p) :=
  bis.map fun bi =>
    let usable := !bs.isStateful bi.busId
    { interaction := bi,
      vars := HashedDedup.hashedDedup (hash ·) (denseBIVars bi),
      usable,
      informative := usable && denseBiInformative bs facts bi,
      domainRedundant := usable && denseBiDomainRedundantV bs facts T bi,
      -- Only `usable` plans are gathered, so an unusable one needs no classification.
      predShape := if usable then denseClassifyBi facts bi else .always }

def densePlanTargetsV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    List (List VarId) :=
  cs.map (fun c => c.vars) ++ bis.map (fun bi => bi.vars)

def denseFreezeBuckets (buckets : Std.HashMap VarId (List Nat)) :
    Std.HashMap VarId (Array Nat) :=
  buckets.fold (fun out v positions => out.insert v positions.toArray) ∅

def denseFreezeCovIndex (idx : DenseCovIndex) : DenseArrayCovIndex :=
  { buckets := denseFreezeBuckets idx.buckets,
    varless := idx.varless.toArray }

def denseConstraintCovIndexV (cs : List (DenseConstraintPlan p)) : DenseConstraintCovIndex :=
  let arr := cs.toArray
  let idx := denseAnchorCovBuild (fun c => c.vars) cs
  let summary := idx.varless.foldl (init := (0, #[])) fun acc i =>
    if h : i < arr.size then
      if arr[i].active then (acc.1, acc.2.push i) else (acc.1 + 1, acc.2)
    else acc
  { buckets := denseFreezeBuckets idx.buckets,
    inactiveVarlessCount := summary.1,
    activeVarless := summary.2 }

def denseForcedIdxV (cs : List (DenseConstraintPlan p)) (bis : List (DenseBusPlan p)) :
    DenseForcedIdx p :=
  { csIdx := denseConstraintCovIndexV cs,
    arrCs := cs.toArray,
    bisIdx := denseFreezeCovIndex (denseAnchorCovBuild (fun bi => bi.vars) bis),
    arrBis := bis.toArray }

/-- Is `op` a recognized byte-relation selector for `spec`? Every such op guarantees both operands
    are below `spec.bound` (`BusFacts.byteXorSpec_sound` / `byteBoolSound`). -/
def denseByteOpBounds (spec : ByteXorSpec p) (op : ZMod p) : Bool :=
  decide (op = spec.xorOp) || decide (op = spec.pairOp) ||
    spec.orOp.any (fun o => decide (op = o)) || spec.andOp.any (fun a => decide (op = a))

/-- The single-variable affine form `(x, a, b)` with `e = a·x + b` and `a ≠ 0`, or `none`. -/
def denseAffineOfExpr (e : DenseExpr p) : Option (VarId × ZMod p × ZMod p) :=
  (denseLinearize e).bind (fun l =>
    match l.norm.terms with
    | [(x, a)] => if a = 0 then none else some (x, a, l.norm.const)
    | _ => none)

/-- The domain a byte operand `e` (known `< bound`) entails for its variable. A bare variable is in
    `[0, bound)`; an affine operand `a·x + b < bound` confines `x` to the `bound`-element coset
    `{(v - b)·a⁻¹ : v < bound}`. Either way it has exactly `bound` elements (`denseByteOperandVar`
    reads off the variable without materializing the coset). -/
def denseByteOperandDomain (e : DenseExpr p) (bound : Nat) : Option (VarId × FiniteDomain p) :=
  match e with
  | .var i => some (i, .range bound)
  | _ => (denseAffineOfExpr e).map (fun t =>
      (t.1, .explicit (((List.range bound).map (Nat.cast : Nat → ZMod p)).map
        (fun z => (z - t.2.2) * t.2.1⁻¹))))

/-- The variable a byte operand `e` confines — the first component of `denseByteOperandDomain`, read
    without building the `bound`-element coset (`denseByteOperandDomain e bound = some (i, _)` iff
    `denseByteOperandVar e = some i`). Used to gate the coset build below. -/
def denseByteOperandVar (e : DenseExpr p) : Option VarId :=
  match e with
  | .var i => some i
  | _ => (denseAffineOfExpr e).map (·.1)

/-- Insert the entailed operand domains of a byte interaction whose op is a recognized relation
    selector: both operands are then below `spec.bound`, sound by `BusFacts.byteXorSpec_sound` /
    `byteBoolSound`. Refine-only: the coset (size exactly `spec.bound`) is built and inserted only
    when it strictly refines the operand variable's existing table entry (`spec.bound < d0.size`).
    A missing entry, or one already at most `spec.bound`, is left untouched — the same table
    `insertEntry` would have produced, but without materializing a coset that would be discarded.
    This shrinks a 16-bit limb's `.range 65536` down to `spec.bound` while skipping byte-width
    operands whose variables are already bounded, avoiding wasted enumeration and coset builds. -/
def denseAddByteVarDoms (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (T : DenseDomainTable p) : DenseDomainTable p :=
  match bi.multiplicity.constValue? with
  | none => T
  | some mult =>
    if mult = 0 then T else
    match facts.byteXorSpec bi.busId with
    | none => T
    | some spec =>
      match spec.decode bi.payload with
      | none => T
      | some (op, o1, o2, _) =>
        match op.constValue? with
        | none => T
        | some opv =>
          if denseByteOpBounds spec opv then
            let ins := fun (e : DenseExpr p) (T0 : DenseDomainTable p) =>
              match denseByteOperandVar e with
              | none => T0
              | some i =>
                match T0.map[i]? with
                | none => T0
                | some d0 =>
                  if spec.bound < d0.size then
                    match denseByteOperandDomain e spec.bound with
                    | some (i', d) => T0.insertEntry i' d
                    | none => T0
                  else T0
            ins o2 (ins o1 T)
          else T

def denseAddByteDoms (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → DenseDomainTable p → DenseDomainTable p
  | [], T => T
  | bi :: rest, T => denseAddByteDoms bs facts rest (denseAddByteVarDoms bs facts bi T)

/-- Domain-batch: builds a finite domain per variable (from constraints like `x*(x-1)=0` giving
    `x ∈ {0,1}`, and from bus range checks), enumerates the small Cartesian product of those
    domains, and for each variable that takes the same value in every surviving assignment infers
    that forced constant. Returns the map of all such `var := const` substitutions. -/
def denseDomainBatchσV (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseSolved p :=
  let T : DenseDomainTable p :=
    denseAddByteDoms bs facts d.busInteractions
      (denseAddBusDoms bs facts d.busInteractions
        (denseAddConstraintDoms d.algebraicConstraints DenseDomainTable.empty))
  let csPlans := denseConstraintPlansV T d.algebraicConstraints
  let busPlans := denseBusPlansV bs facts T d.busInteractions
  let targets := densePlanTargetsV csPlans busPlans
  let fidx := denseForcedIdxV csPlans busPlans
  -- Fan out only at keccak/SHA scale; below it the sequential fold avoids spawn overhead.
  denseCollectForcedV bs facts T fidx (8192 ≤ d.algebraicConstraints.length) targets ∅
    DenseSolved.empty

/-- The value-only dense domain-batch transform. -/
def denseDomainBatchTransformV (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (denseDomainBatchσV bs facts d) d else d

end ApcOptimizer.Dense
