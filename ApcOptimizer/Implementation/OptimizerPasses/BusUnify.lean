import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense consecutive-match bus unification (runtime transform for `busUnify`)

Impl-only (no soundness lemma). `denseBusUnifyF` matches the `denseF` shape
`DenseVerifiedPassW.of` (`Bridge.lean`) wraps directly.

The engine prepares every memory-bus interaction once (`denseBUPrep`) — the address slots'
constant value, linear form and two-root reductions, plus an order-insensitive *fingerprint* of
each form — then sweeps each bus once over an array of those records, proposing `(sendPos, recvPos)`
index pairs. The sweep is untrusted: `denseCheckPair` re-verifies every proposal, so the sweep uses
the fingerprint tests (integer comparisons, over-approximating a refutation only on a hash
collision) while the verifier uses the exact ones. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Address/equality helpers -/

def denseEqExprImpl (e2 e1 : DenseExpr p) : DenseExpr p :=
  .add e2 (.mul (.const (zmodNegOneP p)) e1)

/-- `e₂ - e₁` as a dense expression. -/
def denseEqExpr (e2 e1 : DenseExpr p) : DenseExpr p := .add e2 (.mul (.const (-1)) e1)

@[csimp] theorem denseEqExpr_eq_impl : @denseEqExpr = @denseEqExprImpl := by
  funext q e2 e1
  simp [denseEqExpr, denseEqExprImpl]

def denseMultConst (bi : BusInteraction (DenseExpr p)) : Option (ZMod p) :=
  bi.multiplicity.constValue?

def denseSetNewMult (ops : DenseZModOps p) (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => ops.one
  | .sendThenReceive => ops.negOne

def denseGetPreviousMult (ops : DenseZModOps p) (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => ops.negOne
  | .sendThenReceive => ops.one

theorem denseSetNewMult_eq (ops : DenseZModOps p) (shape : MemoryBusShape) :
    denseSetNewMult ops shape = shape.setNewMult := by
  cases shape with
  | mk addressFields direction => cases direction <;> simp [denseSetNewMult,
      MemoryBusShape.setNewMult, ops.one_eq, ops.negOne_eq]

theorem denseGetPreviousMult_eq (ops : DenseZModOps p) (shape : MemoryBusShape) :
    denseGetPreviousMult ops shape = -shape.setNewMult := by
  cases shape with
  | mk addressFields direction => cases direction <;> simp [denseGetPreviousMult,
      MemoryBusShape.setNewMult, ops.one_eq, ops.negOne_eq]

/-- Do the two sends carry equal constant address entries? -/
def denseAddrConstsEq (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.all (fun slot =>
    match S.payload[slot]?, S'.payload[slot]? with
    | some e, some e' =>
      decide (e = e') ||
      (match e.constValue?, e'.constValue? with
       | some c, some c' => c = c'
       | _, _ => false)
    | _, _ => false)

/-- The entailed conclusions: slot-wise equality of the receive's and the send's payloads,
    excluding the (constant, already-equal) address slots. -/
def denseMemEqConstraints (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p)) :
    List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => denseEqExpr ((Rt.payload[i]?).getD (.const 0)) ((S.payload[i]?).getD (.const 0)))

/-- Boxed twin: the `-1` of `denseEqExpr` and the `0` padding are `ZMod p` literals, so inside the
    slot `map` each one rebuilds the whole `CommRing (ZMod p)` chain per payload slot. -/
def denseMemEqConstraintsW (negOne pad : DenseExpr p) (shape : MemoryBusShape)
    (S Rt : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun i => decide (i ∉ shape.addressFields))).map
    (fun i => .add ((Rt.payload[i]?).getD pad) (.mul negOne ((S.payload[i]?).getD pad)))

def denseMemEqConstraintsFast (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p)) :
    List (DenseExpr p) :=
  denseMemEqConstraintsW (.const (-1)) (.const 0) shape S Rt

@[csimp] theorem denseMemEqConstraints_eq_fast :
    @denseMemEqConstraints = @denseMemEqConstraintsFast := by
  funext p shape S Rt; rfl

/-! ## Address inequality -/

/-- Some address slot carries provably-different constants: the two interactions provably have
    different addresses. -/
def denseAddrConstsNeq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match e.constValue?, e'.constValue? with
       | some c, some c' => decide (c ≠ c')
       | _, _ => false)
    | _, _ => false)

/-! ## A canonical address key -/

/-- A canonical address key. -/
structure DenseAddrKey (p : ℕ) where
  exprs : List (DenseExpr p)
deriving DecidableEq

instance : Hashable (DenseAddrKey p) :=
  ⟨fun k => k.exprs.foldl (fun h e => mixHash h e.bHash) 7⟩

def DenseAddrKey.allConst (k : DenseAddrKey p) : Bool :=
  k.exprs.all fun e => match e with
    | .const _ => true
    | _ => false

/-! ## Prepared address records

One record per memory-bus interaction, built once per invocation. `cval` / `lin` / `reds` are the
data the certificates of `AddrDiseq.lean` re-derive per compared pair; `linSig` / `redSig` are the
order-insensitive term signatures that let the sweep decide the same tests by comparing integers.
Two linear forms differ by a nonzero constant exactly when their normalized term lists agree and
their constants do not, so equal signature + different constant is `denseConstDiffNZ` up to a hash
collision — and a collision can only over-report a refutation, which the verifier catches. Both
branches of one two-root reduction differ by a constant, hence share one signature. -/

/-- The canonical form of a linear form's terms: merged, zero-dropped, sorted by variable. Two
    forms differ by a nonzero constant (`denseConstDiffNZ`) exactly when their canonical terms are
    equal and their constants are not, so this list *is* the affine/two-root comparison. -/
def denseBUTermKey (l : DenseLinExpr p) : List (VarId × ZMod p) :=
  l.norm.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))

/-- Hash *of the canonical key*, which gates the list compare: unequal hashes are unequal keys,
    and that is the overwhelmingly common case. Deriving it from the key rather than from the term
    list makes the gate's soundness `congrArg` and saves a second `norm`. -/
def denseBUKeyHash (k : List (VarId × ZMod p)) : UInt64 :=
  k.foldl (fun h t => mixHash h (mixHash (hash t.1) (hash t.2.val))) 0

structure DenseBUSlot (p : ℕ) where
  expr : DenseExpr p
  eHash : UInt64
  cval : Option (ZMod p)
  /-- Kept for `denseBUNonzeroNeq`, the one arm that needs the form itself. -/
  lin : Option (DenseLinExpr p)
  linSig : UInt64
  linKey : List (VarId × ZMod p)
  /-- Per two-root reduction: hash, canonical terms, and the two branches' constants. Both
      branches differ by a constant, so they share one key. -/
  reds : List (UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p)

/-- Prepared interaction: the multiplicity constant, one record per address slot, and the canonical
    address key. -/
structure DenseBUPre (p : ℕ) where
  mult : Option (ZMod p)
  slots : List (Option (DenseBUSlot p))
  key : Option (DenseAddrKey p)
  allConst : Bool

def denseBUSlotPrep (T : DenseTwoRootMap p) (e : DenseExpr p) : DenseBUSlot p :=
  let lin := denseLinearize e
  let key := match lin with | some L => denseBUTermKey L | none => []
  { expr := e, eHash := e.bHash, cval := e.constValue?
    lin := lin
    linKey := key
    linSig := denseBUKeyHash key
    reds := (densePtrReductions T e).map
      (fun r => let k := denseBUTermKey r.1; (denseBUKeyHash k, k, r.1.const, r.2.const)) }

/-- Assemble a prepared interaction from its slot records. -/
def denseBUOfSlots (bi : BusInteraction (DenseExpr p))
    (slots : List (Option (DenseBUSlot p))) : DenseBUPre p :=
  let key := (slots.foldr (fun so acc =>
    match acc, so with
    | some ks, some sp =>
      match sp.cval with
      | some c => some (.const c :: ks)
      | none => some (sp.expr :: ks)
    | _, _ => none) (some [])).map DenseAddrKey.mk
  { mult := denseMultConst bi
    slots := slots
    key := key
    allConst := match key with | some k => k.allConst | none => false }

def denseBUPrep (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bi : BusInteraction (DenseExpr p)) : DenseBUPre p :=
  denseBUOfSlots bi
    (shape.addressFields.map (fun slot => (bi.payload[slot]?).map (denseBUSlotPrep T)))

/-! ## The pairwise tests on prepared records

Slot-wise recursion (the lists are one entry per address field); a missing slot on either side
fails an `all` and skips an `any`, matching the originals' missing-slot arms. -/

@[specialize] def denseBUSlotsAny (f : DenseBUSlot p → DenseBUSlot p → Bool) :
    List (Option (DenseBUSlot p)) → List (Option (DenseBUSlot p)) → Bool
  | some sa :: as, some sb :: bs => f sa sb || denseBUSlotsAny f as bs
  | _ :: as, _ :: bs => denseBUSlotsAny f as bs
  | _, _ => false

@[specialize] def denseBUSlotsAll (f : DenseBUSlot p → DenseBUSlot p → Bool) :
    List (Option (DenseBUSlot p)) → List (Option (DenseBUSlot p)) → Bool
  | some sa :: as, some sb :: bs => f sa sb && denseBUSlotsAll f as bs
  | _ :: _, _ :: _ => false
  | _, _ => true

/-- `denseAddrConstsEq` on prepared records; the hash gates the deep structural compare. -/
def denseBUConstsEq (a b : DenseBUPre p) : Bool :=
  denseBUSlotsAll (fun sa sb =>
    (sa.eHash == sb.eHash && decide (sa.expr = sb.expr)) ||
    (match sa.cval, sb.cval with | some c, some c' => decide (c = c') | _, _ => false))
    a.slots b.slots

/-- `denseAddrConstsNeq` on prepared records. -/
def denseBUConstsNeq (a b : DenseBUPre p) : Bool :=
  denseBUSlotsAny (fun sa sb =>
    match sa.cval, sb.cval with | some c, some c' => decide (c ≠ c') | _, _ => false)
    a.slots b.slots

/-- `denseConstDiffNZ` on two prepared slots: the canonical keys agree and the constants do not.
    The hash short-circuits the list compare. -/
@[inline] def denseBUAffineNeqSlot (sa sb : DenseBUSlot p) : Bool :=
  match sa.lin, sb.lin with
  | some L, some L' =>
    (sa.linSig == sb.linSig && decide (sa.linKey = sb.linKey)) && decide (L.const ≠ L'.const)
  | _, _ => false

/-- One key compare per reduction pair decides all four branch differences, which differ only in
    their constants. -/
@[inline] def denseBUTwoRootNeqSlot (sa sb : DenseBUSlot p) : Bool :=
  sa.reds.any (fun r => sb.reds.any (fun r' =>
    ((r.1 == r'.1 && decide (r.2.1 = r'.2.1)) &&
      (decide (r.2.2.1 ≠ r'.2.2.1) && decide (r.2.2.1 ≠ r'.2.2.2))) &&
      (decide (r.2.2.2 ≠ r'.2.2.1) && decide (r.2.2.2 ≠ r'.2.2.2))))

/-- `denseAddrAffineNeq` on prepared records. -/
def denseBUAffineNeq (a b : DenseBUPre p) : Bool :=
  denseBUSlotsAny denseBUAffineNeqSlot a.slots b.slots

/-- `denseAddrTwoRootNeq` on prepared records. -/
def denseBUTwoRootNeq (a b : DenseBUPre p) : Bool :=
  denseBUSlotsAny denseBUTwoRootNeqSlot a.slots b.slots

/-- `denseDiffSumOver` over prepared slot pairs. -/
def denseBUDiffSum : List (Option (DenseBUSlot p) × Option (DenseBUSlot p)) →
    Option (DenseLinExpr p)
  | [] => some ⟨0, []⟩
  | s :: fs =>
    match denseBUDiffSum fs with
    | none => none
    | some acc =>
      match s with
      | (some sa, some sb) =>
        match sa.lin, sb.lin with
        | some lS, some lM => some ((lM.add (lS.scale (-1))).add acc)
        | _, _ => none
      | _ => none

/-- `denseAddrNonzeroNeq` on prepared records. Reached only by pairs no other arm decided (a few
    hundred per sweep), so it stays the exact subset scan in both the sweep and the verifier. -/
def denseBUNonzeroNeq (nw : DenseNonzeroWits p) (a b : DenseBUPre p) : Bool :=
  (a.slots.zip b.slots).sublists.any (fun sub =>
    match denseBUDiffSum sub with
    | some D =>
      (nw.index.getD (denseLinHash D) [] ++ nw.index.getD (denseLinHash (D.scale (-1))) []).any
        (fun g => denseIsZeroLin (D.add (g.scale (-1))) || denseIsZeroLin (D.add g))
    | none => false)

/-! ## The consumer sweep

One left-to-right pass over a bus's prepared array maintaining open send windows (`constOpen`,
keyed by canonical address; `symOpen`, tested against every message) and closing, excluding or
dropping them as later messages consume, exclude or block them. -/

/-- One message tested against one open window (consumer / excluded / blocker). -/
inductive DenseStepRes
  | consumer
  | excluded
  | blocker

/-- The sweep's classification: exact on the consumer and constant arms, signature-gated on the
    affine and two-root arms. A signature collision can only turn a blocker into an exclusion, so
    the window lives longer and the extra proposal is rejected by `denseCheckPair`. -/
def denseBUStepSig (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (prevMult : ZMod p)
    (a b : DenseBUPre p) : DenseStepRes :=
  if decide (b.mult = some prevMult) && denseBUConstsEq a b then .consumer
  else if denseBUConstsNeq a b || denseBUAffineNeq a b || denseBUTwoRootNeq a b
      || denseBUNonzeroNeq nw a b || decide (b.mult = some ops.zero) then .excluded
  else .blocker

/-- An open send window: its prepared record and its position. -/
structure DenseBUWin (p : ℕ) where
  pre : DenseBUPre p
  i : Nat

/-- The sweep. Returns the consumed windows as `(sendPos, recvPos)` pairs, in consume order. -/
def denseBUSweep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (arr : Array (DenseBUPre p)) :
    (fuel : Nat) → (j : Nat) →
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseBUWin p)) →
    (symOpen : List (DenseBUWin p)) →
    (out : List (Nat × Nat)) → List (Nat × Nat)
  | 0, _, _, _, out => out
  | fuel + 1, j, constOpen, symOpen, out =>
    match arr[j]? with
    | none => out
    | some mp =>
      -- (1) constant-keyed windows: an all-constant message meets only the window at its own key;
      --     a symbolic-address message is tested against every one.
      let (constOpen, out) :=
        if mp.allConst then
          match mp.key with
          | some k =>
            match constOpen[k]? with
            | some w =>
              match denseBUStepSig ops nw prevMult w.pre mp with
              | .consumer =>
                (constOpen.erase k, if w.i < j then (w.i, j) :: out else out)
              | .excluded => (constOpen, out)
              | .blocker => (constOpen.erase k, out)
            | none => (constOpen, out)
          | none => (constOpen, out)
        else
          let (drops, out) := constOpen.toList.foldl (init := (([] : List (DenseAddrKey p)), out))
            fun da kw =>
              match denseBUStepSig ops nw prevMult kw.2.pre mp with
              | .consumer =>
                (kw.1 :: da.1, if kw.2.i < j then (kw.2.i, j) :: da.2 else da.2)
              | .excluded => da
              | .blocker => (kw.1 :: da.1, da.2)
          (drops.foldl (·.erase ·) constOpen, out)
      -- (2) symbolic-keyed windows are tested literally against every message.
      let (symOpen, out) :=
        if symOpen.isEmpty then (symOpen, out) else
        symOpen.foldr (init := (([] : List (DenseBUWin p)), out)) fun w sa =>
          match denseBUStepSig ops nw prevMult w.pre mp with
          | .consumer => (sa.1, if w.i < j then (w.i, j) :: sa.2 else sa.2)
          | .excluded => (w :: sa.1, sa.2)
          | .blocker => (sa.1, sa.2)
      -- (3) a send opens its window; a same-key window that survived (1) moves to `symOpen`.
      let (constOpen, symOpen) :=
        if decide (mp.mult = some setMult) then
          match mp.key with
          | some k =>
            let w : DenseBUWin p := ⟨mp, j⟩
            if k.allConst then
              match constOpen[k]? with
              | some old => (constOpen.insert k w, old :: symOpen)
              | none => (constOpen.insert k w, symOpen)
            else (constOpen, w :: symOpen)
          | none => (constOpen, symOpen)
        else (constOpen, symOpen)
      denseBUSweep ops nw setMult prevMult arr fuel (j + 1) constOpen symOpen out

/-- Scatter the sweep's pairs by send position, then read them back ascending — the pairs come
    out in consume order, and the equalities have to follow send order. -/
def denseBUScatter (n : Nat) (pairs : List (Nat × Nat)) : Array (Option Nat) :=
  pairs.foldl (fun a ij => a.setIfInBounds ij.1 (some ij.2)) (Array.replicate n none)

def denseBUCands (out : Array (Option Nat)) : (i : Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | i + 1, acc =>
    match out[i]? with
    | some (some j) => denseBUCands out i ((i, j) :: acc)
    | _ => denseBUCands out i acc

/-! ## The verifier

`denseCheckPair` on prepared records over an index range: no `mid` list is materialized, and every
arm is the exact certificate. -/

def denseBUMidOk (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (a b : DenseBUPre p) : Bool :=
  denseBUConstsNeq a b || denseBUAffineNeq a b || denseBUTwoRootNeq a b
    || denseBUNonzeroNeq nw a b || decide (b.mult = some ops.zero)

def denseBUMidScan (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (arr : Array (DenseBUPre p))
    (a : DenseBUPre p) (j : Nat) : (fuel : Nat) → (q : Nat) → Bool
  | 0, _ => true
  | fuel + 1, q =>
    if q ≥ j then true
    else
      match arr[q]? with
      | none => true
      | some b => if denseBUMidOk ops nw a b then denseBUMidScan ops nw arr a j fuel (q + 1)
                  else false

/-- The verifier checks the ordering itself, which is what lets the sweep stay entirely untrusted:
    nothing about the windows, the scatter or the candidate order carries a proof obligation. -/
def denseBUCheckPair (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (arr : Array (DenseBUPre p)) (i j : Nat) : Bool :=
  match arr[i]?, arr[j]? with
  | some a, some r =>
    decide (i < j) && decide (a.mult = some setMult) && decide (r.mult = some prevMult) &&
      denseBUConstsEq a r && denseBUMidScan ops nw arr a j (j - i) (i + 1)
  | _, _ => false

/-- For each verified candidate, the entailed slot equalities, in ascending send-position order. -/
def denseBUCollect (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (arr : Array (DenseBUPre p)) : List (Nat × Nat) → List (DenseExpr p)
  | [] => []
  | (i, j) :: rest =>
    let acc := denseBUCollect ops nw setMult prevMult shape bis arr rest
    if denseBUCheckPair ops nw setMult prevMult arr i j then
      match bis[i]?, bis[j]? with
      | some S, some R => denseMemEqConstraints shape S R ++ acc
      | _, _ => acc
    else acc

/-! ## Per-invocation scaffolding -/

/-- The memory-shaped buses in first-occurrence order of bus id, each paired with its shape and its
    interactions in source order. -/
def denseBUBusLists (memShape : Nat → Option MemoryBusShape)
    (bis : List (BusInteraction (DenseExpr p))) :
    List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))) :=
  ((bis.map (fun bi => bi.busId)).dedup).filterMap (fun busId =>
    (memShape busId).map (fun shape => (busId, shape, bis.filter (fun bi => bi.busId = busId))))

/-- The variables a two-root lookup can reach: those of an address-slot expression of an
    interaction on a memory-shaped bus, at that bus's own address fields. `densePtrReductions`
    keys on the queried form's own variables, so no other entry is ever read. -/
def denseBUAddrVars
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p)))) :
    Std.HashSet VarId :=
  busLists.foldl (fun acc sl =>
    sl.2.2.foldl (fun acc bi =>
      sl.2.1.addressFields.foldl (fun acc slot =>
        match bi.payload[slot]? with
        | some e => e.vars.foldl (fun a v => a.insert v) acc
        | none => acc) acc) acc) ∅

/-- The two-root entries of one constraint, restricted to the variables a lookup can reach. Only a
    variable with a nonzero coefficient in the first factor can produce an entry, so the candidate
    list is that factor's normalized terms rather than `c.vars.eraseDups`. -/
def denseBUAddTwoRoot (avars : Std.HashSet VarId) (T : DenseTwoRootMap p) (c : DenseExpr p) :
    DenseTwoRootMap p :=
  match c with
  | .mul f1 f2 =>
    match denseLinearize f1, denseLinearize f2 with
    | some l1, some l2 =>
      (l1.norm.terms.map (fun t => t.1)).foldl (fun T v =>
        if avars.contains v then
          match denseTwoRootOfLins l1 l2 v with
          | some (k, A, δ) => if k * k⁻¹ = 1 then T.insertEntry v k A δ else T
          | none => T
        else T) T
    | _, _ => T
  | _ => T

def denseBUTwoRootMap (avars : Std.HashSet VarId) (cs : List (DenseExpr p)) : DenseTwoRootMap p :=
  if Nat.Prime p then
    cs.foldl (fun T c => denseBUAddTwoRoot avars T c) DenseTwoRootMap.empty
  else DenseTwoRootMap.empty

/-- The entailed equalities of one bus: prepare, sweep, verify. -/
def denseBUForBus (ops : DenseZModOps p) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (shape : MemoryBusShape) (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  let setMult := denseSetNewMult ops shape
  let prevMult := denseGetPreviousMult ops shape
  let bis := bisL.toArray
  let arr := bis.map (denseBUPrep shape T)
  let pairs := denseBUSweep ops nw setMult prevMult arr arr.size 0 ∅ [] []
  let out := denseBUScatter arr.size pairs
  denseBUCollect ops nw setMult prevMult shape bis arr (denseBUCands out out.size [])

/-- The two-root table over the constraints that can be queried (`denseBUAddrVars`). -/
def denseBUTable (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : DenseTwoRootMap p :=
  let avars := denseBUAddrVars busLists
  denseBUTwoRootMap avars (d.algebraicConstraints.filter (fun c => c.mentionsAny avars))

/-- `DenseNonzeroWits.build` with the witness list scanned once instead of twice. -/
def denseBUWits (d : DenseConstraintSystem p) : DenseNonzeroWits p :=
  let ws := d.algebraicConstraints.flatMap denseReciprocalWits?
  ⟨ws, denseNZIndexOf ws⟩

/-- The equalities every bus contributes, before the zero / already-present filter. -/
def denseBUEqsOf (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  (busLists.map (fun sl => denseBUForBus denseZModOps T nw sl.2.1 sl.2.2)).flatten

def denseBUEqs (memShape : Nat → Option MemoryBusShape) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists memShape d.busInteractions
  if busLists.isEmpty then [] else denseBUEqsOf busLists d

/-- Drop the equalities that are identically zero or already present. The already-present test
    buckets by `DenseExpr.bHash`; only a constraint of an equality's own shape can be `==` to one,
    so the rest never enter the bucket. -/
def denseBUFilterNew (d : DenseConstraintSystem p) (eqs : List (DenseExpr p)) :
    List (DenseExpr p) :=
  let dHashes : Std.HashMap UInt64 (List (DenseExpr p)) :=
    d.algebraicConstraints.foldl (fun m c =>
      match c with
      | .add _ (.mul (.const _) _) => let h := c.bHash; m.insert h (c :: m.getD h [])
      | _ => m) ∅
  let containsC : DenseExpr p → Bool := fun c =>
    (dHashes.getD c.bHash []).any (fun c' => c' == c)
  eqs.filter (fun c => !c.normalize.fold.isConstZero && !containsC c)

/-- The constraints `denseBusUnifyF` appends: the entailed slot equalities of every verified
    consecutive send→receive pair, minus those that are identically zero or already present. -/
def denseBusUnifyNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let _ := bs
  let eqs := denseBUEqs facts.memShape d
  if eqs.isEmpty then [] else denseBUFilterNew d eqs

/-- For a memory bus, a `set` (send) at address `a` immediately followed by a matching `get`
    (receive) at the same address must carry the same payload, so this adds the entailed slot
    equalities `getᵢ = setᵢ` for every provably-matched consecutive send→receive pair on each
    declared memory / execution-bridge bus (skipping equations already present or zero).

    No-new-variable side condition holds by construction (`denseMemEqConstraints_vars`). -/
def denseBusUnifyF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := denseBusUnifyNewCs bs facts d
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
