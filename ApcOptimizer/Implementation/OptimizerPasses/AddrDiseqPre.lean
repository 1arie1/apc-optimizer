import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Prepared address-disequality certificates

The disequality certificates (`AddrDiseq.lean`) re-derive the same per-interaction data — the
address slot's constant value, linear form, and two-root reductions — once per *compared pair*,
which made `busPairCancel`'s region scans quadratic in interaction count. `DenseAddrPre` prepares
that data once per interaction (each field a memoizing `Thunk`, so untouched certificate arms stay
unpaid); the `*P` tests below read the prepared records. Equalities to the original certificates
live in `Proofs/AddrDiseqPre.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Prepared per-address-slot data: the raw slot expression plus its lazily-computed constant
    value, linear form, canonical term key (with the key's hash) and keyed two-root reductions.
    The keys are what make the affine and two-root arms integer-and-list comparisons instead of a
    normalization per compared pair (`denseTermKey`, `AddrDiseq.lean`). -/
structure DenseSlotPre (p : ℕ) where
  expr : DenseExpr p
  cval : Thunk (Option (ZMod p))
  lin : Thunk (Option (DenseLinExpr p))
  key : Thunk (UInt64 × List (VarId × ZMod p))
  reds : Thunk (List (UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p))

def denseSlotPrep (T : DenseTwoRootMap p) (e : DenseExpr p) : DenseSlotPre p :=
  let lin : Thunk (Option (DenseLinExpr p)) := Thunk.mk fun _ => denseLinearize e
  ⟨e, Thunk.pure e.constValue?, lin,
   Thunk.mk fun _ =>
     match lin.get with
     | some L => let k := denseTermKey L; (denseTermKeyHash k, k)
     | none => (0, []),
   Thunk.mk fun _ => (densePtrReductions T e).map denseRedKey⟩

/-- Prepared per-interaction address data relative to one memory-bus shape: the bus id, the
    multiplicity constant, and the prepared slot record at each of the shape's address fields. -/
structure DenseAddrPre (p : ℕ) where
  busId : Nat
  mult : Thunk (Option (ZMod p))
  slots : List (Option (DenseSlotPre p))

def denseAddrPrep (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bi : BusInteraction (DenseExpr p)) : DenseAddrPre p :=
  ⟨bi.busId, Thunk.mk fun _ => denseMultConst bi,
   shape.addressFields.map (fun slot => (bi.payload[slot]?).map (denseSlotPrep T))⟩

/-- One prepared array for *every* memory bus at once: a position gets its own bus's shape, and a
    position on no memory bus gets a bus-id-only stub. Sound for every candidate bus because every
    test reads `busId` first and answers there (`denseMidRefutedP`/`densePreRefutedP` refute, and
    `denseProvRecvP` fails) whenever the compared position is off the candidate's bus — so a record
    prepared under another bus's shape, or not prepared at all, is never looked into. -/
def denseAddrPrepAll (memShape : Nat → Option MemoryBusShape) (T : DenseTwoRootMap p)
    (arr : Array (BusInteraction (DenseExpr p))) : Array (DenseAddrPre p) :=
  arr.map (fun bi =>
    match memShape bi.busId with
    | some shape => denseAddrPrep shape T bi
    | none => ⟨bi.busId, Thunk.pure none, []⟩)

/-! ## The prepared certificate tests

Slot-wise tests recurse over the two slot lists directly — a region scan runs them once per
compared pair, so a `zip` there would allocate on every test. A pair with a missing slot on
either side fails an `all` and skips an `any`, matching the originals' missing-slot arms. -/

@[specialize] def denseSlotsAny (f : DenseSlotPre p → DenseSlotPre p → Bool) :
    List (Option (DenseSlotPre p)) → List (Option (DenseSlotPre p)) → Bool
  | some sa :: as, some sb :: bs => f sa sb || denseSlotsAny f as bs
  | _ :: as, _ :: bs => denseSlotsAny f as bs
  | _, _ => false

@[specialize] def denseSlotsAll (f : DenseSlotPre p → DenseSlotPre p → Bool) :
    List (Option (DenseSlotPre p)) → List (Option (DenseSlotPre p)) → Bool
  | some sa :: as, some sb :: bs => f sa sb && denseSlotsAll f as bs
  | _ :: _, _ :: _ => false
  | _, _ => true

def denseAddrConstsNeqP (a b : DenseAddrPre p) : Bool :=
  denseSlotsAny (fun sa sb =>
    match sa.cval.get, sb.cval.get with
    | some c, some c' => decide (c ≠ c')
    | _, _ => false) a.slots b.slots

def denseAddrConstsEqP (a b : DenseAddrPre p) : Bool :=
  denseSlotsAll (fun sa sb =>
    decide (sa.expr = sb.expr) ||
    (match sa.cval.get, sb.cval.get with
     | some c, some c' => c = c'
     | _, _ => false)) a.slots b.slots

def denseAddrAffineNeqP (a b : DenseAddrPre p) : Bool :=
  denseSlotsAny (fun sa sb =>
    match sa.lin.get, sb.lin.get with
    | some L, some L' =>
      let ka := sa.key.get
      let kb := sb.key.get
      (ka.1 == kb.1 && decide (ka.2 = kb.2)) && decide (L.const ≠ L'.const)
    | _, _ => false) a.slots b.slots

def denseAddrTwoRootNeqP (a b : DenseAddrPre p) : Bool :=
  denseSlotsAny (fun sa sb =>
    sa.reds.get.any (fun r => sb.reds.get.any (denseRedKeysNeq r))) a.slots b.slots

/-- `denseDiffSumOver` over prepared slot pairs (same fold, linearizations read from the prep). -/
def denseDiffSumP : List (Option (DenseSlotPre p) × Option (DenseSlotPre p)) →
    Option (DenseLinExpr p)
  | [] => some ⟨0, []⟩
  | s :: fs =>
    match denseDiffSumP fs with
    | none => none
    | some acc =>
      match s with
      | (some sa, some sb) =>
        match sa.lin.get, sb.lin.get with
        | some lS, some lM => some ((lM.add (lS.scale (-1))).add acc)
        | _, _ => none
      | _ => none

def denseAddrNonzeroNeqP (nw : DenseNonzeroWits p) (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).sublists.any (fun sub =>
    match denseDiffSumP sub with
    | some D =>
      (nw.index.getD (denseLinHash D) [] ++ nw.index.getD (denseLinHash (D.scale (-1))) []).any
        (fun g => denseIsZeroLin (D.add (g.scale (-1))) || denseIsZeroLin (D.add g))
    | none => false)

/-! ## The region tests on prepared records (originals in `BusPairCancelCheck.lean`) -/

def denseMidRefutedP (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (a b : DenseAddrPre p) : Bool :=
  decide (b.busId ≠ busId) || decide (b.mult.get = some ops.zero) || denseAddrConstsNeqP a b
    || denseAddrAffineNeqP a b || denseAddrTwoRootNeqP a b || denseAddrNonzeroNeqP nw a b

def densePreRefutedP (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (setMult : ZMod p) (a b : DenseAddrPre p) : Bool :=
  denseMidRefutedP ops nw busId a b ||
    (match b.mult.get with
     | some c => decide (c ≠ setMult)
     | none => false)

def denseProvRecvP (busId : Nat) (getPrevMult : ZMod p) (a b : DenseAddrPre p) : Bool :=
  decide (b.busId = busId) && denseAddrConstsEqP a b && decide (b.mult.get = some getPrevMult)

end ApcOptimizer.Dense
