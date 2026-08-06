import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Dedup
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses

set_option autoImplicit false

/-! # Dense timestamp-group bus unification (runtime transform for `busUnify`)

Adds the payload-copy equalities a memory bus's discipline entails, justified *order-free*: the
rely is `admissibleMemoryBusM` (per-address multiset counting) plus the TS_BOUND fact
(`facts.memTsField` — every active message's declared ts-slot value is `< B ≤ 2^29`), consumed
through `admissibleMemoryBusM_copies_of_ts` (`Implementation/MemoryBusMultiset.lean`). Nothing
about the interaction list's order is trusted.

The engine prepares every memory-bus interaction once (`denseBUPrep` — the address slots' constant
value, linear form and two-root reductions), buckets by canonical address key to *propose* groups
(untrusted), and verifies each proposal with `denseBUGroupPairs?`: fiber completeness (every
interaction classified member-send / member-receive / certified-outside), one shared send-ts base
with increasing offsets of spread `< B`, and a solved LessThan gadget per receive. Proofs in
`Proofs/BusUnify.lean`. -/

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

/-- A canonical address key (each slot constant-folded where possible); buckets the group
    proposals. -/
structure DenseAddrKey (p : ℕ) where
  exprs : List (DenseExpr p)
deriving DecidableEq

instance : Hashable (DenseAddrKey p) :=
  ⟨fun k => k.exprs.foldl (fun h e => mixHash h e.bHash) 7⟩

/-- Every slot folded to a constant, so the key identifies the evaluated address; the sweep
    (`BusSweep.lean`) meets such a message only against the window at its own key. -/
def DenseAddrKey.allConst (k : DenseAddrKey p) : Bool :=
  k.exprs.all fun e => match e with
    | .const _ => true
    | _ => false

/-! ## Prepared address records

One record per memory-bus interaction, built once per invocation. `cval` / `lin` / `reds` are the
data the certificates of `AddrDiseq.lean` re-derive per compared pair; `linSig` / `linKey` are the
canonical term signatures. Two linear forms differ by a nonzero constant exactly when their
normalized term lists agree and their constants do not (`denseKeyDiffNZ`), so the arms compare an
integer and a list. Both branches of one two-root reduction differ by a constant, hence share one
signature. -/

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
  let key := match lin with | some L => denseTermKey L | none => []
  { expr := e, eHash := e.bHash, cval := e.constValue?
    lin := lin
    linKey := key
    linSig := denseTermKeyHash key
    reds := (densePtrReductions T e).map denseRedKey }

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

/-- `denseKeyDiffNZ` on two prepared slots: the canonical keys agree and the constants do not. -/
@[inline] def denseBUAffineNeqSlot (sa sb : DenseBUSlot p) : Bool :=
  match sa.lin, sb.lin with
  | some L, some L' =>
    (sa.linSig == sb.linSig && decide (sa.linKey = sb.linKey)) && decide (L.const ≠ L'.const)
  | _, _ => false

/-- One key compare per reduction pair decides all four branch differences, which differ only in
    their constants. -/
@[inline] def denseBUTwoRootNeqSlot (sa sb : DenseBUSlot p) : Bool :=
  sa.reds.any (fun r => sb.reds.any (denseRedKeysNeq r))

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

/-! ## The timestamp-group engine

The pass certifies one *address group* at a time under the order-free rely: every interaction on
the bus is classified against a group leader as a member send, a member receive, or certifiably
outside the group (different address, or a constant multiplicity in neither fiber); any undecided
interaction aborts the group. The group's send timestamps must share one linear base with strictly
increasing constant offsets of spread `< B` (the declared TS_BOUND), and each receive's ts slot
must carry the solved LessThan gadget against its own send (`send_ts − recv_ts = c₀ + Σ coeffᵢ ·
limbᵢ` with `c₀ ≥ 1` and range-checked limbs). `admissibleMemoryBusM_copies_of_ts`
(`Implementation/MemoryBusMultiset.lean`) then forces every interior receive to copy the previous
send's payload. -/

/-- The classification of one interaction against a group leader. -/
inductive DenseBUVerdict where
  | send
  | recv
  | out

/-- Classify a prepared record against the group leader `a`: a member send (constant multiplicity
    `setMult`, certified same address), a member receive (`prevMult`, same address), or certified
    outside the group — provably different address (the `AddrDiseq.lean` arms) or a constant
    multiplicity in neither fiber. `none` (undecided) aborts the group. -/
def denseBUClassify (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (a m : DenseBUPre p) : Option DenseBUVerdict :=
  if decide (m.mult = some setMult) && denseBUConstsEq a m then some .send
  else if decide (m.mult = some prevMult) && denseBUConstsEq a m then some .recv
  else if denseBUConstsNeq a m || denseBUAffineNeq a m || denseBUTwoRootNeq a m
      || denseBUNonzeroNeq nw a m
      || (match m.mult with
          | some c => decide (c ≠ setMult) && decide (c ≠ prevMult)
          | none => false) then some .out
  else none

/-- Split a bus's interactions into the leader's member sends and receives (source order), if
    every interaction classifies. Each list entry carries its own prepared record. -/
def denseBUSplit (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p) (a : DenseBUPre p) :
    List (BusInteraction (DenseExpr p) × DenseBUPre p) →
    Option (List (BusInteraction (DenseExpr p)) × List (BusInteraction (DenseExpr p)))
  | [] => some ([], [])
  | (bi, pre) :: rest =>
    match denseBUClassify nw setMult prevMult a pre,
        denseBUSplit nw setMult prevMult a rest with
    | some .send, some (s, r) => some (bi :: s, r)
    | some .recv, some (s, r) => some (s, bi :: r)
    | some .out, some (s, r) => some (s, r)
    | _, _ => none

/-! ## Timestamp certificates -/

/-- The linearized ts-slot expression of an interaction. -/
def denseBUTsLin (tsField : Nat) (bi : BusInteraction (DenseExpr p)) : Option (DenseLinExpr p) :=
  match bi.payload[tsField]? with
  | some e => denseLinearize e
  | none => none

/-- The send offsets: every send's ts slot linearizes with canonical term key `key0` (the shared
    base), leaving its constant. -/
def denseBUOffs (tsField : Nat) (key0 : List (VarId × ZMod p)) :
    List (BusInteraction (DenseExpr p)) → Option (List (ZMod p))
  | [] => some []
  | S :: rest =>
    match denseBUTsLin tsField S, denseBUOffs tsField key0 rest with
    | some L, some offs =>
      if denseTermKey L = key0 then some (L.const :: offs) else none
    | _, _ => none

/-- Consecutive offsets step by a constant in `[1, B)`. Under TS_BOUND that orders the sends'
    timestamp *values* (`val_lt_of_step`) wherever the shared base sits — the base a pass finds is
    whichever instruction's clock survived substitution, so the offsets themselves are signed. -/
def denseBUStepsOk (B : Nat) : List (ZMod p) → Bool
  | [] => true
  | [_] => true
  | c :: c' :: rest =>
    decide (1 ≤ (c' - c).val) && decide ((c' - c).val < B) && denseBUStepsOk B (c' :: rest)

/-- The group sends share one ts base and step through it in increasing order. -/
def denseBUSendTsOk (tsField B : Nat) (sends : List (BusInteraction (DenseExpr p))) : Bool :=
  match sends.head? with
  | none => false
  | some S0 =>
    match denseBUTsLin tsField S0 with
    | none => false
    | some L0 =>
      match denseBUOffs tsField (denseTermKey L0) sends with
      | none => false
      | some offs => denseBUStepsOk B offs

/-- An active single-variable range check `[x, width]` on a `varRangeBus` witnessing
    `(denv x).val < 2 ^ width.val`; returns that bound. -/
def denseBUVarBound (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → VarId → Option Nat
  | [], _ => none
  | bi :: rest, v =>
    match bi.payload, denseMultConst bi with
    | [DenseExpr.var v', DenseExpr.const b], some c =>
      if facts.varRangeBus bi.busId && decide (v' = v) && decide (c ≠ 0) then
        some (2 ^ b.val)
      else denseBUVarBound bs facts rest v
    | _, _ => denseBUVarBound bs facts rest v

/-- Per-term range certificates for a gadget's limb terms: each variable's witnessed bound. -/
def denseBUTermCerts (bs : BusSemantics p) (facts : BusFacts p bs)
    (allBis : List (BusInteraction (DenseExpr p))) :
    List (VarId × ZMod p) → Option (List (VarId × ZMod p × Nat))
  | [] => some []
  | (v, coeff) :: rest =>
    match denseBUVarBound bs facts allBis v, denseBUTermCerts bs facts allBis rest with
    | some w, some cs => some ((v, coeff, w) :: cs)
    | _, _ => none

/-- The solved LessThan gadget between a receive's and its own send's ts slots:
    `send_ts − recv_ts` normalizes to `c₀ + Σ coeffᵢ · limbᵢ` with `c₀ ≥ 1`, every limb
    range-checked, and the no-wrap certificate `c₀ + B + Σ coeffᵢ·(boundᵢ − 1) ≤ p`
    (consumed via `val_lt_of_lessThan_gadget`). -/
def denseBUGadgetOk (bs : BusSemantics p) (facts : BusFacts p bs)
    (allBis : List (BusInteraction (DenseExpr p))) (tsField B : Nat)
    (S R : BusInteraction (DenseExpr p)) : Bool :=
  match denseBUTsLin tsField S, denseBUTsLin tsField R with
  | some LS, some LR =>
    let N := (LS.add (LR.scale (-1))).norm
    match denseBUTermCerts bs facts allBis N.terms with
    | some certs =>
      decide (1 ≤ N.const.val) &&
        decide (N.const.val + B + (certs.map (fun c => c.2.1.val * (c.2.2 - 1))).sum ≤ p)
    | none => false
  | _, _ => false

/-! ## The group verifier -/

/-- Verify one proposed group (leader at position `pos`): everything on the bus classifies, the
    fibers pair up (`#sends = #recvs ≥ 2`), the sends' ts structure holds, and each receive
    (source order) carries the gadget against its same-position send. Returns the member sends and
    receives. -/
def denseBUGroupPairs? (bs : BusSemantics p) (facts : BusFacts p bs) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (tsField B : Nat)
    (allBis : List (BusInteraction (DenseExpr p)))
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) (pos : Nat) :
    Option (List (BusInteraction (DenseExpr p)) × List (BusInteraction (DenseExpr p))) :=
  match zipped[pos]? with
  | none => none
  | some lp =>
    if decide (2 ^ 30 < p) && decide (B ≤ 2 ^ 29) then
      match denseBUSplit nw setMult prevMult lp.2 zipped with
      | some (sends, recvs) =>
        if decide (2 ≤ sends.length) && decide (sends.length = recvs.length)
            && denseBUSendTsOk tsField B sends
            && (sends.zip recvs).all (fun sr =>
                denseBUGadgetOk bs facts allBis tsField B sr.1 sr.2)
        then some (sends, recvs)
        else none
      | none => none
    else none

/-- The equalities of one verified group: interior receive `i` copies send `i − 1`
    (`admissibleMemoryBusM_copies_of_ts`), so pair the sends with the receives shifted by one. -/
def denseBUGroupEqs (shape : MemoryBusShape)
    (sends recvs : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  (sends.zip recvs.tail).flatMap (fun sr => denseMemEqConstraints shape sr.1 sr.2)

/-! ## Group proposals

Untrusted: buckets the bus by canonical address key and proposes each bucket with at least two
sends passing the cheap ts pre-check; only `denseBUGroupPairs?` carries proof obligations. -/

def denseBUProps (tsField B : Nat) (setMult : ZMod p)
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) : List Nat :=
  let step := fun (acc : Nat ×
        Std.HashMap (DenseAddrKey p) (Nat × List (BusInteraction (DenseExpr p))))
      (bp : BusInteraction (DenseExpr p) × DenseBUPre p) =>
    let (i, m) := acc
    (i + 1,
      match bp.2.key with
      | some k =>
        match m[k]? with
        | some (l, sends) =>
          m.insert k (l, if bp.2.mult = some setMult then bp.1 :: sends else sends)
        | none => m.insert k (i, if bp.2.mult = some setMult then [bp.1] else [])
      | none => m)
  let m := (zipped.foldl step (0, ∅)).2
  m.toList.filterMap (fun kv =>
    let sends := kv.2.2.reverse
    if 2 ≤ sends.length && denseBUSendTsOk tsField B sends then some kv.2.1 else none)

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

/-- The entailed equalities of one bus with a declared ts slot: prepare, propose, verify each
    group, emit the interior copy equalities. -/
def denseBUForBus (bs : BusSemantics p) (facts : BusFacts p bs) (ops : DenseZModOps p)
    (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) (shape : MemoryBusShape) (tsField B : Nat)
    (allBis : List (BusInteraction (DenseExpr p)))
    (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  let setMult := denseSetNewMult ops shape
  let prevMult := denseGetPreviousMult ops shape
  let zipped := bisL.map (fun bi => (bi, denseBUPrep shape T bi))
  (denseBUProps tsField B setMult zipped).flatMap (fun pos =>
    match denseBUGroupPairs? bs facts nw setMult prevMult tsField B allBis zipped pos with
    | some (sends, recvs) => denseBUGroupEqs shape sends recvs
    | none => [])

/-- The two-root table over the constraints that can be queried (`denseBUAddrVars`). -/
def denseBUTable (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : DenseTwoRootMap p :=
  let avars := denseBUAddrVars busLists
  denseBUTwoRootMap avars (d.algebraicConstraints.filter (fun c => c.mentionsAny avars))

/-- `DenseNonzeroWits.build` with the witness list scanned once instead of twice. -/
def denseBUWits (d : DenseConstraintSystem p) : DenseNonzeroWits p :=
  let ws := d.algebraicConstraints.flatMap denseReciprocalWits?
  ⟨ws, denseNZIndexOf ws⟩

/-- The equalities every bus contributes, before the zero / already-present filter. A bus without
    a declared ts slot (`facts.memTsField`) contributes nothing. -/
def denseBUEqsOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  (busLists.map (fun sl =>
    match facts.memTsField sl.1 with
    | some (tsField, B) =>
      denseBUForBus bs facts denseZModOps T nw sl.2.1 tsField B d.busInteractions sl.2.2
    | none => [])).flatten

def denseBUEqs (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists facts.memShape d.busInteractions
  if busLists.isEmpty then [] else denseBUEqsOf bs facts busLists d

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
    group's interior receives, minus those that are identically zero or already present. -/
def denseBusUnifyNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let eqs := denseBUEqs bs facts d
  if eqs.isEmpty then [] else denseBUFilterNew d eqs

/-- For a memory bus, each `getPrevious` (receive) reads back the payload the previous same-address
    `setNew` (send) committed, so this adds the entailed slot equalities `getᵢ = setᵢ` for every
    certified address group's interior receives against the timestamp-previous send, on each
    declared memory / execution-bridge bus with a declared timestamp slot (skipping equations
    already present or zero). Justified order-free via `admissibleMemoryBusM_copies_of_ts`. -/
def denseBusUnifyF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := denseBusUnifyNewCs bs facts d
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
