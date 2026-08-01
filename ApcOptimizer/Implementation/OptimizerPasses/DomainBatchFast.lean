import ApcOptimizer.Implementation.OptimizerPasses.DomainBatchRuntime

set_option autoImplicit false

/-! # `domainBatch`, engine rewrite (runtime only)

Same optimization as `DomainBatchRuntime.lean` — finite domains per variable, then a box enumeration
per candidate variable set, keeping every variable that takes the same value in every surviving
point — with the representation rebuilt for runtime:

* every per-variable structure is an `Array` keyed by `VarId.index` (domain table, anchor buckets);
* each item's distinct variable list is computed **once** and reused by the table build, the target
  list, the buckets and the gathers;
* the affine roots of a product constraint come from one linearization per factor, shared by the
  constraint's ≤ 3 variables;
* items compile **once per invocation** to programs over a `VarId.index`-keyed register file
  (`DbItem`/`DbTree`), so a scan neither compiles nor allocates a point: the box loop writes one
  register per step and the candidate mask is a value array plus an alive flag array with a live
  count, so the abort test is O(1);
* a `.coset` domain arm streams a byte operand's coset in the field with one hoisted inverse.

The forced set is the one `denseDomainBatchσV` computes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Domains

The scan works on `ZMod p` values in their `ZMod.val` representation — a plain `Nat` below `p` —
so a point costs machine arithmetic instead of a `p`-match plus a `Fin` reconstruction per
operation. `DbDom` therefore stores `Nat`s; `zmodOfNatP` maps back at the boundary. -/

/-- A finite domain: explicit values, `[0, bound)`, or the `bound`-element coset
    `{(v + negB) * aInv : v < bound}` (a byte operand's entailed domain, never materialized).
    Every value is a `ZMod.val`. -/
inductive DbDom where
  | explicit (vals : Array Nat)
  | range (bound : Nat)
  | coset (bound : Nat) (negB aInv : Nat)

@[inline] def DbDom.size : DbDom → Nat
  | .explicit vs => vs.size
  | .range b => b
  | .coset b _ _ => b

/-- `(n : ZMod p)`, dictionary-free (mirrors `zmodOneP`). -/
def zmodOfNatP : ∀ (p : ℕ), Nat → ZMod p
  | 0, n => ((n : ℤ) : ZMod 0)
  | m + 1, n => (⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ : Fin (m + 1))

/-- `a + b` on `val`s: both are below `p`, so the sum needs a conditional subtraction rather than
    the division `Fin.add` performs. -/
@[inline] def dbAddN (p a b : Nat) : Nat := let s := a + b; if s < p then s else s - p

@[inline] def dbMulN (p a b : Nat) : Nat := a * b % p

/-- The `i`-th element of a domain, in `toList` order. The index is a position in a domain of at
    most `maxEnumSize` elements, so the reduction is a comparison rather than a division. -/
@[inline] def DbDom.at (p : ℕ) (d : DbDom) (i : Nat) : Nat :=
  match d with
  | .explicit vs => vs.getD i 0
  | .range _ => if i < p then i else i % p
  | .coset _ negB aInv =>
    dbMulN p (dbAddN p (if i < p then i else i % p) negB) aInv

/-- Elements of a coset domain, with early exit; the other two arms need no iteration. -/
def dbCosetIterN {β : Type} (p : ℕ) (f : β → Nat → β) (stop : β → Bool) (negB aInv cur : Nat) :
    Nat → β → β
  | 0, acc => acc
  | n + 1, acc =>
    if stop acc then acc
    else dbCosetIterN p f stop negB aInv ((cur + 1 % p) % p) n (f acc (dbMulN p ((cur + negB) % p) aInv))

/-- The single value the domain admits, or `none` (`denseDomainConstantValueV?`). -/
def DbDom.const? (p : ℕ) (d : DbDom) : Option Nat :=
  match d with
  | .explicit vs =>
    match vs[0]? with
    | none => none
    | some v => if vs.all (fun w => w == v) then some v else none
  | .range b => if b == 1 then some 0 else none
  | .coset b negB aInv => if b == 1 then some (dbMulN p negB aInv) else none

/-- Every element is `< bound` as a `Nat` (`denseDomainBelowV`). -/
def DbDom.below (p : ℕ) (d : DbDom) (bound : Nat) : Bool :=
  match d with
  | .explicit vs => vs.all (fun v => decide (v < bound))
  | .range b => decide (b ≤ bound)
  | .coset b negB aInv =>
    dbCosetIterN p (fun acc v => acc && decide (v < bound)) (fun acc => !acc) negB aInv 0 b true

/-! ## Compiled items

`DbTree` leaves are `VarId.index`es into the scan's register file, so a compiled item is
target-independent: it is built once per invocation and shared by every target that gathers it. -/

inductive DbTree where
  | const (c : Nat)
  | reg (i : Nat)
  | add (a b : DbTree)
  | mul (a b : DbTree)

def dbEval (p : ℕ) (regs : Array Nat) : DbTree → Nat
  | .const c => c
  | .reg i => regs.getD i 0
  | .add a b => dbAddN p (dbEval p regs a) (dbEval p regs b)
  | .mul a b => dbMulN p (dbEval p regs a) (dbEval p regs b)

def dbCompile : DenseExpr p → DbTree
  | .const c => .const c.val
  | .var i => .reg i.index
  | .add a b => .add (dbCompile a) (dbCompile b)
  | .mul a b => .mul (dbCompile a) (dbCompile b)

/-- One gathered item's per-point obligation; the bus arms mirror `DenseCBiPred`. -/
inductive DbItem where
  | zero (e : DbTree)
  | always
  | varRange (mult x width : DbTree)
  | varRangeConst (mult x : DbTree) (bound : Nat)
  | tupleRange (mult x y : DbTree) (boundX boundY : Nat)
  | fixedRange (mult value : DbTree) (bound : Nat)
  | byte (mult o1 o2 result : DbTree) (bound : Nat) (kind : DenseBytePredKind)
  | fallback (busId : Nat) (mult : DbTree) (payload : List DbTree)

def dbByteRel (kind : DenseBytePredKind) (a b r : Nat) : Bool :=
  match kind with
  | .xor => decide (r = Nat.xor a b)
  | .pair => r == 0
  | .or => decide (r = Nat.lor a b)
  | .and => decide (r = Nat.land a b)

def dbItemOk {bs : BusSemantics p} (facts : BusFacts p bs) (regs : Array Nat) :
    DbItem → Bool
  | .zero e => dbEval p regs e == 0
  | .always => true
  | .varRange mult x width =>
    if dbEval p regs mult == 0 then true
    else
      let w := dbEval p regs width
      decide (w ≤ 17) && decide (dbEval p regs x < 2 ^ w)
  | .varRangeConst mult x bound =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs x < bound)
  | .tupleRange mult x y boundX boundY =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs x < boundX) && decide (dbEval p regs y < boundY)
  | .fixedRange mult value bound =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs value < bound)
  | .byte mult o1 o2 result bound kind =>
    if dbEval p regs mult == 0 then true
    else
      let a := dbEval p regs o1
      let b := dbEval p regs o2
      decide (a < bound) && decide (b < bound) && dbByteRel kind a b (dbEval p regs result)
  | .fallback busId mult payload =>
    let m := dbEval p regs mult
    if m == 0 then true
    else
      facts.acceptsDec
        { busId := busId, multiplicity := zmodOfNatP p m,
          payload := payload.map (fun t => zmodOfNatP p (dbEval p regs t)) }

def dbAllOk {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbItem)
    (regs : Array Nat) (i : Nat) : Bool :=
  if h : i < items.size then
    (if dbItemOk facts regs items[i] then dbAllOk facts items regs (i + 1) else false)
  else true
  termination_by items.size - i
  decreasing_by all_goals omega

/-! ### Per-interaction data, computed once

Every `BusFacts` query about an interaction is resolved here, once, and read by the three consumers
that used to each ask again: the byte-domain phase, the item compiler and the domain-redundancy
test. `spec.decode` in particular allocates and was run three times per interaction. -/

/-- An interaction's byte-bus view: the spec, the op selector's constant value, and the decoded
    logical operands. -/
structure DbBytePre (p : ℕ) where
  spec : ByteXorSpec p
  op? : Option (ZMod p)
  o1 : DenseExpr p
  o2 : DenseExpr p
  result : DenseExpr p

/-- The constant multiplicity, the constant-slot pattern, the distinct variables, the stateless
    flag and the resolved bus facts of one interaction. Built once and never rewritten:
    `denseBiInformative`'s verdict rides alongside in its own array, so the slot-bound phase
    does not rebuild this record per interaction. -/
structure DbBiPre (p : ℕ) where
  mult? : Option (ZMod p)
  pat : List (Option (ZMod p))
  vars : Array VarId
  usable : Bool
  byte? : Option (DbBytePre p)
  varRange : Bool
  tuple? : Option (Nat × Nat)
  rangeAt? : Option (Nat × Nat)

def dbBiPreEmpty : DbBiPre p := ⟨none, [], #[], false, none, false, none, none⟩

/-- Resolve every `BusFacts` query about one interaction. Faithfulness of the cache is
    `DbBiPreOf` (`Proofs/DomainBatchFast.lean`). -/
def dbPreOne {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (vars : Array VarId) : DbBiPre p :=
  let pat := bi.payload.map DenseExpr.constValue?
  let usable := !bs.isStateful bi.busId
  -- the width/tuple facts are consulted only on a two-slot payload, and the range fact only when
  -- neither of them answered: each is resolved exactly where its consumers can reach it
  let twoSlot := match bi.payload with | [_, _] => true | _ => false
  let varRange := usable && twoSlot && facts.varRangeBus bi.busId
  let tuple? := if usable && twoSlot && !varRange then facts.tupleRangeBus bi.busId else none
  { mult? := bi.multiplicity.constValue?
    pat
    vars
    usable
    -- read by the compiler and the pair-redundancy test (both `usable`-only) and by the
    -- byte-domain phase (nonzero constant multiplicity only)
    byte? :=
      if usable || (bi.multiplicity.constValue?).any (fun m => !zmodIsZero m) then
        (facts.byteXorSpec bi.busId).bind fun spec =>
          (spec.decode bi.payload).map fun t => ⟨spec, t.1.constValue?, t.2.1, t.2.2.1, t.2.2.2⟩
      else none
    varRange
    tuple?
    rangeAt? :=
      if usable && !varRange && tuple?.isNone then facts.rangeCheckAt bi.busId pat else none }

/-! ### Compiling a bus interaction (mirrors `denseCompileCBiPredV`) -/

def dbCompileRange (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (mult : DbTree) :
    Option (DbItem) :=
  match e.mult? with
  | some m =>
    if zmodIsOne m then
      match e.rangeAt? with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some value => some (.fixedRange mult (dbCompile value) bound)
        | none => none
      | none => none
    else none
  | none => none

def dbCompileByte (e : DbBiPre p) (mult : DbTree) : Option (DbItem) :=
  match e.byte? with
  | none => none
  | some b =>
    match b.op? with
    | none => none
    | some opValue =>
      let spec := b.spec
      let mk : DenseBytePredKind → Option (DbItem) := fun kind =>
        some (.byte mult (dbCompile b.o1) (dbCompile b.o2) (dbCompile b.result) spec.bound kind)
      if opValue = spec.xorOp then mk .xor
      else if opValue = spec.pairOp then mk .pair
      else
        match spec.orOp with
        | some orOp =>
          if opValue = orOp then mk .or
          else
            match spec.andOp with
            | some andOp => if opValue = andOp then mk .and else none
            | none => none
        | none =>
          match spec.andOp with
          | some andOp => if opValue = andOp then mk .and else none
          | none => none

def dbCompileOther (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (mult : DbTree) :
    DbItem :=
  match dbCompileRange bi e mult with
  | some item => item
  | none =>
    match dbCompileByte e mult with
    | some item => item
    | none => .fallback bi.busId mult (bi.payload.map dbCompile)

def dbCompileBi {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : DbItem :=
  if denseBiAlwaysOk facts bi then .always
  else
    let mult := dbCompile bi.multiplicity
    match bi.payload with
    | [x, width] =>
      if e.varRange then
        match width.constValue? with
        | some widthValue =>
          if widthValue.val ≤ 17 then .varRangeConst mult (dbCompile x) (2 ^ widthValue.val)
          else .varRange mult (dbCompile x) (dbCompile width)
        | none => .varRange mult (dbCompile x) (dbCompile width)
      else
        match e.tuple? with
        | some (boundX, boundY) =>
          .tupleRange mult (dbCompile x) (dbCompile width) boundX boundY
        | none => dbCompileOther bi e mult
    | _ => dbCompileOther bi e mult

/-! ## Distinct variables per item, computed once -/

def dbPushVar (acc : Array VarId) (i : VarId) : Array VarId :=
  if acc.contains i then acc else acc.push i

def dbVarsOf : DenseExpr p → Array VarId → Array VarId
  | .const _, acc => acc
  | .var i, acc => dbPushVar acc i
  | .add a b, acc => dbVarsOf b (dbVarsOf a acc)
  | .mul a b, acc => dbVarsOf b (dbVarsOf a acc)

def dbVarsOfList : List (DenseExpr p) → Array VarId → Array VarId
  | [], acc => acc
  | e :: rest, acc => dbVarsOfList rest (dbVarsOf e acc)

def dbBiVars (bi : BusInteraction (DenseExpr p)) : Array VarId :=
  dbVarsOfList bi.payload (dbVarsOf bi.multiplicity #[])

/-! ## Affine roots: one linearization per factor

`denseRootsIn i c` linearizes the whole tree once per queried variable. The plan below linearizes
each factor of the product spine once; answering a variable is then a walk over normalized forms. -/

inductive DbRootPlan (p : ℕ) where
  | leaf (lin : Option (DenseLinExpr p))
  | prod (lin : Option (DenseLinExpr p)) (a b : DbRootPlan p)

def dbRootPlan : DenseExpr p → DbRootPlan p
  | .mul a b =>
    .prod ((denseLinearize (.mul a b)).map DenseLinExpr.norm) (dbRootPlan a) (dbRootPlan b)
  | e => .leaf ((denseLinearize e).map DenseLinExpr.norm)

/-- `denseRootsOfTerms` on an already-normalized form. Every operation is a `zmod…P` primitive:
    mentioning `0`, `+` or `*` here rebuilds `ZMod.commRing p` at the function's entry, ahead of the
    terms match, on all ~1.5 M calls of a sha256 run. -/
def dbRootsOfLin (i : VarId) (l : DenseLinExpr p) : Option (List (ZMod p)) :=
  match l.terms with
  | [] => if zmodIsZero l.const then none else some []
  | [(j, a)] =>
    if j = i then
      if zmodIsZero a then none
      -- a normalized `x - c`: the root is `c`, with no modular inverse to compute
      else if zmodIsOne a then some [zmodNegP l.const]
      else
        let r := zmodNegP (zmodMulP a⁻¹ l.const)
        if zmodIsZero (zmodAddP (zmodMulP a r) l.const) then some [r] else none
    else none
  | _ :: _ :: _ => none

def dbRootsIn (i : VarId) : DbRootPlan p → Option (List (ZMod p))
  | .leaf lin => lin.bind (dbRootsOfLin i)
  | .prod lin a b =>
    match lin.bind (dbRootsOfLin i) with
    | some r => some r
    | none =>
      match dbRootsIn i a, dbRootsIn i b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none

/-! ## The domain table -/

structure DbTab (p : ℕ) where
  dom : Array (Option (DbDom))

/-- Keep the strictly smaller domain, as `DenseDomainTable.insertEntry`. -/
def DbTab.insert (T : DbTab p) (i : Nat) (d : DbDom) : DbTab p :=
  let ⟨dom⟩ := T
  match dom.getD i none with
  | some d0 => if d.size < d0.size then ⟨dom.set! i (some d)⟩ else ⟨dom⟩
  | none => ⟨dom.set! i (some d)⟩

@[inline] def DbTab.get (T : DbTab p) (i : Nat) : Option (DbDom) := T.dom.getD i none

def dbAddConstraintVars (plan : DbRootPlan p) (vs : Array VarId) (k : Nat) (T : DbTab p) :
    DbTab p :=
  if h : k < vs.size then
    let i := vs[k]
    match dbRootsIn i plan with
    | some rs => dbAddConstraintVars plan vs (k + 1) (T.insert i.index (.explicit (rs.map ZMod.val).toArray))
    | none => dbAddConstraintVars plan vs (k + 1) T
  else T
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbSlotBound {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (mult? : Option (ZMod p)) (pat : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match mult? with
  | none => none
  | some m => if zmodIsZero m then none else facts.slotBound bi.busId m pat slot

/-- Walk the payload once: the raw-variable slots' bounds (first slot per variable, as
    `denseVarSlot`) feed both the table and `denseBiInformative`'s second disjunct. -/
def dbBusSlots {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (mult? : Option (ZMod p)) (pat : List (Option (ZMod p))) :
    List (DenseExpr p) → Nat → Array VarId → Bool → DbTab p → Bool × DbTab p
  | [], _, _, inf, T => (inf, T)
  | e :: rest, slot, seen, inf, T =>
    match e with
    | .var i =>
      if seen.contains i then dbBusSlots facts bi mult? pat rest (slot + 1) seen inf T
      else
        match dbSlotBound facts bi mult? pat slot with
        | none => dbBusSlots facts bi mult? pat rest (slot + 1) (seen.push i) true T
        | some bound =>
          let T := if bound ≤ maxDomainBound then T.insert i.index (.range bound) else T
          dbBusSlots facts bi mult? pat rest (slot + 1) (seen.push i) inf T
    | _ =>
      dbBusSlots facts bi mult? pat rest (slot + 1) seen (inf || !(e.constValue?).isSome) T

/-! ### Byte-operand domains (`denseAddByteVarDoms`), coset streamed -/

def dbByteOperand (e : DenseExpr p) (bound : Nat) : Option (Nat × DbDom) :=
  match e with
  | .var i => some (i.index, .range bound)
  | _ => (denseAffineOfExpr e).map (fun t => (t.1.index, .coset bound (zmodNegP t.2.2).val (t.2.1⁻¹).val))

def dbByteOperandVar (e : DenseExpr p) : Option Nat :=
  match e with
  | .var i => some i.index
  | _ => (denseAffineOfExpr e).map (fun t => t.1.index)

def dbAddByteOperand (e : DenseExpr p) (bound : Nat) (T : DbTab p) : DbTab p :=
  match dbByteOperandVar e with
  | none => T
  | some i =>
    match T.get i with
    | none => T
    | some d0 =>
      if bound < d0.size then
        match dbByteOperand e bound with
        | some (i', d) => T.insert i' d
        | none => T
      else T

def dbAddByteBi (e : DbBiPre p) (T : DbTab p) : DbTab p :=
  match e.mult? with
  | none => T
  | some m =>
    if zmodIsZero m then T
    else
      match e.byte? with
      | none => T
      | some b =>
        match b.op? with
        | none => T
        | some opv =>
          if denseByteOpBounds b.spec opv then
            dbAddByteOperand b.o2 b.spec.bound (dbAddByteOperand b.o1 b.spec.bound T)
          else T

/-! ## Box helpers -/

def dbBoxOf (T : DbTab p) (vs : Array VarId) (k : Nat) (acc : Nat) : Option Nat :=
  if h : k < vs.size then
    match T.get vs[k].index with
    | none => none
    | some d => dbBoxOf T vs (k + 1) (acc * d.size)
  else some acc
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbDomsOf (T : DbTab p) (vs : Array VarId) : Option (Array (DbDom)) :=
  vs.foldl (init := some #[]) fun acc v =>
    match acc with
    | none => none
    | some ds =>
      match T.get v.index with
      | none => none
      | some d => some (ds.push d)

/-- Enumerate a box, testing one item at every point; `false` at the first failure. Explicit-arg
    loops: no per-point allocation. -/
def dbBoxAllOne {bs : BusSemantics p} (facts : BusFacts p bs) (item : DbItem)
    (keys : Array Nat) (doms : Array (DbDom)) (d i n : Nat) (regs : Array Nat)
    (ok : Bool) : Array Nat × Bool :=
  if i ≥ n then ⟨regs, ok⟩
  else if !ok then ⟨regs, ok⟩
  else
    let regs := regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (.range 0)) i)
    if d + 1 ≥ keys.size then
      if dbItemOk facts regs item then dbBoxAllOne facts item keys doms d (i + 1) n regs true
      else ⟨regs, false⟩
    else
      let ⟨regs, ok⟩ := dbBoxAllOne facts item keys doms (d + 1) 0
        (doms.getD (d + 1) (.range 0)).size regs true
      if ok then dbBoxAllOne facts item keys doms d (i + 1) n regs true else ⟨regs, false⟩
  termination_by (keys.size - d, n - i)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

/-- The box point where key `d` takes element `min i (size_d - 1)`. -/
def dbDiagPoint (p : ℕ) (keys : Array Nat) (doms : Array (DbDom)) (i : Nat) (regs : Array Nat) :
    Array Nat :=
  (Array.range keys.size).foldl (init := regs) fun regs d =>
    let dom := doms.getD d (.range 0)
    regs.set! (keys.getD d 0) (DbDom.at p dom (min i (dom.size - 1)))

/-- Refute redundancy on the box diagonal before sweeping it. The sweep varies the last key fastest,
    so a constraint that only fails once an *outer* key moves costs a whole inner domain to refute;
    97 % of the non-redundant checks on sha256/keccak fail within the first eight diagonal points
    (measured). Verdict-identical: these are box points, so a failure here is a failure there. -/
def dbDiagRefute {bs : BusSemantics p} (facts : BusFacts p bs) (item : DbItem)
    (keys : Array Nat) (doms : Array (DbDom)) (i imax : Nat) (regs : Array Nat) :
    Array Nat × Bool :=
  if i ≥ imax then ⟨regs, false⟩
  else
    let regs := dbDiagPoint p keys doms i regs
    if dbItemOk facts regs item then dbDiagRefute facts item keys doms (i + 1) imax regs
    else ⟨regs, true⟩
  termination_by imax - i
  decreasing_by omega

/-- Boxes at most this size are swept directly; the diagonal pre-test would cost more than it
    saves. -/
def dbDiagGate : Nat := 16

/-- `denseConstraintRedundantV`: identically zero on the box of its own variables' domains. -/
def dbConstraintRedundant {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (item : DbItem) (vs : Array VarId) (regs : Array Nat) : Array Nat × Bool :=
  match dbBoxOf T vs 0 1 with
  | none => ⟨regs, false⟩
  | some box =>
    if box ≤ maxEnumSize then
      match dbDomsOf T vs with
      | none => ⟨regs, false⟩
      | some doms =>
        if vs.isEmpty then ⟨regs, dbItemOk facts regs item⟩
        else
          let keys := vs.map (fun v => v.index)
          let ⟨regs, refuted⟩ :=
            if dbDiagGate < box then dbDiagRefute facts item keys doms 0 8 regs
            else ⟨regs, false⟩
          if refuted then ⟨regs, false⟩
          else
            dbBoxAllOne facts item keys doms 0 0 (doms.getD 0 (.range 0)).size regs true
    else ⟨regs, false⟩

/-! ## Domain-redundancy of an interaction -/

def dbExprBelow (T : DbTab p) (e : DenseExpr p) (bound : Nat) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    match e with
    | .var i => match T.get i.index with | some d => DbDom.below p d bound | none => false
    | _ => false

def dbRangeCheckRedundant (T : DbTab p) (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) :
    Bool :=
  match e.mult? with
  | some mult =>
    if zmodIsZero mult then true
    else if zmodIsOne mult then
      match e.rangeAt? with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some x => dbExprBelow T x bound
        | none => false
      | none => false
    else false
  | none => false

def dbBytePairRedundant (T : DbTab p) (e : DbBiPre p) : Bool :=
  match e.byte? with
  | none => false
  | some b =>
    match b.op?, b.result.constValue? with
    | some opValue, some resultValue =>
      opValue = b.spec.pairOp && zmodIsZero resultValue &&
        dbExprBelow T b.o1 b.spec.bound && dbExprBelow T b.o2 b.spec.bound
    | _, _ => false

/-- `denseConstBiV?` from the pattern computed once. -/
def dbConstBi? (bi : BusInteraction (DenseExpr p)) (mult? : Option (ZMod p))
    (pat : List (Option (ZMod p))) : Option (BusInteraction (ZMod p)) :=
  match mult? with
  | none => none
  | some m =>
    match pat.foldr (fun s acc => match s, acc with
      | some v, some vs => some (v :: vs)
      | _, _ => none) (some []) with
    | none => none
    | some payload => some { busId := bi.busId, multiplicity := m, payload }

/-- `denseBiDomainRedundantV`. -/
def dbBiDomainRedundant {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : Bool :=
  match dbConstBi? bi e.mult? e.pat with
  | some value => zmodIsZero value.multiplicity || facts.acceptsDec value
  | none =>
    if facts.neverViolates bi.busId then true
    else
      match bi.payload with
      | [x, b] =>
        if e.varRange then
          match b.constValue? with
          | some width => if width.val ≤ 17 then dbExprBelow T x (2 ^ width.val) else false
          | none => false
        else
          match e.tuple? with
          | some (boundX, boundB) => dbExprBelow T x boundX && dbExprBelow T b boundB
          | none => dbRangeCheckRedundant T bi e || dbBytePairRedundant T e
      | _ => dbRangeCheckRedundant T bi e || dbBytePairRedundant T e

/-! ## The box scan

The register file is `VarId.index`-keyed and owned by the scan; the candidate mask is a value array
plus an alive flag array with a live count, so the abort test is O(1) per point. -/

structure DbScanSt where
  regs : Array Nat
  vals : Array Nat
  alive : Array Bool
  live : Nat
  started : Bool
deriving Inhabited

def dbAbsorbGo (regs : Array Nat) (keys : Array Nat) (i : Nat)
    (vals : Array Nat) (alive : Array Bool) (live : Nat) :
    Array Nat × Array Bool × Nat :=
  if h : i < keys.size then
    if alive.getD i false then
      if regs.getD (keys[i]) 0 == vals.getD i 0 then dbAbsorbGo regs keys (i + 1) vals alive live
      else dbAbsorbGo regs keys (i + 1) vals (alive.set! i false) (live - 1)
    else dbAbsorbGo regs keys (i + 1) vals alive live
  else (vals, alive, live)
  termination_by keys.size - i
  decreasing_by all_goals omega

/-- Intersect the mask with a surviving point; called only for survivors. -/
def dbAbsorbArgs (keys : Array Nat) (regs : Array Nat) (vals : Array Nat)
    (alive : Array Bool) (live : Nat) (started : Bool) :
    Array Nat × Array Bool × Nat × Bool :=
  if !started then
    ⟨keys.map (fun k => regs.getD k 0), Array.replicate keys.size true, keys.size, true⟩
  else
    let (vals, alive, live) := dbAbsorbGo regs keys 0 vals alive live
    ⟨vals, alive, live, started⟩

/-- The box loop. State is passed as explicit arguments, so nothing is allocated per point: the
    innermost dimension is walked in place (`regs.set!` on a uniquely-owned register file) and only a
    surviving point touches the mask. -/
def dbScanLoop {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem))
    (keys : Array Nat) (doms : Array (DbDom)) (d i n : Nat)
    (regs : Array Nat) (vals : Array Nat) (alive : Array Bool) (live : Nat)
    (started : Bool) : DbScanSt :=
  if i ≥ n then ⟨regs, vals, alive, live, started⟩
  else if started && live == 0 then ⟨regs, vals, alive, live, started⟩
  else
    let regs := regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (.range 0)) i)
    if d + 1 ≥ keys.size then
      -- innermost: test the point in place
      if dbAllOk facts items regs 0 then
        let ⟨vals, alive, live, started⟩ := dbAbsorbArgs keys regs vals alive live started
        dbScanLoop facts items keys doms d (i + 1) n regs vals alive live started
      else dbScanLoop facts items keys doms d (i + 1) n regs vals alive live started
    else
      let ⟨regs, vals, alive, live, started⟩ :=
        dbScanLoop facts items keys doms (d + 1) 0 (doms.getD (d + 1) (.range 0)).size
          regs vals alive live started
      dbScanLoop facts items keys doms d (i + 1) n regs vals alive live started
  termination_by (keys.size - d, n - i)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

/-- Scan a job's box, starting from an empty mask. -/
def dbScanBox {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem))
    (keys : Array Nat) (doms : Array (DbDom)) (regs : Array Nat) : DbScanSt :=
  if keys.isEmpty then
    -- the variable-free box has exactly one (empty) point
    if dbAllOk facts items regs 0 then ⟨regs, #[], #[], 0, true⟩ else ⟨regs, #[], #[], 0, false⟩
  else dbScanLoop facts items keys doms 0 0 (doms.getD 0 (.range 0)).size regs #[] #[] 0 false

/-! ## Plans -/

/-- A preflighted target: an immediate answer, or a scan job carrying its compiled items. -/
inductive DbPlan (p : ℕ) where
  | done (forced : List (VarId × ZMod p))
  | scan (keys : Array VarId) (doms : Array (DbDom)) (items : Array (DbItem))
      (constOk : Bool)

def dbForcedOfMask (p : ℕ) (keys : Array VarId) (vals : Array Nat) (alive : Array Bool) (i : Nat) :
    List (VarId × ZMod p) :=
  if h : i < keys.size then
    let rest := dbForcedOfMask p keys vals alive (i + 1)
    if alive.getD i false then (keys[i], zmodOfNatP p (vals.getD i 0)) :: rest else rest
  else []
  termination_by keys.size - i
  decreasing_by all_goals omega

def dbZeroAll (keys : Array VarId) : List (VarId × ZMod p) :=
  keys.toList.map (fun x => (x, zmodZeroP p))

/-- Run one plan, threading the register file so it is allocated once for the whole run. -/
def dbRunPlan {bs : BusSemantics p} (facts : BusFacts p bs) (nv : Nat)
    (st : Array Nat × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    Array Nat × List (List (VarId × ZMod p)) :=
  match plan with
  | .done forced => ⟨st.1, forced :: st.2⟩
  | .scan keys doms items constOk =>
    let ⟨regs0, out⟩ := st
    let regs0 := if regs0.size == nv then regs0 else Array.replicate nv 0
    if !constOk then ⟨regs0, dbZeroAll keys :: out⟩
    else
      let res := dbScanBox facts items (keys.map (fun v => v.index)) doms regs0
      let ⟨regs, vals, alive, live, started⟩ := res
      if !started then ⟨regs, dbZeroAll keys :: out⟩
      else if live == 0 then ⟨regs, [] :: out⟩
      else ⟨regs, dbForcedOfMask p keys vals alive 0 :: out⟩

def dbRunPlans {bs : BusSemantics p} (facts : BusFacts p bs) (nv : Nat) (plans : List (DbPlan p)) :
    List (List (VarId × ZMod p)) :=
  (plans.foldl (dbRunPlan facts nv)
    (⟨#[], []⟩ : Array Nat × List (List (VarId × ZMod p)))).2.reverse

/-! ## Target dedup: content hash plus an exact compare on the ascending index key -/

def dbKeyHash (vs : Array VarId) : UInt64 :=
  vs.foldl (init := 0x9e3779b97f4a7c15) fun h v =>
    (h ^^^ (UInt64.ofNat v.index)) * 0x100000001b3

def dbInsSorted (x : Nat) (out : Array Nat) (i : Nat) : Array Nat :=
  if h : i < out.size then
    if x < out[i] then out.insertIdx i x
    else if x == out[i] then out
    else dbInsSorted x out (i + 1)
  else out.push x
  termination_by out.size - i
  decreasing_by all_goals omega

/-- Seen target keys, bucketed by content hash with an exact compare (a false hit would lose a
    forced constant, so the compare is not optional). -/
structure DbSeen where
  buckets : Std.HashMap UInt64 (List (Array Nat))

/-- Destructure before reading the bucket: leaving `s.buckets` referenced by the record while
    inserting copies the whole table per insert. -/
def DbSeen.insertNew (s : DbSeen) (h : UInt64) (k : Array Nat) : Bool × DbSeen :=
  let ⟨buckets⟩ := s
  let cur := buckets.getD h []
  if cur.any (fun k' => k' == k) then (false, ⟨buckets⟩)
  else (true, ⟨buckets.insert h (k :: cur)⟩)

/-- The dedup key: ascending distinct `VarId.index`es (targets carry a handful of variables). -/
def dbSortedKey (vs : Array VarId) : Array Nat :=
  vs.foldl (init := #[]) fun acc v => dbInsSorted v.index acc 0

/-! ## The per-invocation context

Everything the target loop reads, built by four passes over the system: variable lists, the domain
table (constraint roots, then bus slot bounds, then byte operands), the per-item flags, and the
anchor buckets. -/

structure DbCtx (p : ℕ) where
  nv : Nat
  T : DbTab p
  csVars : Array (Array VarId)
  csItems : Array (DbItem)
  csActive : Array Bool
  csBucket : Array (Array Nat)
  /-- Variable-free constraints' target-independent contribution: their count (active or not) and
      the active ones' items (`denseConstraintCovIndexV`). -/
  csVarlessCount : Nat
  csVarlessItems : Array (DbItem)
  biVars : Array (Array VarId)
  biItems : Array (DbItem)
  biUsable : Array Bool
  biInformative : Array Bool
  biDomRed : Array Bool
  biBucket : Array (Array Nat)
  /-- The variable-free usable interactions' summary (`DenseBusVarlessSummary`). -/
  biVarlessCount : Nat
  biVarlessInformative : Bool
  biVarlessDomRed : Bool
  constOk : Bool

def dbNvOf (vs : Array (Array VarId)) (m : Nat) : Nat :=
  vs.foldl (init := m) fun acc a => a.foldl (fun b v => max b (v.index + 1)) acc

/-- Phase 1: constraint-sourced domains, one root plan per constraint (≤ 3 distinct variables). -/
def dbConstraintPhase (cs : Array (DenseExpr p)) (csVars : Array (Array VarId)) (k : Nat)
    (T : DbTab p) : DbTab p :=
  if h : k < cs.size then
    let vs := csVars.getD k #[]
    let T := if vs.size ≤ 3 then dbAddConstraintVars (dbRootPlan cs[k]) vs 0 T else T
    dbConstraintPhase cs csVars (k + 1) T
  else T
  termination_by cs.size - k
  decreasing_by all_goals omega

/-- Phase 2: bus slot bounds and `informative`, one payload walk per interaction. -/
def dbBusPhase {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : Array (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p)) (k : Nat)
    (st : DbTab p × Array Bool) : DbTab p × Array Bool :=
  if h : k < bis.size then
    let ⟨T, inf⟩ := st
    let e := pre.getD k dbBiPreEmpty
    let (i, T) := dbBusSlots facts bis[k] e.mult? e.pat bis[k].payload 0 #[] false T
    dbBusPhase facts bis pre (k + 1) ⟨T, inf.push i⟩
  else st
  termination_by bis.size - k
  decreasing_by all_goals omega

/-- Phase 3: byte-operand domains (reads the table phase 2 produced). -/
def dbBytePhase (pre : Array (DbBiPre p)) (k : Nat) (T : DbTab p) : DbTab p :=
  if h : k < pre.size then
    dbBytePhase pre (k + 1) (dbAddByteBi pre[k] T)
  else T
  termination_by pre.size - k
  decreasing_by all_goals omega

/-- The per-constraint scan programs. An item with a variable outside the table can never be
    gathered (a target's keys are all domained), so it needs neither a program nor a redundancy
    verdict. -/
def dbCsItemsOf (T : DbTab p) (cs : Array (DenseExpr p)) (csVars : Array (Array VarId)) :
    Array (DbItem) :=
  let gatherable := csVars.map (fun vs => (dbBoxOf T vs 0 1).isSome)
  (cs.zipIdx).map fun cj =>
    if gatherable.getD cj.2 false then DbItem.zero (dbCompile cj.1) else DbItem.always

/-- The per-interaction scan programs (see `dbCsItemsOf` for the gate). -/
def dbBiItemsOf {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (bis : Array (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p)) : Array (DbItem) :=
  (bis.zipIdx).map fun bij =>
    let e := pre.getD bij.2 dbBiPreEmpty
    if e.usable && (dbBoxOf T e.vars 0 1).isSome then dbCompileBi facts bij.1 e
    else DbItem.always

/-- Per-constraint `active` (`¬ redundant`), threading the register file. -/
def dbActivePhase {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (csItems : Array (DbItem)) (csVars : Array (Array VarId)) (k : Nat)
    (st : Array Nat × Array Bool) : Array Nat × Array Bool :=
  if h : k < csItems.size then
    let ⟨regs, out⟩ := st
    let ⟨regs, red⟩ := dbConstraintRedundant facts T csItems[k] (csVars.getD k #[]) regs
    dbActivePhase facts T csItems csVars (k + 1) ⟨regs, out.push (!red)⟩
  else st
  termination_by csItems.size - k
  decreasing_by all_goals omega

def dbBucketsOf (nv : Nat) (vars : Array (Array VarId)) : Array (Array Nat) × Array Nat :=
  vars.zipIdx.foldl (init := (Array.replicate nv (#[] : Array Nat), (#[] : Array Nat)))
    fun st vi =>
      let ⟨buckets, varless⟩ := st
      match vi.1[0]? with
      | none => ⟨buckets, varless.push vi.2⟩
      | some v => ⟨buckets.modify v.index (fun b => b.push vi.2), varless⟩

/-- `denseVarsInListF`: every variable of the item is a key of the target. -/
@[inline] def dbSubset (vs xs : Array VarId) : Bool := vs.all (fun v => xs.contains v)

/-! ## Gather and preflight -/

structure DbGather (p : ℕ) where
  fullCount : Nat
  activeCs : Nat
  biCount : Nat
  informative : Bool
  domRed : Bool
  items : Array (DbItem)

def dbGatherCsAt (ctx : DbCtx p) (xs : Array VarId) (g : DbGather p) (pos : Nat) : DbGather p :=
  if dbSubset (ctx.csVars.getD pos #[]) xs then
    let ⟨fullCount, activeCs, biCount, informative, domRed, items⟩ := g
    if ctx.csActive.getD pos false then
      ⟨fullCount + 1, activeCs + 1, biCount, informative, domRed,
        items.push (ctx.csItems.getD pos .always)⟩
    else ⟨fullCount + 1, activeCs, biCount, informative, domRed, items⟩
  else g

def dbGatherBiAt (ctx : DbCtx p) (xs : Array VarId) (g : DbGather p) (pos : Nat) : DbGather p :=
  if ctx.biUsable.getD pos false && dbSubset (ctx.biVars.getD pos #[]) xs then
    let ⟨fullCount, activeCs, biCount, informative, domRed, items⟩ := g
    ⟨fullCount, activeCs, biCount + 1, informative || ctx.biInformative.getD pos false,
      domRed && ctx.biDomRed.getD pos false, items.push (ctx.biItems.getD pos .always)⟩
  else g

def dbGather (ctx : DbCtx p) (xs : Array VarId) : DbGather p :=
  let g0 : DbGather p :=
    { fullCount := ctx.csVarlessCount, activeCs := ctx.csVarlessItems.size,
      biCount := ctx.biVarlessCount, informative := ctx.biVarlessInformative,
      domRed := ctx.biVarlessDomRed, items := ctx.csVarlessItems }
  xs.foldl (init := g0) fun g v =>
    let g := (ctx.csBucket.getD v.index #[]).foldl (dbGatherCsAt ctx xs) g
    (ctx.biBucket.getD v.index #[]).foldl (dbGatherBiAt ctx xs) g

/-- Constant-domain answers for a target that needs no scan (`denseConstantDomainsV`). -/
def dbConstantDomains (p : ℕ) (keys : Array VarId) (doms : Array (DbDom)) :
    List (VarId × ZMod p) :=
  (keys.zipIdx.foldr (init := []) fun ki acc =>
    match DbDom.const? p (doms.getD ki.2 (.range 0)) with
    | some c => (ki.1, zmodOfNatP p c) :: acc
    | none => acc)

def dbPreflight (ctx : DbCtx p) (xs : Array VarId) : Option (DbPlan p) :=
  match dbDomsOf ctx.T xs with
  | none => none
  | some doms =>
    let box := doms.foldl (fun acc d => acc * d.size) 1
    if box ≤ maxEnumSize then
      let g := dbGather ctx xs
      let informative := g.fullCount != 0 || g.informative
      if informative && box * (g.fullCount + g.biCount) ≤ maxEnumWork then
        if g.activeCs == 0 && g.domRed && doms.all (fun d => d.size != 0) then
          some (.done (dbConstantDomains p xs doms))
        else
          some (.scan xs doms g.items ctx.constOk)
      else none
    else none

/-! ## The target loop: gate, then dedup, then preflight -/

def dbTargetStep (ctx : DbCtx p) (xs : Array VarId)
    (st : DbSeen × List (DbPlan p)) : DbSeen × List (DbPlan p) :=
  if xs.isEmpty then st
  else
    -- cheap gate first: every variable domained, and the box within the enumeration cap
    match dbBoxOf ctx.T xs 0 1 with
    | none => st
    | some box =>
      if maxEnumSize < box then st
      else
        let ⟨seen, plans⟩ := st
        let ⟨isNew, seen⟩ := seen.insertNew (dbKeyHash xs) (dbSortedKey xs)
        if !isNew then ⟨seen, plans⟩
        else
          match dbPreflight ctx xs with
          | none => ⟨seen, plans⟩
          | some plan => ⟨seen, plan :: plans⟩

def dbTargetsCs (ctx : DbCtx p) (k : Nat) (st : DbSeen × List (DbPlan p)) :
    DbSeen × List (DbPlan p) :=
  if h : k < ctx.csVars.size then
    dbTargetsCs ctx (k + 1) (dbTargetStep ctx ctx.csVars[k] st)
  else st
  termination_by ctx.csVars.size - k
  decreasing_by all_goals omega

def dbTargetsBis (ctx : DbCtx p) (k : Nat) (st : DbSeen × List (DbPlan p)) :
    DbSeen × List (DbPlan p) :=
  if h : k < ctx.biVars.size then
    dbTargetsBis ctx (k + 1) (dbTargetStep ctx ctx.biVars[k] st)
  else st
  termination_by ctx.biVars.size - k
  decreasing_by all_goals omega

/-! ## The invocation -/

/-- Build the context: variable lists, the three table phases, the flags and the buckets. -/
def dbBuildCtx (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DbCtx p :=
  let cs := d.algebraicConstraints.toArray
  let bis := d.busInteractions.toArray
  let csVars := cs.map (fun c => dbVarsOf c #[])
  let biVars := bis.map dbBiVars
  let nv := dbNvOf biVars (dbNvOf csVars 0)
  let T0 : DbTab p := ⟨Array.replicate nv none⟩
  let T1 := dbConstraintPhase cs csVars 0 T0
  let pre : Array (DbBiPre p) :=
    (bis.zipIdx).map fun bij => dbPreOne facts bij.1 (biVars.getD bij.2 #[])
  let ⟨T2, biInf⟩ := dbBusPhase facts bis pre 0 ⟨T1, #[]⟩
  let T := dbBytePhase pre 0 T2
  let csItems := dbCsItemsOf T cs csVars
  let biItems := dbBiItemsOf facts T bis pre
  let ⟨_, csActive⟩ := dbActivePhase facts T csItems csVars 0
    ⟨Array.replicate nv 0, #[]⟩
  let biDomRed := (bis.zipIdx).map fun bij =>
    let e := pre.getD bij.2 dbBiPreEmpty
    e.usable && (dbBoxOf T e.vars 0 1).isSome && dbBiDomainRedundant facts T bij.1 e
  let ⟨csBucket, csVarless⟩ := dbBucketsOf nv csVars
  let ⟨biBucket, biVarless⟩ := dbBucketsOf nv biVars
  let csVarlessItems := csVarless.filterMap (fun i =>
    if csActive.getD i false then some (csItems.getD i .always) else none)
  -- the variable-free usable interactions' summary (entry 155): count, flags and the constant
  -- verdict their obligations already decide
  let biSummary := biVarless.foldl (init := (0, false, true, true)) fun s i =>
    let e := pre.getD i dbBiPreEmpty
    if e.usable then
      (s.1 + 1, s.2.1 || biInf.getD i false, s.2.2.1 && biDomRed.getD i false,
        s.2.2.2 && dbItemOk facts #[] (biItems.getD i .always))
    else s
  { nv, T, csVars, csItems, csActive, csBucket,
    csVarlessCount := csVarless.size, csVarlessItems,
    biVars, biItems,
    biUsable := pre.map (fun e => e.usable),
    biInformative := biInf,
    biDomRed, biBucket,
    biVarlessCount := biSummary.1, biVarlessInformative := biSummary.2.1,
    biVarlessDomRed := biSummary.2.2.1, constOk := biSummary.2.2.2 }

/-- Domain-batch: builds a finite domain per variable (from constraints like `x*(x-1)=0` giving
    `x ∈ {0,1}`, and from bus range checks), enumerates the small Cartesian product of those
    domains, and for each variable that takes the same value in every surviving assignment infers
    that forced constant. Returns the map of all such `var := const` substitutions. -/
def dbDomainBatchσ (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseSolved p :=
  let ctx := dbBuildCtx bs facts d
  let ⟨_, plansRev⟩ := dbTargetsBis ctx 0 (dbTargetsCs ctx 0 ⟨⟨∅⟩, []⟩)
  let plans := plansRev.reverse
  -- run serially: handing plans to `Task.spawn` marks the shared objects multi-threaded, and every
  -- later refcount touch on them — in this pass and in every pass after it — becomes atomic
  let results := dbRunPlans facts ctx.nv plans
  results.foldl (fun dσ forced =>
    dσ.insertAll (forced.map (fun f => (f.1, DenseExpr.const f.2)))) DenseSolved.empty

/-- The value-only dense domain-batch transform, over the rebuilt engine. -/
def dbDomainBatchTransform (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then applyσ (dbDomainBatchσ bs facts d) d else d

end ApcOptimizer.Dense
