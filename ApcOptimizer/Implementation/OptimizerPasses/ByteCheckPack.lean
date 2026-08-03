import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense single-value byte-check packing

Runtime recognizers and the pair-finding scan for `byteCheckPack`; the pass is assembled in
`Proofs/ByteCheckPack.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- `255 − e` as a dense expression. -/
def denseComplExpr (e : DenseExpr p) : DenseExpr p := .add (.const 255) (.mul (.const (-1)) e)

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment? -/
def denseIsByteCompl (a b : DenseExpr p) : Bool :=
  (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue? == some 0

/-- The byte-check shapes recognizable on a `byteXorSpec` bus, by decoded payload
    `(op, o₁, o₂, r)`: the XOR self-check `[x, x, 0]`, the XOR-with-zero and NOT/XOR-255 mirrors
    (the latter gated `256 ≤ p`), the OR-identity (`x | 0 = x`) mirrors, and the packed pair. -/
inductive DenseByteShape
  | selfCheck | xorZeroL | xorZeroR | not255L | not255R | orIdL | orIdR | pair

/-- The decoded operands a shape byte-checks (`…L` checks `o₁`, `…R` checks `o₂`). -/
def DenseByteShape.operands (sh : DenseByteShape) (o1 o2 : DenseExpr p) : List (DenseExpr p) :=
  match sh with
  | .selfCheck => [o1] | .xorZeroL => [o1] | .xorZeroR => [o2] | .not255L => [o1]
  | .not255R => [o2] | .orIdL => [o1] | .orIdR => [o2] | .pair => [o1, o2]

/-- Structural constant test: `e` is literally `const c`. -/
def denseCmpStructural (e : DenseExpr p) (c : ZMod p) : Bool := e == DenseExpr.const c

/-- Folded constant test: `e` constant-folds to `c`. -/
def denseCmpFolded (e : DenseExpr p) (c : ZMod p) : Bool := e.constValue? == some c

/-- Classify a byte check through the VM-neutral `byteXorSpec` (byte bound `256`), testing
    constant slots with `cmp`: the recognized `DenseByteShape` with the spec and decoded operands,
    or `none`. Sound for any `cmp` whose hits pin evaluation (`denseByteShape?_sound`,
    `Proofs/ByteCheckPack.lean`). -/
def denseByteShapeWith? (cmp : DenseExpr p → ZMod p → Bool) (spec : ByteXorSpec p)
    (bi : BusInteraction (DenseExpr p)) :
    Option (DenseByteShape × ByteXorSpec p × DenseExpr p × DenseExpr p) :=
    if decide (spec.bound = 256) then
      match spec.decode bi.payload with
      | none => none
      | some (op, o1, o2, r) =>
        if cmp op spec.xorOp then
          if o1 == o2 && cmp r 0 then some (.selfCheck, spec, o1, o2)
          else if cmp o2 0 && o1 == r then some (.xorZeroL, spec, o1, o2)
          else if cmp o1 0 && o2 == r then some (.xorZeroR, spec, o1, o2)
          else if decide (256 ≤ p) && cmp o2 255 && denseIsByteCompl o1 r then
            some (.not255L, spec, o1, o2)
          else if decide (256 ≤ p) && cmp o1 255 && denseIsByteCompl o2 r then
            some (.not255R, spec, o1, o2)
          else none
        else if spec.orOp.any (fun oop => cmp op oop) then
          if cmp o2 0 && o1 == r then some (.orIdL, spec, o1, o2)
          else if cmp o1 0 && o2 == r then some (.orIdR, spec, o1, o2)
          else none
        else if cmp op spec.pairOp && cmp r 0 then some (.pair, spec, o1, o2)
        else none
    else none

/-- `denseByteShapeWith?` against the bus's own spec. -/
def denseByteShape? (cmp : DenseExpr p → ZMod p → Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseByteShape × ByteXorSpec p × DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec => denseByteShapeWith? cmp spec bi

/-- The value byte-checked by a multiplicity-1 single-value byte check on a bus with spec `spec`:
    the operand of a structurally recognized single-operand shape, e.g. `x` for the XOR self-check
    `[x, x, 0]`; `none` otherwise. -/
def denseSvCheckWith? (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p)) :
    Option (DenseExpr p) :=
  if bi.multiplicity = DenseExpr.const 1 then
    match denseByteShapeWith? denseCmpStructural spec bi with
    | some (sh, _, o1, o2) =>
      match sh.operands o1 o2 with
      | [e] => some e
      | _ => none
    | none => none
  else none

/-- `denseSvCheckWith?` against the bus's own spec. -/
def denseSvCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec => denseSvCheckWith? spec bi

/-- The recognizer's full result: the checked value together with the bus's byte-XOR spec, which
    the pair check emitted in its place is built from. -/
def denseBpSv? (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p)) :
    Option (ByteXorSpec p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec => (denseSvCheckWith? spec bi).map (fun e => (spec, e))

/-- What the plan proposes at a position: leave it alone, open a pack (the position becomes the
    pair check), or close one (the position is dropped into the pair opened to its left). -/
inductive DenseBpAction
  | keep | openPack | closePack

/-- Resolve `facts.byteXorSpec busId` through the memo `specs`, returning the extended memo. -/
def denseBpSpecOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (specs : List (Nat × Option (ByteXorSpec p))) (busId : Nat) :
    Option (ByteXorSpec p) × List (Nat × Option (ByteXorSpec p)) :=
  match specs.lookup busId with
  | some s => (s, specs)
  | none => let s := facts.byteXorSpec busId; (s, (busId, s) :: specs)

/-- The pairing plan, built left to right: single-value byte checks on a bus alternate between
    opening a pack and closing it, so the pairs are the bus's checks taken two at a time in source
    order. `none` when no bus ever closes one, which makes the pass return its input untouched.
    `specs` memoizes `facts.byteXorSpec`, whose OpenVM instance rebuilds the spec record — and with
    it the field's `ZMod` literals — on every call; `opened` is the buses with a pack open. Both
    are assoc lists because a circuit has few buses, and one or two byte-XOR ones.

    The plan is **untrusted**: `denseBpBack` re-checks every action it acts on, so a wrong plan
    costs packing opportunities, never soundness. It comes out reversed, which is the order
    `denseBpBack` consumes it in. -/
def denseBpPlan (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → List (Nat × Option (ByteXorSpec p)) → List Nat →
      Bool → List DenseBpAction → Option (List DenseBpAction)
  | [], _, _, packed, acc => if packed then some acc else none
  | b :: rest, specs, opened, packed, acc =>
    match denseBpSpecOf bs facts specs b.busId with
    | (none, specs') => denseBpPlan bs facts rest specs' opened packed (.keep :: acc)
    | (some spec, specs') =>
      match denseSvCheckWith? spec b with
      | none => denseBpPlan bs facts rest specs' opened packed (.keep :: acc)
      | some _ =>
        if opened.contains b.busId then
          denseBpPlan bs facts rest specs' (opened.erase b.busId) true (.closePack :: acc)
        else
          denseBpPlan bs facts rest specs' (b.busId :: opened) packed (.openPack :: acc)

/-- A closed check awaiting the pack opened to its left: its bus, the value it checks, and the
    interaction itself (which supplies that value's variables). -/
abbrev DenseBpDrop (p : ℕ) := Nat × DenseExpr p × BusInteraction (DenseExpr p)

/-- Take the first drop on `busId` out of `dropped`. -/
def denseBpTake (busId : Nat) : List (DenseBpDrop p) →
    Option (DenseExpr p × BusInteraction (DenseExpr p) × List (DenseBpDrop p))
  | [] => none
  | q :: rest =>
    if q.1 = busId then some (q.2.1, q.2.2, rest)
    else (denseBpTake busId rest).map (fun r => (r.1, r.2.1, q :: r.2.2))

/-- Apply the plan right to left, building the result in source order: a closed check goes into
    `dropped`, and an opened one absorbs its bus's drop into a pair check. Every action is
    re-checked against the recognizer, and a pack is only emitted against a drop actually held, so
    the two interactions a pair check replaces are exactly the ones it obliges (soundness in
    `Proofs/ByteCheckPack.lean`). A leftover drop means the plan was inconsistent; the caller then
    discards the whole result. -/
def denseBpBack (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → List DenseBpAction → List (DenseBpDrop p) →
      List (BusInteraction (DenseExpr p)) →
      List (DenseBpDrop p) × List (BusInteraction (DenseExpr p))
  | [], _, dropped, out => (dropped, out)
  | b :: rest, plan, dropped, out =>
    match plan.headD .keep with
    | .keep => denseBpBack bs facts rest plan.tail dropped (b :: out)
    | .closePack =>
      match denseBpSv? bs facts b with
      | some (_, e) => denseBpBack bs facts rest plan.tail ((b.busId, e, b) :: dropped) out
      | none => denseBpBack bs facts rest plan.tail dropped (b :: out)
    | .openPack =>
      match denseBpSv? bs facts b with
      | some (spec, e) =>
        match denseBpTake b.busId dropped with
        | some (e', _, dropped') =>
          denseBpBack bs facts rest plan.tail dropped'
            (denseMkBytePair spec b.busId e e' :: out)
        | none => denseBpBack bs facts rest plan.tail dropped (b :: out)
      | none => denseBpBack bs facts rest plan.tail dropped (b :: out)

/-- Pack single-value byte checks pairwise, per byte-XOR bus, first come first served: `x < 256`
    and `y < 256` on the bitwise bus become one `[x, y]` pair check at the first one's position.
    The input list is returned unchanged when nothing pairs. -/
def denseBytePackBis (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) : List (BusInteraction (DenseExpr p)) :=
  match denseBpPlan bs facts bis [] [] false [] with
  | none => bis
  | some revPlan =>
    match denseBpBack bs facts bis.reverse revPlan [] [] with
    | ([], out) => out
    | _ => bis

end ApcOptimizer.Dense
