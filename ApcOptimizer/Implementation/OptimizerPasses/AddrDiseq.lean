import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Dense address-disequality certificate library

Certificate-building/checking functions the dense `busUnify` / `busPairCancel` passes consult to
refute a memory-address match. Exports no pass; correctness lives in `Proofs/AddrDiseq.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Recognizing a two-root constraint (dense) -/

/-- The two-root entry for `x` from a product's already-linearized factors. -/
def denseTwoRootOfLins (l1 l2 : DenseLinExpr p) (x : VarId) :
    Option (ZMod p × DenseLinExpr p × ZMod p) :=
  let k := l1.coeff x
  let A := (l1.others x).norm
  let A2 := (l2.others x).norm
  if k ≠ 0 ∧ l2.coeff x = k ∧ A2.terms = A.terms then some (k, A, A2.const - A.const)
  else none

/-- One `DenseZModOps p` for the two coefficients, the two normal forms and the zero test. -/
def denseTwoRootOfLinsWith (ops : DenseZModOps p) (l1 l2 : DenseLinExpr p) (x : VarId) :
    Option (ZMod p × DenseLinExpr p × ZMod p) :=
  let k := denseCoeffSumWith ops x l1.terms
  let A := (l1.others x).normWith ops
  let A2 := (l2.others x).normWith ops
  if k ≠ ops.zero ∧ denseCoeffSumWith ops x l2.terms = k ∧ A2.terms = A.terms then
    some (k, A, A2.const - A.const)
  else none

def denseTwoRootOfLinsFast (l1 l2 : DenseLinExpr p) (x : VarId) :
    Option (ZMod p × DenseLinExpr p × ZMod p) :=
  denseTwoRootOfLinsWith denseZModOps l1 l2 x

theorem denseTwoRootOfLinsWith_eq (ops : DenseZModOps p) (l1 l2 : DenseLinExpr p) (x : VarId) :
    denseTwoRootOfLinsWith ops l1 l2 x = denseTwoRootOfLins l1 l2 x := by
  simp only [denseTwoRootOfLinsWith, denseTwoRootOfLins, DenseLinExpr.coeff,
    denseCoeffSumWith_eq, DenseLinExpr.normWith_eq, ops.zero_eq]

@[csimp] theorem denseTwoRootOfLins_eq_fast :
    @denseTwoRootOfLins = @denseTwoRootOfLinsFast := by
  funext p l1 l2 x
  exact (denseTwoRootOfLinsWith_eq denseZModOps l1 l2 x).symm

/-- The two-root decomposition of a dense constraint relative to `x`: `some (k, A, δ)` when the
    constraint is a product of two affine factors, both linear in `x` with the same nonzero
    coefficient `k`, whose `x`-free parts differ by the constant `δ`. -/
def denseTwoRootOf? (c : DenseExpr p) (x : VarId) : Option (ZMod p × DenseLinExpr p × ZMod p) :=
  match c with
  | .mul f1 f2 =>
    match denseLinearize f1, denseLinearize f2 with
    | some l1, some l2 => denseTwoRootOfLins l1 l2 x
    | _, _ => none
  | _ => none

/-! ## Substituting a two-root branch into a linear form -/

/-- The two affine forms obtained by replacing the variable with coefficient `cx` in `rest + cx·x`
    by the two roots `x = -(k⁻¹·A)` and `x = -(k⁻¹·A) - k⁻¹·δ` of a `denseTwoRootOf?` decomposition
    `(k, A, δ)`. -/
def densePtrBranchesOf (k : ZMod p) (A : DenseLinExpr p) (δ cx : ZMod p) (rest : DenseLinExpr p) :
    DenseLinExpr p × DenseLinExpr p :=
  let r1 := A.scale (-(k⁻¹))
  let r2 := r1.add ⟨-(k⁻¹ * δ), []⟩
  ((rest.add (r1.scale cx)).norm, (rest.add (r2.scale cx)).norm)

/-! ## A dense two-root map (memoized `denseTwoRootOf?`)

Precomputed once per pass into a hash map (per-pair scanning is quadratic on keccak's window). -/

/-- Per-variable two-root decomposition data (data only). -/
structure DenseTwoRootMap (p : ℕ) where
  map : Std.HashMap VarId (ZMod p × DenseLinExpr p × ZMod p)

namespace DenseTwoRootMap

def empty : DenseTwoRootMap p where
  map := ∅

/-- Insert an entry (last write wins). -/
def insertEntry (T : DenseTwoRootMap p) (v : VarId) (k : ZMod p) (A : DenseLinExpr p) (δ : ZMod p) :
    DenseTwoRootMap p where
  map := T.map.insert v (k, A, δ)

/-- Insert the two-root entry (if any, with a unit coefficient) for each of `c`'s variables. -/
def addVars (c : DenseExpr p) : DenseTwoRootMap p → List VarId → DenseTwoRootMap p
  | T, [] => T
  | T, v :: vs =>
    match denseTwoRootOf? c v with
    | some (k, A, δ) =>
      if k * k⁻¹ = 1 then addVars c (T.insertEntry v k A δ) vs
      else addVars c T vs
    | none => addVars c T vs

/-- `addVars` from a product's linearized factors. -/
def addVarsLins (l1 l2 : DenseLinExpr p) : DenseTwoRootMap p → List VarId → DenseTwoRootMap p
  | T, [] => T
  | T, v :: vs =>
    match denseTwoRootOfLins l1 l2 v with
    | some (k, A, δ) =>
      if k * k⁻¹ = 1 then addVarsLins l1 l2 (T.insertEntry v k A δ) vs
      else addVarsLins l1 l2 T vs
    | none => addVarsLins l1 l2 T vs

/-- `addVars` with the product's factors linearized once instead of once per variable; the compiled
    twin of `addVars` (`addVars_eq_fast`). -/
def addVarsFast (c : DenseExpr p) (T : DenseTwoRootMap p) (vs : List VarId) : DenseTwoRootMap p :=
  match c with
  | .mul f1 f2 =>
    match denseLinearize f1, denseLinearize f2 with
    | some l1, some l2 => addVarsLins l1 l2 T vs
    | _, _ => T
  | _ => T

theorem addVarsLins_eq {f1 f2 : DenseExpr p} {l1 l2 : DenseLinExpr p}
    (h1 : denseLinearize f1 = some l1) (h2 : denseLinearize f2 = some l2) :
    ∀ (T : DenseTwoRootMap p) (vs : List VarId),
      addVarsLins l1 l2 T vs = addVars (.mul f1 f2) T vs := by
  have hentry : ∀ v, denseTwoRootOf? (.mul f1 f2) v = denseTwoRootOfLins l1 l2 v := by
    intro v; simp only [denseTwoRootOf?, h1, h2]
  intro T vs
  induction vs generalizing T with
  | nil => rfl
  | cons v rest ih =>
      rw [addVarsLins, addVars, hentry v]
      cases denseTwoRootOfLins l1 l2 v with
      | none => exact ih T
      | some kAδ => obtain ⟨k, A, δ⟩ := kAδ; dsimp only; split <;> exact ih _

/-- `addVars` never inserts when no variable has a two-root entry. -/
theorem addVars_of_none {c : DenseExpr p} (h : ∀ v, denseTwoRootOf? c v = none) :
    ∀ (T : DenseTwoRootMap p) (vs : List VarId), addVars c T vs = T := by
  intro T vs
  induction vs generalizing T with
  | nil => rfl
  | cons v rest ih => rw [addVars, h v]; exact ih T

@[csimp] theorem addVars_eq_fast :
    @DenseTwoRootMap.addVars = @DenseTwoRootMap.addVarsFast := by
  funext q c T vs
  cases c with
  | const n => exact addVars_of_none (fun _ => rfl) T vs
  | var i => exact addVars_of_none (fun _ => rfl) T vs
  | add a b => exact addVars_of_none (fun _ => rfl) T vs
  | mul f1 f2 =>
      cases h1 : denseLinearize f1 with
      | none =>
          rw [addVars_of_none (fun _ => by simp [denseTwoRootOf?, h1]) T vs]
          simp [addVarsFast, h1]
      | some l1 =>
          cases h2 : denseLinearize f2 with
          | none =>
              rw [addVars_of_none (fun _ => by simp [denseTwoRootOf?, h1, h2]) T vs]
              simp [addVarsFast, h1, h2]
          | some l2 =>
              rw [← addVarsLins_eq h1 h2 T vs]
              simp [addVarsFast, h1, h2]

/-- Fold `addVars` over a constraint list, with the candidate variables of each constraint
    restricted to `vars`: an entry for a variable outside `vars` is never looked up
    (`buildForAddrs`), and `denseTwoRootOfLins` normalizes both factors per candidate variable, so
    this is the whole cost of the build. -/
def addAllFor (vars : Std.HashSet VarId) :
    DenseTwoRootMap p → (pending : List (DenseExpr p)) → DenseTwoRootMap p
  | T, [] => T
  | T, c :: rest => addAllFor vars (addVars c T (c.vars.filter vars.contains).eraseDups) rest

/-- Build the map for a constraint list, indexing only the variables in `vars` (empty on
    composite `p`). -/
def buildFor (vars : Std.HashSet VarId) (constraints : List (DenseExpr p)) : DenseTwoRootMap p :=
  if Nat.Prime p then addAllFor vars empty constraints else empty

end DenseTwoRootMap

/-- All affine two-root reductions of a dense expression `E`: for each variable of the linearized
    form that carries a two-root entry, the pair of branch forms `densePtrBranchesOf`. -/
def densePtrReductions (T : DenseTwoRootMap p) (E : DenseExpr p) :
    List (DenseLinExpr p × DenseLinExpr p) :=
  match denseLinearize E with
  | none => []
  | some L =>
    (L.terms.map Prod.fst).eraseDups.filterMap (fun v =>
      match T.map[v]? with
      | some (k, A, δ) => some (densePtrBranchesOf k A δ (L.coeff v) (L.others v))
      | none => none)

/-- Runtime `densePtrReductions`: the two-root variables are deduplicated through the hash-bucketed
    twin. The list is a linear form's variable list, and the pass queries this per compared message
    pair, so the `List.eraseDups` quadratic showed up directly in `busPairCancel`. -/
def densePtrReductionsFast (T : DenseTwoRootMap p) (E : DenseExpr p) :
    List (DenseLinExpr p × DenseLinExpr p) :=
  match denseLinearize E with
  | none => []
  | some L =>
    (HashedDedup.hashedEraseDups (hash ·) (L.terms.map Prod.fst)).filterMap (fun v =>
      match T.map[v]? with
      | some (k, A, δ) => some (densePtrBranchesOf k A δ (L.coeff v) (L.others v))
      | none => none)

@[csimp] theorem densePtrReductions_eq_fast :
    @densePtrReductions = @densePtrReductionsFast := by
  funext q T E
  show densePtrReductions T E = _
  unfold densePtrReductions densePtrReductionsFast
  cases denseLinearize E with
  | none => rfl
  | some L => dsimp only; rw [HashedDedup.hashedEraseDups_eq]

/-! ## Nonzero-constant differences, by canonical term key

Two linear forms differ by a nonzero constant exactly when their *canonical* terms — merged,
zero-dropped, sorted by variable — agree and their constants do not. A key is derived once per
expression, so the certificate arms below compare an integer and a list instead of normalizing
`a − b` per compared pair. Soundness is `denseKeyDiffNZ_sound` (`Proofs/AddrDiseq.lean`). -/

/-- The canonical form of a linear form's terms: merged, zero-dropped, sorted by variable. -/
def denseTermKey (l : DenseLinExpr p) : List (VarId × ZMod p) :=
  l.norm.terms.mergeSort (fun a b => decide (a.1.index ≤ b.1.index))

/-- Hash *of the canonical key*, which gates the list compare: unequal hashes are unequal keys, and
    that is the common case. -/
def denseTermKeyHash (k : List (VarId × ZMod p)) : UInt64 :=
  k.foldl (fun h t => mixHash h (mixHash (hash t.1) (hash t.2.val))) 0

/-- The two forms differ by a nonzero field constant. -/
def denseKeyDiffNZ (a b : DenseLinExpr p) : Bool :=
  let ka := denseTermKey a
  let kb := denseTermKey b
  (denseTermKeyHash ka == denseTermKeyHash kb && decide (ka = kb)) && decide (a.const ≠ b.const)

/-- One two-root reduction, keyed: the canonical key of its branches with that key's hash, plus the
    two branch constants. Both branches differ from each other only by a constant
    (`densePtrReductions_key`), so one key describes the pair and the four branch-pair differences
    of `denseRedKeysNeq` are four constant comparisons. -/
def denseRedKey (r : DenseLinExpr p × DenseLinExpr p) :
    UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p :=
  let k := denseTermKey r.1
  (denseTermKeyHash k, k, r.1.const, r.2.const)

/-- All four branch-pair differences of two keyed reductions are nonzero constants. -/
def denseRedKeysNeq (r r' : UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p) : Bool :=
  ((r.1 == r'.1 && decide (r.2.1 = r'.2.1)) &&
    (decide (r.2.2.1 ≠ r'.2.2.1) && decide (r.2.2.1 ≠ r'.2.2.2))) &&
    (decide (r.2.2.2 ≠ r'.2.2.1) && decide (r.2.2.2 ≠ r'.2.2.2))

/-! ## The expression- and address-level certificates -/

/-- Two dense expressions provably evaluate differently: some two-root reduction of each yields
    four branch-pair differences that are all nonzero field constants. -/
def denseExprTwoRootNeq (T : DenseTwoRootMap p) (e e' : DenseExpr p) : Bool :=
  ((densePtrReductions T e).map denseRedKey).any (fun r =>
    ((densePtrReductions T e').map denseRedKey).any (denseRedKeysNeq r))

/-- Some address slot of `S` and `bi` provably evaluates differently: the two interactions have
    different addresses. -/
def denseAddrTwoRootNeq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' => denseExprTwoRootNeq T e e'
    | _, _ => false)

/-! ## The affine (same-base) address-disequality certificate -/

/-- Some address slot of `S` and `bi` linearizes to two affine forms differing by a nonzero field
    constant: the two interactions provably have different addresses. -/
def denseAddrAffineNeq (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.any (fun slot =>
    match S.payload[slot]?, bi.payload[slot]? with
    | some e, some e' =>
      (match denseLinearize e, denseLinearize e' with
       | some L, some L' => denseKeyDiffNZ L L'
       | _, _ => false)
    | _, _ => false)

/-! ## The nonzero-witness (register-vs-RAM) address-disequality certificate -/

def denseIsZeroLinImpl (l : DenseLinExpr p) : Bool :=
  l.norm.terms.isEmpty && zmodIsZero l.norm.const

/-- A dense linear form is identically zero (empty terms and zero constant after normalization). -/
def denseIsZeroLin (l : DenseLinExpr p) : Bool :=
  l.norm.terms.isEmpty && zmodIsZero l.norm.const

@[csimp] theorem denseIsZeroLin_eq_impl : @denseIsZeroLin = @denseIsZeroLinImpl := by
  funext q l
  simp [denseIsZeroLin, denseIsZeroLinImpl]

/-- Nonzero linear factors of a single reciprocal product `a * b + r` with `r` a nonzero constant:
    `a·b = −r ≠ 0`, so each factor that linearizes is a nonzero witness. -/
def denseReciprocalWitsProd (a b r : DenseExpr p) : List (DenseLinExpr p) :=
  match denseLinearize r with
  | some lr =>
    if lr.terms.isEmpty && decide (lr.const ≠ 0) then
      (match denseLinearize a with | some la => [la] | none => []) ++
      (match denseLinearize b with | some lb => [lb] | none => [])
    else []
  | none => []

/-- Nonzero linear witnesses recognized from a constraint of the form `a·b + r = 0` (in either
    additive order), with `r` a nonzero constant. -/
def denseReciprocalWits? (c : DenseExpr p) : List (DenseLinExpr p) :=
  match c with
  | .add e1 e2 =>
    match e1 with
    | .mul a b => denseReciprocalWitsProd a b e2
    | _ => match e2 with
           | .mul a b => denseReciprocalWitsProd a b e1
           | _ => []
  | _ => []

/-- Order-independent hash of a linear form's *value*: the merged normal form's constant mixed with
    an order-insensitive (additive) combination of its `(variable, coefficient)` terms. Two forms
    with equal value (`denseIsZeroLin` of their difference) share this hash regardless of term
    order, so it keys the witness index below without ever missing a match. -/
def denseLinHash (l : DenseLinExpr p) : UInt64 :=
  let n := l.norm
  n.terms.foldl (fun h t => h + mixHash (hash t.1) (hash t.2.val)) (hash n.const.val)

/-- Bucket a witness list by `denseLinHash`, so a query needs only the two matching buckets rather
    than a scan of every witness. Untrusted (re-checked at use); membership soundness is
    `denseNZIndexOf_mem`. -/
def denseNZIndexOf (wits : List (DenseLinExpr p)) : Std.HashMap UInt64 (List (DenseLinExpr p)) :=
  wits.foldr (fun g m => m.insert (denseLinHash g) (g :: m.getD (denseLinHash g) [])) ∅

/-- Linear forms provably nonzero under a constraint list, plus a `denseLinHash` index over them. -/
structure DenseNonzeroWits (p : ℕ) where
  wits : List (DenseLinExpr p)
  index : Std.HashMap UInt64 (List (DenseLinExpr p))

/-- Collect every reciprocal-witness linear form from the constraint list. -/
def DenseNonzeroWits.build (constraints : List (DenseExpr p)) : DenseNonzeroWits p :=
  let w := constraints.flatMap denseReciprocalWits?
  ⟨w, denseNZIndexOf w⟩

/-- `Σ_{f ∈ fields} (m.payload[f] − S.payload[f])` as a dense linear form; `none` if any listed
    slot is absent from either payload or is nonlinear. -/
def denseDiffSumOver (S m : BusInteraction (DenseExpr p)) : List Nat → Option (DenseLinExpr p)
  | [] => some ⟨0, []⟩
  | f :: fs =>
    match denseDiffSumOver S m fs with
    | none => none
    | some acc =>
      match S.payload[f]?, m.payload[f]? with
      | some eS, some eM =>
        match denseLinearize eS, denseLinearize eM with
        | some lS, some lM => some ((lM.add (lS.scale (-1))).add acc)
        | _, _ => none
      | _, _ => none

/-- The address slots of `S` and `m` provably differ: some subset `T` of the shape's address
    fields has limb-difference sum `Σ_{i∈T}(mᵢ − Sᵢ)` equal (up to sign) to a nonzero witness `g`. -/
def denseAddrNonzeroNeq (shape : MemoryBusShape) (nw : DenseNonzeroWits p)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  shape.addressFields.sublists.any (fun T =>
    match denseDiffSumOver S m T with
    | some D =>
      (nw.index.getD (denseLinHash D) [] ++ nw.index.getD (denseLinHash (D.scale (-1))) []).any
        (fun g => denseIsZeroLin (D.add (g.scale (-1))) || denseIsZeroLin (D.add g))
    | none => false)

/-! ## Restricting the two-root map to the variables that can be queried -/

/-- Does the expression mention a variable of `s`? -/
def DenseExpr.mentionsAny (s : Std.HashSet VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var i => s.contains i
  | .add a b => a.mentionsAny s || b.mentionsAny s
  | .mul a b => a.mentionsAny s || b.mentionsAny s

/-- The variables a two-root lookup can reach: those of an address-slot expression of an
    interaction on a memory-shaped bus, at *that bus's own* address fields. Every certificate arm
    that reads the table is gated on the compared message being on the candidate's bus, and
    `densePtrReductions` keys on the queried form's own variables, so no other entry is read. -/
def denseAddrSlotVars (memShape : Nat → Option MemoryBusShape)
    (bis : List (BusInteraction (DenseExpr p))) : Std.HashSet VarId :=
  bis.foldl (fun s bi =>
    match memShape bi.busId with
    | some shape =>
      shape.addressFields.foldl (fun s slot =>
        match bi.payload[slot]? with
        | some e => e.vars.foldl (fun s v => s.insert v) s
        | none => s) s
    | none => s) ∅

/-- The two-root map over just the constraints mentioning an address-slot variable, and only for
    those variables. Every entry a lookup can reach is unchanged: an entry for `v` is only ever
    inserted by a constraint mentioning `v` (`addVars` folds over `c.vars`), and only address-slot
    variables are looked up (`densePtrReductions` keys on the queried form's own variables). -/
def DenseTwoRootMap.buildForAddrs (memShape : Nat → Option MemoryBusShape)
    (bis : List (BusInteraction (DenseExpr p))) (constraints : List (DenseExpr p)) :
    DenseTwoRootMap p :=
  let vars := denseAddrSlotVars memShape bis
  DenseTwoRootMap.buildFor vars (constraints.filter (fun c => c.mentionsAny vars))

/-- Both address-disequality certificate tables, bundled so they thread through a pass as one
    memoized value. -/
structure DenseAddrCerts (p : ℕ) where
  tworoot : DenseTwoRootMap p
  nonzero : DenseNonzeroWits p

/-- Build both certificate tables from the constraint list, the two-root map over the address-slot
    constraints only (`DenseTwoRootMap.buildForAddrs`). -/
def DenseAddrCerts.build (memShape : Nat → Option MemoryBusShape)
    (bis : List (BusInteraction (DenseExpr p))) (constraints : List (DenseExpr p)) :
    DenseAddrCerts p :=
  ⟨DenseTwoRootMap.buildForAddrs memShape bis constraints, DenseNonzeroWits.build constraints⟩

end ApcOptimizer.Dense
