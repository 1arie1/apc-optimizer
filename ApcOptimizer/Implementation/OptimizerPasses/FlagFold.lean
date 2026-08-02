import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BoxRewrite
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FxSubst

set_option autoImplicit false

/-! # Dense `flagFold` (runtime; correctness in `Proofs/FlagFold.lean`)

One fused transform, `denseFlagFoldF`, running the four flagFold parts over shared state:

* **A** entailed nonlinear substitution across matched scaled range checks (`denseFxSubstF`);
* **B** multilinear rewriting of over-bound expressions (`boxRewriteWith`);
* **C** box-tautology constraints replaced by `0` (`ffBoxTauto`);
* **D** pointwise-duplicate stateless interactions dropped (`ffPdDropF`).

Parts B, C and D all ask `denseFindDomainAlg` over the *single-variable* constraints. That lives in
one `VarId.index`-keyed table (`FfTab`) built once per constraint-list version: the certificates
read it through `ffTabGet`, and its soundness is `ffTabGet_eq` — every entry is its own bucket's
`denseFindDomainAlg` verdict, and every bucket holds single-variable constraints of the system.

Unguarded here — box-rewrite intermediates legitimately exceed the bound — so the whole chain runs
under ONE `guardDegree b` at its `cleanupPasses` entry. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The shared finite-domain table

Single-variable constraints are recognised by a walk whose state is a single scalar (`0` no
variable yet, `1` two or more distinct, `i + 2` exactly the variable of index `i`), so it
short-circuits at the second distinct variable and allocates nothing — a three-constructor
inductive state would allocate one node per variable leaf. -/

def ffSoleGo : DenseExpr p → Nat → Nat
  | .const _, s => s
  | .var i, s => if s == 0 then i.index + 2 else if s == i.index + 2 then s else 1
  | .add a b, s => let s' := ffSoleGo a s; if s' == 1 then 1 else ffSoleGo b s'
  | .mul a b, s => let s' := ffSoleGo a s; if s' == 1 then 1 else ffSoleGo b s'

/-- The single variable of `e`, or `none` when it has zero or two-or-more distinct variables. -/
@[inline] def ffSole (e : DenseExpr p) : Option VarId :=
  let s := ffSoleGo e 0
  if 2 ≤ s then some ⟨s - 2⟩ else none

/-- One past the largest scalar state, so every `ffSole` variable indexes inside the table. -/
def ffTabSize (cs : List (DenseExpr p)) : Nat :=
  cs.foldl (fun n c => max n (ffSoleGo c 0)) 0

/-- The single-variable constraints bucketed by their variable, `VarId.index`-keyed, source order
    (`foldr` prepends). -/
def ffBucketsOf (cs : List (DenseExpr p)) : Array (List (DenseExpr p)) :=
  cs.foldr (fun c B =>
    match ffSole c with
    | some v => B.set! v.index (c :: B.getD v.index [])
    | none => B) (Array.replicate (ffTabSize cs) [])

@[inline] def ffBucketOf (B : Array (List (DenseExpr p))) (v : VarId) : List (DenseExpr p) :=
  B.getD v.index []

/-- Finite domains keyed by `VarId.index`: entry `i` is its bucket's `denseFindDomainAlg` verdict,
    derived once per invocation instead of per query. -/
abbrev FfTab (p : ℕ) := Array (Option (List (ZMod p)))

def ffTabOf (B : Array (List (DenseExpr p))) : FfTab p :=
  B.mapFinIdx (fun i bl _ => denseFindDomainAlg bl ⟨i⟩)

@[inline] def ffTabGet (T : FfTab p) (v : VarId) : Option (List (ZMod p)) := T.getD v.index none

/-! ## Part C's rejection gate

`denseBtCert` builds a deduplicated variable list and a domain association list before it can
reject on "some variable has no finite domain", which is what rejects almost every constraint.
`ffAllBoxed` is that conjunct alone: one allocation-free walk aborting at the first variable
without a domain. -/

def ffAllBoxed (T : FfTab p) : DenseExpr p → Bool
  | .const _ => true
  | .var i => (ffTabGet T i).isSome
  | .add a b => ffAllBoxed T a && ffAllBoxed T b
  | .mul a b => ffAllBoxed T a && ffAllBoxed T b

/-- `denseBtCert` behind its own cheapest conjunct (`ffBtCert_eq`). -/
def ffBtCert (T : FfTab p) (c : DenseExpr p) : Bool :=
  ffAllBoxed T c && denseBtCert (ffTabGet T) c

/-- Box-tautology replacement, table-served. -/
def DenseConstraintSystem.ffBoxTauto (d : DenseConstraintSystem p) (T : FfTab p) :
    DenseConstraintSystem p :=
  { d with algebraicConstraints := d.algebraicConstraints.map (fun c =>
      if ffBtCert T c then DenseExpr.const 0 else c) }

/-! ## Part B's skip gate

`denseBrRw` is the identity on a within-bound expression, so a system with nothing over its bound
needs neither the rewrite nor the domain table it would consult. -/

def ffAnyOverBound (b : DegreeBound) (d : DenseConstraintSystem p) : Bool :=
  d.algebraicConstraints.any (fun c => !(c.degree ≤ b.identities)) ||
  d.busInteractions.any (fun bi =>
    !(bi.multiplicity.degree ≤ b.busInteractions) ||
    bi.payload.any (fun e => !(e.degree ≤ b.busInteractions)))

/-! ## Part D: the duplicate-proposal sweep

Everything in this section is a *proposal generator*: `ffPdDropF` re-verifies every proposal with
`densePdKeep` before it drops anything, so none of it carries a soundness obligation. What it must
be is precise — a proposal `densePdKeep` refutes is wasted work, and a match it misses is a lost
drop. -/

/-- Distinct unboxed variables of `e`, in `ffSoleGo`'s scalar encoding. -/
def ffUnbGo (T : FfTab p) : DenseExpr p → Nat → Nat
  | .const _, s => s
  | .var i, s =>
    if (ffTabGet T i).isSome then s
    else if s == 0 then i.index + 2 else if s == i.index + 2 then s else 1
  | .add a b, s => let s' := ffUnbGo T a s; if s' == 1 then 1 else ffUnbGo T b s'
  | .mul a b, s => let s' := ffUnbGo T a s; if s' == 1 then 1 else ffUnbGo T b s'

@[inline] def ffVarBit (v : VarId) : UInt64 := (1 : UInt64) <<< (UInt64.ofNat ((hash v).toNat % 64))

def ffBloomGo : DenseExpr p → UInt64 → UInt64
  | .const _, h => h
  | .var i, h => h ||| ffVarBit i
  | .add a b, h => ffBloomGo b (ffBloomGo a h)
  | .mul a b, h => ffBloomGo b (ffBloomGo a h)

/-- Carrier candidates for the non-syntactic arm of `denseSlotEqCert`. Every variable of the
    remainder `R = e ∖ x` needs a finite domain and `vars R ⊇ vars e ∖ {x}`, so a slot with two or
    more unboxed variables can only match syntactically, one with exactly one unboxed variable can
    only carry on it, and one with none can carry on any of its variables. -/
def ffCarriers (T : FfTab p) (e : DenseExpr p) : Option (Array VarId) :=
  let s := ffUnbGo T e 0
  if s == 1 then none else if 2 ≤ s then some #[⟨s - 2⟩] else some (ffVars e)

/-- The same as a Bloom mask, allocation-free — `0` where the slot cannot carry. -/
def ffCarBloom (T : FfTab p) (e : DenseExpr p) : UInt64 :=
  let s := ffUnbGo T e 0
  if s == 1 then 0 else if 2 ≤ s then ffVarBit ⟨s - 2⟩ else ffBloomGo e 0

/-! ### Box agreement on a register file

`keys`/`vals` replace the `List (VarId × ZMod p)` point `denseAssignments` materializes and the
association-list closure `denseEnvOfFast` evaluates through. -/

def ffSlotOf (keys : Array VarId) (i : VarId) (j : Nat) : Nat :=
  if h : j < keys.size then (if keys[j] == i then j else ffSlotOf keys i (j + 1)) else j
  termination_by keys.size - j
  decreasing_by omega

def ffEvalAt (keys : Array VarId) (vals : Array (ZMod p)) : DenseExpr p → ZMod p
  | .const n => n
  | .var i => vals.getD (ffSlotOf keys i 0) (zmodZeroP p)
  | .add a b => zmodAddP (ffEvalAt keys vals a) (ffEvalAt keys vals b)
  | .mul a b => zmodMulP (ffEvalAt keys vals a) (ffEvalAt keys vals b)

/-- Advance the odometer at digit `j`; `none` once every digit has wrapped. -/
def ffOdoStep (doms : Array (List (ZMod p))) (digits : Array Nat) (n j : Nat) :
    Option (Array Nat) :=
  if j < n then
    if digits.getD j 0 + 1 < (doms.getD j []).length then some (digits.set! j (digits.getD j 0 + 1))
    else ffOdoStep doms (digits.set! j 0) n (j + 1)
  else none
  termination_by n - j

def ffPointGo (doms : Array (List (ZMod p))) (digits : Array Nat) (n j : Nat)
    (acc : Array (ZMod p)) : Array (ZMod p) :=
  if j < n then
    ffPointGo doms digits n (j + 1)
      (acc.push ((doms.getD j []).getD (digits.getD j 0) (zmodZeroP p)))
  else acc
  termination_by n - j

/-- Do the two expressions agree at every point of the box? `fuel` bounds the point count. -/
def ffBoxAllEq (keys : Array VarId) (doms : Array (List (ZMod p))) (R R' : DenseExpr p)
    (digits : Array Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    let vals := ffPointGo doms digits keys.size 0 #[]
    if zmodIsZero (zmodAddP (ffEvalAt keys vals R) (zmodNegP (ffEvalAt keys vals R'))) then
      match ffOdoStep doms digits keys.size 0 with
      | some digits' => ffBoxAllEq keys doms R R' digits' fuel
      | none => true
    else false

/-- Collect `e`'s distinct variables with their domains, aborting at the first variable with no
    domain or once the box exceeds `cap` points. -/
def ffBoxOf (T : FfTab p) (cap : Nat) : DenseExpr p →
    Array VarId × Array (List (ZMod p)) × Nat → Option (Array VarId × Array (List (ZMod p)) × Nat)
  | .const _, st => some st
  | .var i, st =>
    if st.1.contains i then some st
    else match ffTabGet T i with
      | some dm =>
        let sz := st.2.2 * dm.length
        if sz ≤ cap then some (st.1.push i, st.2.1.push dm, sz) else none
      | none => none
  | .add a b, st => (ffBoxOf T cap a st).bind (ffBoxOf T cap b)
  | .mul a b, st => (ffBoxOf T cap a st).bind (ffBoxOf T cap b)

def ffBoxAgree (T : FfTab p) (R R' : DenseExpr p) : Bool :=
  match (ffBoxOf T 32 R (#[], #[], 1)).bind (ffBoxOf T 32 R') with
  | some (keys, doms, _) => ffBoxAllEq keys doms R R' (Array.replicate keys.size 0) 33
  | none => false

/-- Slot-pair match against precomputed carriers. -/
def ffSlotEqW (T : FfTab p) (cars : Option (Array VarId)) (e e' : DenseExpr p) : Bool :=
  e == e' ||
  (match cars with
   | none => false
   | some cs => cs.any (fun x =>
      e'.mentions x &&
      match e.splitAt x, e'.splitAt x with
      | some (k, R), some (k2, R') => k2 == k && ffBoxAgree T R R'
      | _, _ => false))

def ffSlotsEq (T : FfTab p) : List (DenseExpr p) → List (DenseExpr p) → Bool
  | [], [] => true
  | e :: r, e' :: r' => ffSlotEqW T (ffCarriers T e) e e' && ffSlotsEq T r r'
  | _, _ => false

/-- Full-message match: same bus, same constant multiplicity, pointwise-equal payloads. Slot 0's
    carriers are the sweep's index key, so they are passed in rather than rederived per pair. -/
def ffMsgEq (T : FfTab p) (cars0 : Option (Array VarId)) (m m' : ZMod p)
    (bi bi' : BusInteraction (DenseExpr p)) : Bool :=
  bi.busId == bi'.busId && m.val == m'.val &&
  (match bi.payload, bi'.payload with
   | [], [] => true
   | e :: r, e' :: r' => ffSlotEqW T cars0 e e' && ffSlotsEq T r r'
   | _, _ => false)

/-- Necessary condition for `ffMsgEq` from the per-slot signatures: every slot pair is hash-equal
    or shares a carrier candidate. Monomorphic — `Array.isEqv` applies a closure per slot. -/
def ffPreOk (ha hb ca cb : Array UInt64) (i : Nat) : Bool :=
  if h : i < ha.size then
    (ha[i] == hb.getD i 0 || (ca.getD i 0 &&& cb.getD i 0) != 0) && ffPreOk ha hb ca cb (i + 1)
  else true
  termination_by ha.size - i
  decreasing_by omega

/-- The value hash, the *rigid* hash, and the per-slot structural hashes of a payload. The rigid
    hash wildcards every slot carrying a variable and keeps the structural hash of every
    variable-free slot: a variable-free slot has no carrier, so a matching twin must agree with it
    syntactically — and its own slot is then variable-free too. Matching interactions therefore
    share the rigid hash, which is what makes it usable as an index key. -/
def ffHashes (bi : BusInteraction (DenseExpr p)) (m : ZMod p) :
    UInt64 × UInt64 × Array UInt64 := Id.run do
  let s := mixHash (hash bi.busId) (hash m.val)
  let mut vh := s
  let mut wh := s
  let mut hs : Array UInt64 := Array.emptyWithCapacity bi.payload.length
  for e in bi.payload do
    let h := e.bHash
    vh := mixHash vh h
    wh := mixHash wh (if e.hasVar then 1 else h)
    hs := hs.push h
  return (vh, wh, hs)

/-- The proposed drops, keyed by `densePdValHash`. Left to right, one verdict per *distinct value*
    — a repeat inherits its first occurrence's verdict, which is `densePdKeep`'s own scope (it
    locates its argument at the first position holding that value), so an exact duplicate is never
    proposed as a fresh drop.

    Representatives are indexed by their rigid hash together with their slot-0 hash and each slot-0
    carrier: a matching twin's slot-0 pair is value-equal or shares a carrier, so the union of the
    two probes covers every match. Carrier Blooms are filled in on first comparison — most
    interactions are never compared. -/
def ffPdSweep (bs : BusSemantics p) (T : FfTab p)
    (bis : List (BusInteraction (DenseExpr p))) :
    Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := Id.run do
  let mut drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p))) := ∅
  let mut vals : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p) × Bool)) := ∅
  let mut rBi : Array (BusInteraction (DenseExpr p)) := #[]
  let mut rM : Array (ZMod p) := #[]
  let mut rHs : Array (Array UInt64) := #[]
  let mut rCbs : Array (Option (Array UInt64)) := #[]
  let mut byHash : Std.HashMap UInt64 (List Nat) := ∅
  let mut byVar : Std.HashMap UInt64 (List Nat) := ∅
  for bi in bis do
    if !bs.isStateful bi.busId then
      match bi.multiplicity.constValue? with
      | none => pure ()
      | some m =>
        let (vh, key, hs) := ffHashes bi m
        match (vals.getD vh []).find? (fun e => e.1 == bi) with
        | some e =>
          if e.2 then
            let dk := densePdValHash bi
            drops := drops.insert dk (bi :: drops.getD dk [])
        | none =>
          let (kh, cars) := match bi.payload with
            | [] => (mixHash key 7, none)
            | e0 :: _ => (mixHash key (hs.getD 0 0), ffCarriers T e0)
          let mut myCbs : Option (Array UInt64) := none
          let mut hit := false
          let mut probe : Array (List Nat) := #[byHash.getD kh []]
          match cars with
          | none => pure ()
          | some cs => for v in cs do probe := probe.push (byVar.getD (mixHash key (hash v)) [])
          for l in probe do
            if hit then break
            for id in l do
              if hit then break
              if hs.size == (rHs.getD id #[]).size then
                if myCbs.isNone then
                  myCbs := some ((bi.payload.map (ffCarBloom T)).toArray)
                if (rCbs.getD id none).isNone then
                  rCbs := rCbs.set! id
                    (some (((rBi.getD id bi).payload.map (ffCarBloom T)).toArray))
                if ffPreOk hs (rHs.getD id #[]) (myCbs.getD #[]) ((rCbs.getD id none).getD #[]) 0 &&
                    ffMsgEq T cars m (rM.getD id m) bi (rBi.getD id bi) then
                  hit := true
          if hit then
            let dk := densePdValHash bi
            drops := drops.insert dk (bi :: drops.getD dk [])
            vals := vals.insert vh ((bi, true) :: vals.getD vh [])
          else
            vals := vals.insert vh ((bi, false) :: vals.getD vh [])
            let id := rBi.size
            rBi := rBi.push bi; rM := rM.push m; rHs := rHs.push hs; rCbs := rCbs.push myCbs
            byHash := byHash.insert kh (id :: byHash.getD kh [])
            match cars with
            | none => pure ()
            | some cs =>
              for v in cs do
                let vk := mixHash key (hash v)
                byVar := byVar.insert vk (id :: byVar.getD vk [])
  return drops

/-- Pointwise-duplicate drop: the sweep flags the drops and `densePdKeep` re-verifies each once per
    distinct proposed value. Both the re-verification and the `denseVarBucket` it reads are reached
    only when the sweep proposed something. -/
def ffPdDropWith (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) :
    DenseConstraintSystem p :=
  if drops.isEmpty then d
  else
    let domIdx := denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints)
    let verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) //
        densePdKeep bs domIdx d.busInteractions b = false }) :=
      drops.fold (init := ∅) fun m h l =>
        m.insert h (l.eraseDups.filterMap (fun b =>
          if hpd : densePdKeep bs domIdx d.busInteractions b = false
          then some ⟨b, hpd⟩ else none))
    d.filterBus (densePdVerdictKeep verdicts)

@[inline] def ffPdDropF (bs : BusSemantics p) (T : FfTab p) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  ffPdDropWith bs d (ffPdSweep bs T d.busInteractions)

/-! ## The fused transform -/

/-- `flagFold`: substitute entailed nonlinear interpolations (A), rewrite over-bound survivors
    multilinearly (B), drop box tautologies (C), drop pointwise stateless-check duplicates (D).
    The finite-domain table is built once — twice only when part B is reached, which changes what
    the single-variable domain sources are. Prime `p` only (re-checked inside each part); identity
    otherwise. -/
def denseFlagFoldF (pw : PrimeWitness p) (b : DegreeBound) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let d1 := denseFxSubstF pw bs facts d
    let d2 := if ffAnyOverBound b d1
      then d1.boxRewriteWith (ffTabGet (ffTabOf (ffBucketsOf d1.algebraicConstraints))) b
      else d1
    let T := ffTabOf (ffBucketsOf d2.algebraicConstraints)
    ffPdDropF bs T (d2.ffBoxTauto T)
  else d

end ApcOptimizer.Dense
