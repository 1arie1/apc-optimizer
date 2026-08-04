import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense pass results, composition, degree guard, and fixpoint

Implementation-only dense analogue of the `VerifiedPass`/`PassResult` framework: a dense pass maps
a registry + covered dense system to an extended registry, dense output, and dense derivations,
bundled with an extension proof, coverage, and a `PassCorrect` on the decoded systems. Composition
threads the registry and concatenates derivations; the degree guard and fixpoint use the dense
measures (`Measure.lean`), which equal the spec measures on the decode. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

theorem DenseComputationMethod.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r')
    {cm : DenseComputationMethod p} (hc : cm.CoveredBy r) : cm.CoveredBy r' := by
  induction cm with
  | const c => exact True.intro
  | quotientOrZero num den =>
      exact ⟨hc.1.mono h, hc.2.mono h⟩
  | ifEqZero cond thenM elseM iht ihe =>
      exact ⟨hc.1.mono h, iht hc.2.1, ihe hc.2.2⟩

theorem DenseDerivations.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r')
    {dd : DenseDerivations p} (hc : dd.CoveredBy r) : dd.CoveredBy r' :=
  fun x hx => ⟨h.valid (hc x hx).1, (hc x hx).2.mono h⟩

theorem DenseDerivations.coveredBy_append {r : VarRegistry} {a b : DenseDerivations p}
    (ha : a.CoveredBy r) (hb : b.CoveredBy r) : (a ++ b).CoveredBy r := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

/-- The result of a dense pass: extended registry, dense output and derivations, with extension,
    coverage, and `PassCorrect`-on-decode evidence (all `Prop`, erased at runtime). -/
structure DensePassResult (reg : VarRegistry) (d : DenseConstraintSystem p) (bs : BusSemantics p) where
  reg' : VarRegistry
  out : DenseConstraintSystem p
  derivs : DenseDerivations p
  ext : reg.Extends reg'
  covered : out.CoveredBy reg'
  dcovered : derivs.CoveredBy reg'
  correct : PassCorrect (reg.decodeCS d) (reg'.decodeCS out) (reg'.decodeDerivs derivs) bs

/-- A proof-carrying dense pass that may consult proven `BusFacts`. Takes the input coverage as an
    (erased) hypothesis so the framework can thread it through composition. -/
abbrev DenseVerifiedPassW (p : ℕ) :=
  (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
    (bs : BusSemantics p) → (facts : BusFacts p bs) → DensePassResult reg d bs

/-- Sequential composition: run `f`, then `g` on its output; concatenate dense derivations (the
    `PassCorrect`s compose via registry-stability). -/
def DenseVerifiedPassW.andThen (f g : DenseVerifiedPassW p) : DenseVerifiedPassW p :=
  fun reg d hcov bs facts =>
    let r1 := f reg d hcov bs facts
    let r2 := g r1.reg' r1.out r1.covered bs facts
    { reg' := r2.reg'
      out := r2.out
      derivs := r1.derivs ++ r2.derivs
      ext := r1.ext.trans r2.ext
      covered := r2.covered
      dcovered := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono r2.ext r1.dcovered) r2.dcovered
      correct := by
        have h := r1.correct.andThen r2.correct
        rwa [r2.reg'.decodeDerivs_append, r2.ext.decodeDerivs_eq r1.dcovered] }

/-! ## Degree guarding

The guard runs after every pass of every stage list, ~200–290 times per run, and `withinDegreeB` is
a whole-system AST walk. Most of what it walks it has already accepted, so a *guarded* pass carries
a `DenseDegCert` — an erased proof that its input is within bound, `none` if unknown — which lets
`degOkFrom` (`Measure.lean`) skip the items the output shares with its input. The certificate is
produced by the guard itself, so it establishes itself on the first invocation of a stage; the
optimizer's input circuit is not assumed to be within bound. -/

/-- A dense pass never pushes a within-bound decoded system past the degree bound `b`. -/
def DenseRespectsDeg (b : DegreeBound) (f : DenseVerifiedPassW p) : Prop :=
  ∀ (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (bs : BusSemantics p) (facts : BusFacts p bs),
    (reg.decodeCS d).withinDegree b →
    ((f reg d hcov bs facts).reg'.decodeCS (f reg d hcov bs facts).out).withinDegree b

/-- An erased certificate that `d` is within bound `b`; `none` means "not known here". -/
abbrev DenseDegCert (b : DegreeBound) (d : DenseConstraintSystem p) : Type :=
  Option (PLift (d.withinDegreeB b = true))

/-- The degree check, served from the input's certificate when there is one
    (`denseDegCheck_eq`: the value never depends on which). -/
def denseDegCheck (b : DegreeBound) (d out : DenseConstraintSystem p) (hd : DenseDegCert b d) :
    Bool :=
  match hd with
  | none => out.withinDegreeB b
  | some h => d.degOkFrom b out h.down

theorem denseDegCheck_eq {b : DegreeBound} {d out : DenseConstraintSystem p}
    {hd : DenseDegCert b d} : denseDegCheck b d out hd = out.withinDegreeB b := by
  cases hd with
  | none => rfl
  | some h => exact d.degOkFrom_eq b out h.down

/-- A pass result together with a certificate for its output. -/
structure DenseGuardedResult (b : DegreeBound) (reg : VarRegistry) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) where
  res : DensePassResult reg d bs
  cert : DenseDegCert b res.out

/-- A degree-guarded dense pass: threads the certificate alongside the system. -/
abbrev DenseGuardedPassW (p : ℕ) (b : DegreeBound) :=
  (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg → DenseDegCert b d →
    (bs : BusSemantics p) → (facts : BusFacts p bs) → DenseGuardedResult b reg d bs

/-- Degree guard on the dense system (no decode): if the output would exceed `b`, keep the input.
    The dense check equals the spec check (`decodeCS_withinDegreeB`). -/
def DenseVerifiedPassW.guardDegree (b : DegreeBound) (f : DenseVerifiedPassW p) :
    DenseGuardedPassW p b :=
  fun reg d hcov hd bs facts =>
    let r := f reg d hcov bs facts
    if hok : denseDegCheck b d r.out hd = true then
      ⟨r, some ⟨denseDegCheck_eq ▸ hok⟩⟩
    else
      ⟨{ reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg,
         covered := hcov, dcovered := by intro x hx; simp at hx,
         correct := PassCorrect.refl (reg.decodeCS d) bs }, hd⟩

/-- Forget the certificate: run the guarded pass with no knowledge about its input. -/
def DenseGuardedPassW.toPass {b : DegreeBound} (g : DenseGuardedPassW p b) : DenseVerifiedPassW p :=
  fun reg d hcov bs facts => (g reg d hcov none bs facts).res

/-- `DenseRespectsDeg` for a guarded pass, for every input certificate. -/
def DenseGuardedRespectsDeg (b : DegreeBound) (g : DenseGuardedPassW p b) : Prop :=
  ∀ (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (hd : DenseDegCert b d) (bs : BusSemantics p) (facts : BusFacts p bs),
    (reg.decodeCS d).withinDegree b →
    ((g reg d hcov hd bs facts).res.reg'.decodeCS
      (g reg d hcov hd bs facts).res.out).withinDegree b

theorem DenseGuardedPassW.toPass_respectsDeg {b : DegreeBound} {g : DenseGuardedPassW p b}
    (h : DenseGuardedRespectsDeg b g) : DenseRespectsDeg b g.toPass :=
  fun reg d hcov bs facts hin => h reg d hcov none bs facts hin

theorem DenseVerifiedPassW.guardDegree_respectsDeg {b : DegreeBound} (f : DenseVerifiedPassW p) :
    DenseGuardedRespectsDeg b (f.guardDegree b) := by
  intro reg d hcov hd bs facts hin
  simp only [DenseVerifiedPassW.guardDegree]
  by_cases hok : denseDegCheck b d (f reg d hcov bs facts).out hd = true
  · rw [dif_pos hok]
    refine (Circuit.withinDegreeB_iff _ _).1 ?_
    rw [(f reg d hcov bs facts).reg'.decodeCS_withinDegreeB]
    exact denseDegCheck_eq ▸ hok
  · rw [dif_neg hok]
    exact hin

/-- Guarded sequential composition: `DenseVerifiedPassW.andThen` with the certificate threaded from
    `f`'s output into `g`'s input, so only the first pass of a chain pays a full walk. -/
def DenseGuardedPassW.andThen {b : DegreeBound} (f g : DenseGuardedPassW p b) :
    DenseGuardedPassW p b :=
  fun reg d hcov hd bs facts =>
    let r1 := f reg d hcov hd bs facts
    let r2 := g r1.res.reg' r1.res.out r1.res.covered r1.cert bs facts
    ⟨{ reg' := r2.res.reg'
       out := r2.res.out
       derivs := r1.res.derivs ++ r2.res.derivs
       ext := r1.res.ext.trans r2.res.ext
       covered := r2.res.covered
       dcovered := DenseDerivations.coveredBy_append
         (DenseDerivations.CoveredBy.mono r2.res.ext r1.res.dcovered) r2.res.dcovered
       correct := by
         have h := r1.res.correct.andThen r2.res.correct
         rwa [r2.res.reg'.decodeDerivs_append, r2.res.ext.decodeDerivs_eq r1.res.dcovered] },
     r2.cert⟩

def DenseGuardedPassW.id {b : DegreeBound} : DenseGuardedPassW p b :=
  fun reg d hcov hd bs _ =>
    ⟨{ reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg, covered := hcov,
       dcovered := by intro x hx; simp at hx,
       correct := PassCorrect.refl (reg.decodeCS d) bs }, hd⟩

/-- Fold a list of guarded dense passes into one (left to right; identity on `[]`). -/
def denseGuardedChain {b : DegreeBound} (l : List (DenseGuardedPassW p b)) :
    DenseGuardedPassW p b :=
  l.foldl DenseGuardedPassW.andThen DenseGuardedPassW.id

theorem DenseGuardedPassW.andThen_respectsDeg {b : DegreeBound} {f g : DenseGuardedPassW p b}
    (hf : DenseGuardedRespectsDeg b f) (hg : DenseGuardedRespectsDeg b g) :
    DenseGuardedRespectsDeg b (f.andThen g) := by
  intro reg d hcov hd bs facts hin
  exact hg _ _ _ _ bs facts (hf reg d hcov hd bs facts hin)

theorem DenseVerifiedPassW.andThen_respectsDeg {b : DegreeBound} {f g : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) (hg : DenseRespectsDeg b g) : DenseRespectsDeg b (f.andThen g) := by
  intro reg d hcov bs facts hin
  exact hg _ _ _ bs facts (hf reg d hcov bs facts hin)

theorem denseGuardedChain_respectsDeg {b : DegreeBound} {l : List (DenseGuardedPassW p b)}
    (h : ∀ f ∈ l, DenseGuardedRespectsDeg b f) :
    DenseGuardedRespectsDeg b (denseGuardedChain l) := by
  unfold denseGuardedChain
  suffices H : ∀ (l : List (DenseGuardedPassW p b)) (init : DenseGuardedPassW p b),
      DenseGuardedRespectsDeg b init → (∀ f ∈ l, DenseGuardedRespectsDeg b f) →
      DenseGuardedRespectsDeg b (l.foldl DenseGuardedPassW.andThen init) by
    exact H l DenseGuardedPassW.id (fun _ _ _ _ _ _ h => h) h
  intro l
  induction l with
  | nil => intro init hinit _; simpa using hinit
  | cons g rest ih =>
      intro init hinit hall
      rw [List.foldl_cons]
      exact ih (init.andThen g)
        (DenseGuardedPassW.andThen_respectsDeg hinit (hall g (List.mem_cons_self ..)))
        (fun f hf => hall f (List.mem_cons_of_mem _ hf))

/-! ## Dense fixpoint

The dense size key is well-founded, so iterating to a fixpoint terminates with no budget. Because
it equals the spec size key on the decode, the stopping decision matches the spec loop's. -/

theorem denseSizeKey_wf :
    WellFounded (fun a b : DenseConstraintSystem p => a.sizeKey < b.sizeKey) :=
  InvImage.wf DenseConstraintSystem.sizeKey wellFounded_lt

/-- The dense fixpoint worker. `_hk` threads in the input's already-computed size key so each cycle
    only recomputes the output's. Correct by construction. -/
def denseIterateToFixpointFrom (f : DenseVerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) (k : Nat ×ₗ Nat ×ₗ Nat) (_hk : d.sizeKey = k) :
    DensePassResult reg d bs :=
  let r := f reg d hcov bs facts
  let k' := r.out.sizeKey
  if h : k' < k then
    let r2 := denseIterateToFixpointFrom f r.reg' r.out r.covered bs facts k' rfl
    { reg' := r2.reg'
      out := r2.out
      derivs := r.derivs ++ r2.derivs
      ext := r.ext.trans r2.ext
      covered := r2.covered
      dcovered := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono r2.ext r.dcovered) r2.dcovered
      correct := by
        have hc := r.correct.andThen r2.correct
        rwa [r2.reg'.decodeDerivs_append, r2.ext.decodeDerivs_eq r.dcovered] }
  else
    { reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg, covered := hcov,
      dcovered := by intro x hx; simp at hx,
      correct := PassCorrect.refl (reg.decodeCS d) bs }
  termination_by d.sizeKey
  decreasing_by rw [_hk]; exact h

/-- Iterate a dense pass to a fixpoint on the dense size key; correct by construction. -/
def denseIterateToFixpoint (f : DenseVerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) : DensePassResult reg d bs :=
  denseIterateToFixpointFrom f reg d hcov bs facts d.sizeKey rfl

/-- `denseIterateToFixpointFrom` preserves the degree bound (strong induction on the `sizeKey`
    measure, registry and threaded key generalized). -/
theorem denseIterateToFixpointFrom_respectsDeg {b : DegreeBound} {f : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) (reg : VarRegistry) (d : DenseConstraintSystem p) :
    ∀ (hcov : d.CoveredBy reg) (bs : BusSemantics p) (facts : BusFacts p bs)
      (k : Nat ×ₗ Nat ×ₗ Nat) (hk : d.sizeKey = k),
      (reg.decodeCS d).withinDegree b →
      ((denseIterateToFixpointFrom f reg d hcov bs facts k hk).reg'.decodeCS
        (denseIterateToFixpointFrom f reg d hcov bs facts k hk).out).withinDegree b := by
  induction d using denseSizeKey_wf.induction generalizing reg with
  | _ d ih =>
    intro hcov bs facts k hk hin
    rw [denseIterateToFixpointFrom]
    split
    · rename_i h
      exact ih _ (by rw [hk]; exact h) _ (f reg d hcov bs facts).covered bs facts _ rfl
        (hf reg d hcov bs facts hin)
    · exact hin

theorem denseIterateToFixpoint_respectsDeg {b : DegreeBound} {f : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) : DenseRespectsDeg b (denseIterateToFixpoint f) := by
  intro reg d hcov bs facts hin
  exact denseIterateToFixpointFrom_respectsDeg hf reg d hcov bs facts d.sizeKey rfl hin

end ApcOptimizer.Dense
