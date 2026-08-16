import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.**

    The assumptions made are:

    * `hLegal`: every chip in the original guest is legal for OpenVM.
    * `hPreserve`: the optimizer preserves legality.
    * `hBudget` prevents *multiplicity* wrapping: `maxInteractions` bus interactions across
      `maxInstances` instances must not overflow.
    * `hWindow` prevents *timestamp* wrapping: a run of `maxInstances`
      instructions, each advancing the clock by less than `maxWindow`
      (`Circuit.advancesClock`), must not overflow.
    * `hSize`: `maxInteractions` is respected
    * `hSound`: each per-chip replacement is sound

    The most important assumption to audit is `hLegal` and `hPreserve`.

    * for `hLegal`, we need to believe that OpenVM's instructions meet it
    * for `hPreserve`, we need to prove that the optimizer preserves legality

    -/
theorem openVm_vmSoundReplacement [Fact p.Prime]
    {maxInstances ptrReg countReg maxWindow maxInteractions : ℕ} {G G' : Guest p}
    (hLegal : ∀ c ∈ G,
      c.legalGuest (openVmGuestRules defaultBusMap) (openVmRank 1) openVmRankBound ∧
        Circuit.advancesClock c 0 1 maxWindow)
    (hPreserve : PreservesLegality (openVmHost maxInstances ptrReg countReg maxWindow 1) G G')
    (hWindow : (maxInstances + 1) * (maxWindow + 1) < p)
    (hSize : ∀ c ∈ G ++ G', c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * maxInstances < p)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost maxInstances ptrReg countReg maxWindow 1) G G' :=
    -- proof below
  vmSoundReplacement_of_forall₂ (openVmHost_realizes maxInstances ptrReg countReg maxWindow
      (openVmHost_pinsRanks maxInstances ptrReg countReg maxWindow hWindow))
    hLegal hPreserve hSize hBudget hSound

end ApcOptimizer.OpenVM
