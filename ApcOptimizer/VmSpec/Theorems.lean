import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.**

    The assumptions made are:

    * `hLegal`: every chip of `G ++ G'` — the optimizer's input *and* its output — is legal for
      the VM `P` configures.
    * `hSound`: each per-chip replacement is sound

    -/
theorem openVm_vmSoundReplacement [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    -- TODO(AO): we'll have to prove the `G'` half of this, probably by absorbing an additional
    -- implication into `Circuit.isSoundReplacementOf`.
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId)
        openVmRankBound P.maxWindow P.maxInteractions)
    -- NB: isSoundReplacementOf must, but does not, depend on some size bounds, since legality does.
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  vmSoundReplacement_of_forall₂ (openVmHost_realizes P (openVmHost_pinsRanks P)) hLegal hSound

end ApcOptimizer.OpenVM
