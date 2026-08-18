import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.**

    The assumptions made are:

    * `hLegal`: every chip in the original guest is legal for OpenVM.
    * `hPreserve`: the optimizer preserves legality.
    * `hBudget` prevents *multiplicity* wrapping: `maxInteractions` bus interactions across
      `maxInstances` instances must not overflow — with one unit of headroom to spare beyond
      that product, which memory finalization's derivation (rather than assumption) of its own
      byte invariant spends (`Realizes.lean`'s `guestNet_add_ne_zero_of_uniform`).
    * `hWindow` prevents *timestamp* wrapping: a run of `maxInstances`
      instructions, each advancing the clock by less than `maxWindow`
      (`Circuit.advancesClock`), must not overflow.
    * `hSize`: `maxInteractions` is respected
    * `hSound`: each per-chip replacement is sound

    The most important assumption to audit is `hLegal` and `hPreserve`.

    * for `hLegal`, we need to believe that OpenVM's instructions meet it
    * for `hPreserve`, we need to prove that the optimizer preserves legality

    **How much of that is genuinely new work** (`Audit/SoundnessGivesLegality.lean`): OpenVM's
    `maintainsInvariants` already pins a message's multiplicity (`= 1` on every lookup bus, `= ±1`
    on the execution bridge and memory) and carries `openVmPayloadOk` on memory, and
    `Circuit.isSoundReplacementOf`'s second conjunct transports it. So a pass that proves `hSound`
    for a chip that guarantees the bus invariants already delivers all three bus-shape clauses of
    `Circuit.legalGuest` — but only on assignments the semantics *accepts*
    (`legalOnAccepted_of_isSoundReplacementOf`). What remains is:

    * those three clauses on assignments that are algebraically satisfying but not accepted —
      which is where the VM-level argument consumes them, since `statelessAccepted_of_sinks` and
      `maintains_of_stateful_active` are what *derive* acceptance
      (`legalOnAccepted_not_statelessSendOnly` shows the gap is real, not an artefact); and
    * all of `Circuit.advancesClock`, which has no counterpart in `Spec.lean` at all.

    Both `hLegal` and `hPreserve` are used only to build one list — every chip of `G ++ G'` is
    legal (`vmSoundReplacement_of_forall₂`) — and that list is consumed only by
    `Host.forcesAccepts`, over whichever mixed list an intermediate substitution step is running.
    Since `hPreserve` is applied exactly once, to `hLegal`, the pair is interchangeable with
    assuming `G'` legal outright; the `PreservesLegality` phrasing records an obligation on the
    optimizer rather than an assumption on its output.

    -/
theorem openVm_vmSoundReplacement [Fact p.Prime]
    {maxInstances ptrReg countReg maxWindow maxInteractions : ℕ} {G G' : Guest p}
    -- TODO(AO): add a vm here (depending on sizes); this removes size bounds below
    -- TODO(AO): we'll have to closely audit these conditions
    (hLegal : ∀ c ∈ G,
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) (openVmRank openVmMemBusId) openVmRankBound maxWindow)
    -- TODO(AO): we'll have to prove this
    -- AG: many questions about legality. At the very least, we just need to assume that G' is legal
    -- AG: since at this stage G and G' are not related, preserving legality doesn't have a separate meaning.
    (hPreserve : PreservesLegality (openVmHost maxInstances ptrReg countReg maxWindow) G G')
    (hWindow : (maxInstances + 1) * (maxWindow + 1) < p)
    (hSize : ∀ c ∈ G ++ G', c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * maxInstances + 1 < p)
    -- NB: isSoundReplacementOf must, but does not, depend on some size bounds
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost maxInstances ptrReg countReg maxWindow) G G' :=
    -- proof below
  vmSoundReplacement_of_forall₂ (openVmHost_realizes maxInstances ptrReg countReg maxWindow
      (openVmHost_pinsRanks maxInstances ptrReg countReg maxWindow hWindow))
    hLegal hPreserve hSize hBudget hSound

end ApcOptimizer.OpenVM
