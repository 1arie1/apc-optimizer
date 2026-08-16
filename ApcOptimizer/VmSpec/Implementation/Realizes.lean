import ApcOptimizer.VmSpec.Implementation.Counting
import ApcOptimizer.VmSpec.Implementation.Rank

set_option autoImplicit false

/-! **What a host must be for its bus semantics to mean anything** — and the one thing that buys.

    `Spec.lean` treats `BusSemantics.accepts`/`maintainsInvariants` as opaque per-message
    predicates. `Host.realizes` says a concrete VM's own chips are what implement them. Every
    field is a property of the VM's fixed furniture — the `HostChip` predicates and `bs` — so it
    is checkable once per VM and holds for every optimizer run; nothing here mentions a guest
    circuit.

    What it buys is `Host.forcesAccepts`, which is **derived**, not assumed
    (`forcesAccepts_of_hostSound`): `VmSat` gives each guest instance only
    `Circuit.satisfiesAlgebraic`, whereas `Circuit.satisfies` also demands `accepts` on every
    active message, and the gap is closed by balancing.

    On stateless buses that is the manuscript's `bus_int.tex` induction: the host chips *are* the
    lookup tables, so a guest's active message has nowhere to go but into a chip that only
    receives table entries. On stateful buses the same shape gives the manuscript's
    `eq:legal:recv_byte` (`maintains_of_stateful_active`): a guest need only vouch for what it
    *sends*, and what it *receives* is vouched for by whoever sent the same tuple. Demanding the
    receive side per-chip would be assuming something false — a chip that reads memory does not
    constrain the value it finds there. -/

variable {p : ℕ}

/-- The `GuestBusRules` a `BusSemantics` induces. **Internal**: the audited spec never uses this —
    a VM writes its rules out directly (`openVmGuestRules`) and proves them equal to this, which is
    what pins its `accepts` to the one `Circuit.satisfies` is stated against. Exactly three of
    `BusSemantics`'s four fields survive, and `maintainsInvariants` only up to the multiplicity. -/
def BusSemantics.toGuestRules (bs : BusSemantics p) : GuestBusRules p where
  isStateful := bs.isStateful
  accepts := bs.accepts
  payloadOk m := ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩

/-- On a stateful bus, acceptance follows from the payload being good — which is the contract
    `GuestBusRules.payloadOk` is named for, now stated directly rather than through a message whose
    multiplicity has to be quantified away.

    This is what lets a receive inherit its acceptance from whoever sent the same tuple. For
    OpenVM it holds by inspection: memory `accepts` asks that received data in a byte-checked
    address space be bytes, and memory `maintainsInvariants` asks exactly that of any message. -/
def BusSemantics.statefulAcceptsOfPayloadOk (bs : BusSemantics p) : Prop :=
  ∀ msg : BusInteraction (ZMod p), bs.isStateful msg.busId = true →
    bs.toGuestRules.payloadOk (msg.busId, msg.payload) → bs.accepts msg

/-- `Host.statefulChipsMaintain` still speaks of a whole message; this is the one-line bridge to
    `GuestBusRules.payloadOk`, which forgets its multiplicity. -/
theorem payloadOk_of_exists {bs : BusSemantics p} {m : BusMessage p}
    (h : ∃ msg : BusInteraction (ZMod p), msg.busId = m.1 ∧ msg.payload = m.2 ∧
      bs.maintainsInvariants msg) : bs.toGuestRules.payloadOk m := by
  obtain ⟨msg, h1, h2, h3⟩ := h
  exact ⟨msg.multiplicity, by cases msg; cases h1; cases h2; exact h3⟩

/-- The host's stateless chips are lookup tables: any stateless message they leave with a nonzero
    net multiplicity is one the semantics accepts. This is the manuscript's "table sink"
    (`bus_int.tex`), which implements its bus's predicate. -/
def Host.sinksAreTables (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ m : BusMessage p, bs.isStateful m.1 = false → hA.busEffect m ≠ 0 →
      ∀ mult : ZMod p, mult ≠ 0 → bs.accepts ⟨m.1, mult, m.2⟩

/-- Every stateful message a host chip touches carries a payload that maintains the bus
    invariants.

    Unlike the guest-side condition this covers receives too, and that is a genuine modelling
    assumption about the host — memory finalization reads whatever the run left behind. It is
    assumption in the right place, though: these chips are the VM's own fixed furniture, not
    something the optimizer produces, so the claim is inspectable once and for all against the
    `HostChip` predicates rather than being asserted about an optimizer's output. -/
def Host.statefulChipsMaintain (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ (t : Fin host.chips.length), ∀ c ∈ hA t, ∀ m : BusMessage p,
      bs.isStateful m.1 = true → c m ≠ 0 →
        ∃ msg : BusInteraction (ZMod p), msg.busId = m.1 ∧ msg.payload = m.2 ∧
          bs.maintainsInvariants msg

/-- The host can re-balance a stateless change: given a legal host assignment and a `δ` supported
    on stateless messages the semantics accepts, some legal host assignment nets exactly `δ` more,
    **leaving the input and output chips alone**.

    Lookup host chips are free in exactly this way — their legality predicate constrains *which*
    payloads may carry a nonzero net multiplicity, not what that multiplicity is — and they are
    not `HostChip.singleton`, so their instance count is free too. The input/output clauses are
    what make the observed effect survive the rebuild.

    Note what this does *not* permit: the input and output chips are pinned, so the observed
    `VmEffect` is carried across untouched. -/
def Host.absorbsStateless (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ δ : BusState p,
      (∀ m : BusMessage p, δ m ≠ 0 →
        bs.isStateful m.1 = false ∧
          ∃ mult : ZMod p, mult ≠ 0 ∧ bs.accepts ⟨m.1, mult, m.2⟩) →
      ∃ hA' : HostAssignment p host, hA'.satisfies ∧ hA'.busEffect = hA.busEffect + δ ∧
        hA' host.inputChip = hA host.inputChip ∧
        hA' host.outputChip = hA host.outputChip

/-- **The host keeps its runs inside the rank window.** A claim about the VM, not about any guest
    circuit: whatever *legal* chips it is running, a satisfying assignment within the trace budget
    has every guest instance's stateful traffic below `rm.bound`.

    The hypotheses are exactly `Host.forcesAccepts`'s, and they are not decoration — without them
    the statement is false. A chip whose only traffic is a self-cancelling memory send/receive pair
    at some huge timestamp balances, satisfies `VmSat`, and violates the conclusion; legality is
    what excludes it, and the trace budget is what stops a run from wrapping `ZMod p` by sheer
    length.

    For OpenVM this is proved: `openVmHost_pinsRanks`, by walking the execution bridge
    (`Chain.lean`). Each instance advances the bridge by a bounded positive amount
    (`Circuit.advancesClock`), so a cycle among the instances would have to sum to zero over a
    total the budget keeps strictly between `0` and `p`; the connector — carrying OpenVM's range
    check as `ConnectorBoundary.finalTimestampBounded` — is therefore the only place a chain can
    start, and one checked timestamp bounds the whole run. -/
def Host.pinsRanks (host : Host p) (rm : RankModel p) : Prop :=
  ∀ (G : Guest p) (maxInteractions : ℕ),
    (∀ c ∈ G, host.legalGuest c) →
    (∀ c ∈ G, c.busInteractions.length ≤ maxInteractions) →
    maxInteractions * host.maxInstances < p →
    ∀ (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a → a.withinRankBound rm

/-- **A host realizes its bus semantics.** The single hypothesis the connecting theorems need of
    the fixed VM; see the module docstring. (The lemmas below still take the individual fields, so
    which one carries which step stays visible.) -/
structure Host.realizes (host : Host p) (bs : BusSemantics p) (rm : RankModel p) : Prop where
  /-- The host's `Host.legalGuest` field is at least `Circuit.legalGuest` for `bs`, at this
      argument's own `rm.rank` and `rm.bound`. -/
  legalGuest : ∀ c : Circuit p,
    host.legalGuest c → c.legalGuest bs.toGuestRules rm.rank rm.bound
  sinksAreTables : host.sinksAreTables bs
  statefulChipsMaintain : host.statefulChipsMaintain bs
  statefulAcceptsOfPayloadOk : bs.statefulAcceptsOfPayloadOk
  absorbsStateless : host.absorbsStateless bs
  pinsRanks : host.pinsRanks rm

/-- The host chips realize `bs`'s acceptance: in any satisfying VM built on this host whose guest
    chips are small enough not to wrap `ZMod p`, every guest instance's assignment is
    `Circuit.satisfies`-good, not merely algebraically consistent.

    Every chip in `G` must be one the host will run: the balancing argument is over the whole
    list, so one illegal chip anywhere on a bus breaks it. `maxInteractions` bounds each chip's
    bus-interaction count; `maxInteractions * host.maxInstances < p` is the anti-wraparound
    condition (see `Counting.lean`).

    Proved from `Host.realizes` — see `forcesAccepts_of_hostSound`. -/
def Host.forcesAccepts (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ (G : Guest p) (maxInteractions : ℕ),
    (∀ c ∈ G, host.legalGuest c) →
    (∀ c ∈ G, c.busInteractions.length ≤ maxInteractions) →
    maxInteractions * host.maxInstances < p →
    ∀ (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a →
      ∀ (t : Fin G.length), ∀ asg ∈ a.guestAssignments t, (G.get t).satisfies bs asg


/-- **A guest instance's lookups all hold**, in any satisfying run. This is the manuscript's
    `bus_int.tex` induction on the stateless buses: the host chips *are* the lookup tables, so an
    actively-sent stateless message has nowhere to go but into a chip that only receives table
    entries.

    Nothing stateful takes part — only `Circuit.statelessSendOnly`, `Host.sinksAreTables`, bus
    balance and the trace budget — which is what makes it safe to hand to
    `Circuit.statefulSendsMaintain`, whose own derivation depends on it. -/
theorem statelessAccepted_of_sinks [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p}
    {G : Guest p} {maxInteractions : ℕ} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest bs.toGuestRules rm.rank rm.bound)
    (hsinks : host.sinksAreTables bs) (hGuests : ∀ c ∈ G, host.legalGuest c)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances < p) (hsat : VmSat ⟨host, G⟩ a)
    (t : Fin G.length) (asg : ChipAssignment p) (hasg : asg ∈ a.guestAssignments t) :
    (G.get t).statelessAccepted bs.toGuestRules asg := by
  have hlegal : ∀ s : Fin G.length, (G.get s).legalGuest bs.toGuestRules rm.rank rm.bound :=
    fun s => hunpack _ (hGuests _ (List.get_mem G s))
  intro bi hbi hst hmult
  have hm : bs.isStateful ((bi.eval asg).busId, (bi.eval asg).payload).1 = false := hst
  have huni : ∀ s : Fin G.length, ∀ asg' ∈ a.guestAssignments s,
      (G.get s).uniformAt asg' ((bi.eval asg).busId, (bi.eval asg).payload) 1 := by
    intro s asg' hasg' bi' hbi' hmsg'
    refine (hlegal s).sendOnly asg' (hsat.satisfiesGuest s asg' hasg') bi' hbi' ?_
    rw [show bi'.busId = (bi.eval asg).busId from congrArg Prod.fst hmsg']
    exact hst
  have hguest :=
    guestNet_ne_zero_of_uniform hsat hSize hBudget one_ne_zero huni hasg hbi rfl hmult
  have hbal := hsat.balances ((bi.eval asg).busId, (bi.eval asg).payload)
  have hhost : a.hostAssignment.busEffect ((bi.eval asg).busId, (bi.eval asg).payload) ≠ 0 := by
    intro h
    exact hguest (by rw [busEffect_apply, h, add_zero] at hbal; exact hbal)
  exact hsinks a.hostAssignment (hsat.satisfiesHost) _ hm hhost (bi.eval asg).multiplicity hmult

/-- **The stateful analogue of the manuscript's stateless induction — its `eq:legal:recv_byte`.**
    In a satisfying VM, every stateful message a guest instance actively touches carries a payload
    that maintains the bus invariants.

    For a *send* that is the chip's own obligation (`Circuit.statefulSendsMaintain`). For a
    *receive* it is forced by balancing: if nothing carrying that payload maintained the
    invariants then no guest sent it and no host chip touched it, leaving a pile of receives that
    cannot sum to zero — which is where the trace budget is needed again, since `p` receives
    would.

    The whole thing is a strong induction on `rm.rank`, and it has to be: balance alone
    cannot establish the invariant, because two chips can each receive a bad payload and send
    another one, cancelling perfectly. What kills that is the rank — one of the two chips would
    have to send below the rank it received at. `Circuit.statefulSendsMaintain` may therefore lean
    on everything the same instance touched at a strictly smaller rank, which is exactly the
    induction hypothesis. -/
theorem maintains_of_stateful_active [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p}
    {G : Guest p} {maxInteractions : ℕ} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest bs.toGuestRules rm.rank rm.bound)
    (hsinks : host.sinksAreTables bs) (hstateful : host.statefulChipsMaintain bs)
    (hGuests : ∀ c ∈ G, host.legalGuest c)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances < p) (hsat : VmSat ⟨host, G⟩ a)
    (hRanks : a.withinRankBound rm)
    {t : Fin G.length} {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ (G.get t).busInteractions)
    (hst : bs.isStateful bi.busId = true) (hmult : (bi.eval asg).multiplicity ≠ 0) :
    bs.toGuestRules.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload) := by
  have hlegal : ∀ s : Fin G.length, (G.get s).legalGuest bs.toGuestRules rm.rank rm.bound :=
    fun s => hunpack _ (hGuests _ (List.get_mem G s))
  suffices key : ∀ r : ℕ, ∀ (s : Fin G.length) (asg' : ChipAssignment p),
      asg' ∈ a.guestAssignments s → ∀ bi' ∈ (G.get s).busInteractions,
      bs.isStateful bi'.busId = true → (bi'.eval asg').multiplicity ≠ 0 →
      rm.rank ((bi'.eval asg').busId, (bi'.eval asg').payload) = r →
      bs.toGuestRules.payloadOk ((bi'.eval asg').busId, (bi'.eval asg').payload) by
    exact key _ t asg hasg bi hbi hst hmult rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s asg' hasg' bi' hbi' hst' hmult' hrank
  by_contra hcon
  -- The payload is not good.
  have hno : ¬ bs.toGuestRules.payloadOk ((bi'.eval asg').busId, (bi'.eval asg').payload) := hcon
  -- Hence no guest *sends* it, so every guest multiplicity at this message is `0` or `-1`.
  have huni : ∀ u : Fin G.length, ∀ asg'' ∈ a.guestAssignments u,
      (G.get u).uniformAt asg'' ((bi'.eval asg').busId, (bi'.eval asg').payload) (-1) := by
    intro u asg'' hasg'' bi'' hbi'' hmsg''
    have hbus : bi''.busId = (bi'.eval asg').busId := congrArg Prod.fst hmsg''
    have hst'' : bs.isStateful bi''.busId = true := by rw [hbus]; exact hst'
    rcases (hlegal u).polarity asg'' (hsat.satisfiesGuest u asg'' hasg'') bi'' hbi'' hst'' with
      h0 | h1 | hm1
    · exact Or.inl h0
    · -- A send has to vouch for itself, given everything it touched at a lower rank — which the
      -- induction hypothesis supplies.
      have hlow : (G.get u).lowerRanksMaintain bs.toGuestRules rm.rank asg''
          (rm.rank ((bi''.eval asg'').busId, (bi''.eval asg'').payload)) := by
        intro bj hbj hstj hmultj hlt
        rw [hmsg'', hrank] at hlt
        exact ih _ hlt u asg'' hasg'' bj hbj hstj hmultj rfl
      have hacc : (G.get u).statelessAccepted bs.toGuestRules asg'' :=
        statelessAccepted_of_sinks hunpack hsinks hGuests hSize hBudget hsat u asg'' hasg''
      exact absurd (hmsg'' ▸ (hlegal u).sendsMaintain asg''
          (hsat.satisfiesGuest u asg'' hasg'') hacc (hRanks u asg'' hasg'') bi'' hbi'' hst'' h1
          hlow) hno
    · exact Or.inr hm1
  -- And no host chip touches it either.
  have hhost : a.hostAssignment.busEffect ((bi'.eval asg').busId, (bi'.eval asg').payload) = 0 := by
    refine hostNet_eq_zero_of_all_zero (fun u c hc => ?_)
    by_contra hcm
    exact hno (payloadOk_of_exists
      (hstateful a.hostAssignment (hsat.satisfiesHost) u c hc _ hst' hcm))
  -- A pile of receives that cannot balance.
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  refine guestNet_ne_zero_of_uniform hsat hSize hBudget hneg huni hasg' hbi' rfl hmult' ?_
  have hbal := hsat.balances ((bi'.eval asg').busId, (bi'.eval asg').payload)
  rw [busEffect_apply, hhost, add_zero] at hbal
  exact hbal

/-- **`Host.forcesAccepts` is derivable.** Honest table sinks on the stateless buses, host chips
    that maintain the invariants on the stateful ones, bus semantics whose stateful acceptance
    follows from those invariants, and the anti-wraparound budget together give every guest
    instance the full `Circuit.satisfies` — not just its algebraic constraints, and with no
    assumption about acceptance placed on the guest chips themselves. -/
theorem forcesAccepts_of_hostSound [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest bs.toGuestRules rm.rank rm.bound)
    (hsinks : host.sinksAreTables bs) (hstateful : host.statefulChipsMaintain bs)
    (hbs : bs.statefulAcceptsOfPayloadOk) (hpins : host.pinsRanks rm) : host.forcesAccepts bs := by
  intro G maxInteractions hGuests hSize hBudget a hsat t asg hasg
  have hRanks := hpins G maxInteractions hGuests hSize hBudget a hsat
  refine ⟨hsat.satisfiesGuest t asg hasg, fun bi hbi hmult => ?_⟩
  by_cases hst : bs.isStateful bi.busId
  · exact hbs _ hst (maintains_of_stateful_active hunpack hsinks hstateful hGuests hSize hBudget
      hsat hRanks hasg hbi hst hmult)
  · exact statelessAccepted_of_sinks hunpack hsinks hGuests hSize hBudget hsat t asg hasg bi hbi
      (by simpa using hst) hmult

/-- `Host.realizes` gives `Host.forcesAccepts`. -/
theorem Host.realizes.forcesAccepts [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} (h : host.realizes bs rm) : host.forcesAccepts bs :=
  forcesAccepts_of_hostSound h.legalGuest h.sinksAreTables h.statefulChipsMaintain
    h.statefulAcceptsOfPayloadOk h.pinsRanks
