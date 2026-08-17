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
    `BusSemantics`'s four fields survive, and `maintainsInvariants` only up to the multiplicity.

    `r0` supplies the clock-facing fields (`execBusId`/`memBusId`/`getTimestamp`) that
    `BusSemantics` itself has no notion of — a template borrowed wholesale, since `Circuit.legalGuest`'s
    `sendOnly`/`polarity`/`sendsMaintain`/`payloadOk` never look at them, only `advancesClock`
    does. In practice `r0` is `openVmGuestRules`'s own value, so `openVmGuestRules_eq` gets them
    for free. -/
def BusSemantics.toGuestRules (bs : BusSemantics p) (r0 : GuestBusRules p) : GuestBusRules p where
  isStateful := bs.isStateful
  accepts := bs.accepts
  payloadOk m := ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩
  execBusId := r0.execBusId
  memBusId := r0.memBusId
  getTimestamp := r0.getTimestamp

/-- On a stateful bus, acceptance follows from the payload being good — which is the contract
    `GuestBusRules.payloadOk` is named for, now stated directly rather than through a message whose
    multiplicity has to be quantified away.

    This is what lets a receive inherit its acceptance from whoever sent the same tuple. For
    OpenVM it holds by inspection: memory `accepts` asks that received data in a byte-checked
    address space be bytes, and memory `maintainsInvariants` asks exactly that of any message. -/
def BusSemantics.statefulAcceptsOfPayloadOk (bs : BusSemantics p) (r0 : GuestBusRules p) : Prop :=
  ∀ msg : BusInteraction (ZMod p), bs.isStateful msg.busId = true →
    (bs.toGuestRules r0).payloadOk (msg.busId, msg.payload) → bs.accepts msg

/-- `Host.statefulChipsMaintain` still speaks of a whole message; this is the one-line bridge to
    `GuestBusRules.payloadOk`, which forgets its multiplicity. -/
theorem payloadOk_of_exists {bs : BusSemantics p} {r0 : GuestBusRules p} {m : BusMessage p}
    (h : ∃ msg : BusInteraction (ZMod p), msg.busId = m.1 ∧ msg.payload = m.2 ∧
      bs.maintainsInvariants msg) : (bs.toGuestRules r0).payloadOk m := by
  obtain ⟨msg, h1, h2, h3⟩ := h
  exact ⟨msg.multiplicity, by cases msg; cases h1; cases h2; exact h3⟩

/-- The host's stateless chips are lookup tables: any stateless message they leave with a nonzero
    net multiplicity is one the semantics accepts. This is the manuscript's "table sink"
    (`bus_int.tex`), which implements its bus's predicate. -/
def Host.sinksAreTables (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ m : BusMessage p, bs.isStateful m.1 = false → hA.busEffect m ≠ 0 →
      ∀ mult : ZMod p, mult ≠ 0 → bs.accepts ⟨m.1, mult, m.2⟩

/-- Every stateful message a host chip *other than `idx`* touches carries a payload that
    maintains the bus invariants.

    This still covers receives, and for those chips it is still a genuine modelling assumption:
    these are the VM's own fixed furniture, not something the optimizer produces, so the claim is
    inspectable once and for all against the `HostChip` predicates rather than being asserted
    about an optimizer's output. `idx` is carved out because it need not be assumed at all — see
    `Host.exemptChip`. -/
def Host.statefulChipsMaintain (host : Host p) (bs : BusSemantics p)
    (idx : Fin host.chips.length) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ (t : Fin host.chips.length), t ≠ idx → ∀ c ∈ hA t, ∀ m : BusMessage p,
      bs.isStateful m.1 = true → c m ≠ 0 →
        ∃ msg : BusInteraction (ZMod p), msg.busId = m.1 ∧ msg.payload = m.2 ∧
          bs.maintainsInvariants msg

/-- A single host-chip instance whose every stateful touch is a receive (`0` or `-1`, never `1`)
    — what a chip that only ever receives (`memoryFinalizeHostChip`'s `canProduce` forces
    multiplicity `-1`) needs so `maintains_of_stateful_active` can fold it into the same
    "nobody sent this, so the receives can't balance" pigeonhole it already runs for guest
    receives, instead of assuming its payload is good outright. `-1` rather than a general `v`
    because that pigeonhole is guest polarity's own (`Circuit.statefulPolarity`), not this
    chip's to choose.

    Deliberately silent on *which* messages it touches: `canProduce` still pins that (bus id,
    address space, ...) — this only supplies the one fact the induction cannot get any other
    way. `singleton` is what caps the instance at one term in the sum, so folding it in costs the
    budget exactly one extra unit of headroom (`Counting.lean`'s
    `guestNet_add_ne_zero_of_uniform`), not an unbounded one. -/
structure Host.exemptChip (host : Host p) (bs : BusSemantics p) (idx : Fin host.chips.length) :
    Prop where
  singleton : (host.chips.get idx).singleton
  uniform : ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ c ∈ hA idx, ∀ m : BusMessage p, bs.isStateful m.1 = true → c m ≠ 0 → c m = -1

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
    which one carries which step stays visible.)

    `r0` is the clock template `bs.toGuestRules` borrows its `execBusId`/`memBusId`/`getTimestamp`
    from — in practice `openVmGuestRules`'s own value — and `maxWindow` bounds how far a guest
    instance may advance the clock (`Circuit.advancesClock`); see `Legal.lean` for why neither
    lives on `rm`. -/
structure Host.realizes (host : Host p) (bs : BusSemantics p) (rm : RankModel p)
    (r0 : GuestBusRules p) (maxWindow : ℕ) : Prop where
  /-- The host's `Host.legalGuest` field is at least `Circuit.legalGuest` for `bs`, at this
      argument's own `rm.rank` and `rm.bound`. -/
  legalGuest : ∀ c : Circuit p,
    host.legalGuest c → c.legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow
  sinksAreTables : host.sinksAreTables bs
  /-- One host-chip type is carved out and derivable instead of assumed — for `openVmHost`,
      `memoryFinalizeHostChip` (see `Host.exemptChip`). Existential rather than two separate data
      fields: a `Fin host.chips.length` cannot itself be projected back out of a `Prop`-valued
      structure, and nothing outside this file needs to name the index — every use of it is
      itself proving a `Prop`, where `obtain`ing the witness is unrestricted. -/
  statefulChipsMaintain : ∃ idx : Fin host.chips.length,
    host.exemptChip bs idx ∧ host.statefulChipsMaintain bs idx
  statefulAcceptsOfPayloadOk : bs.statefulAcceptsOfPayloadOk r0
  absorbsStateless : host.absorbsStateless bs
  pinsRanks : host.pinsRanks rm

/-- The host chips realize `bs`'s acceptance: in any satisfying VM built on this host whose guest
    chips are small enough not to wrap `ZMod p`, every guest instance's assignment is
    `Circuit.satisfies`-good, not merely algebraically consistent.

    Every chip in `G` must be one the host will run: the balancing argument is over the whole
    list, so one illegal chip anywhere on a bus breaks it. `maxInteractions` bounds each chip's
    bus-interaction count; `maxInteractions * host.maxInstances + 1 < p` is the anti-wraparound
    condition (see `Counting.lean`) — one unit more than the guest-only argument needs, because
    the exempt host chip (`Host.exemptChip`) can add one more receive to the same pile.

    Proved from `Host.realizes` — see `forcesAccepts_of_hostSound`. -/
def Host.forcesAccepts (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ (G : Guest p) (maxInteractions : ℕ),
    (∀ c ∈ G, host.legalGuest c) →
    (∀ c ∈ G, c.busInteractions.length ≤ maxInteractions) →
    maxInteractions * host.maxInstances + 1 < p →
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
    {rm : RankModel p} {r0 : GuestBusRules p} {maxWindow : ℕ}
    {G : Guest p} {maxInteractions : ℕ} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow)
    (hsinks : host.sinksAreTables bs) (hGuests : ∀ c ∈ G, host.legalGuest c)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances < p) (hsat : VmSat ⟨host, G⟩ a)
    (t : Fin G.length) (asg : ChipAssignment p) (hasg : asg ∈ a.guestAssignments t) :
    (G.get t).statelessAccepted (bs.toGuestRules r0) asg := by
  have hlegal : ∀ s : Fin G.length,
      (G.get s).legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow :=
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
    induction hypothesis.

    The one host chip `Host.exemptChip` carves out is folded into the very same pile-of-receives
    step as the guest side, rather than settled outright — it costs the one extra unit of budget
    `guestNet_add_ne_zero_of_uniform` needs. -/
theorem maintains_of_stateful_active [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p} {maxWindow : ℕ}
    {G : Guest p} {maxInteractions : ℕ} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow)
    (hsinks : host.sinksAreTables bs)
    (hstateful : ∃ idx : Fin host.chips.length,
      host.exemptChip bs idx ∧ host.statefulChipsMaintain bs idx)
    (hGuests : ∀ c ∈ G, host.legalGuest c)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances + 1 < p) (hsat : VmSat ⟨host, G⟩ a)
    (hRanks : a.withinRankBound rm)
    {t : Fin G.length} {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ (G.get t).busInteractions)
    (hst : bs.isStateful bi.busId = true) (hmult : (bi.eval asg).multiplicity ≠ 0) :
    (bs.toGuestRules r0).payloadOk ((bi.eval asg).busId, (bi.eval asg).payload) := by
  obtain ⟨idx, hexempt, hstateful⟩ := hstateful
  have hBudget' : maxInteractions * host.maxInstances < p := by omega
  have hlegal : ∀ s : Fin G.length,
      (G.get s).legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow :=
    fun s => hunpack _ (hGuests _ (List.get_mem G s))
  suffices key : ∀ r : ℕ, ∀ (s : Fin G.length) (asg' : ChipAssignment p),
      asg' ∈ a.guestAssignments s → ∀ bi' ∈ (G.get s).busInteractions,
      bs.isStateful bi'.busId = true → (bi'.eval asg').multiplicity ≠ 0 →
      rm.rank ((bi'.eval asg').busId, (bi'.eval asg').payload) = r →
      (bs.toGuestRules r0).payloadOk ((bi'.eval asg').busId, (bi'.eval asg').payload) by
    exact key _ t asg hasg bi hbi hst hmult rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s asg' hasg' bi' hbi' hst' hmult' hrank
  by_contra hcon
  -- The payload is not good.
  have hno : ¬ (bs.toGuestRules r0).payloadOk ((bi'.eval asg').busId, (bi'.eval asg').payload) :=
    hcon
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
      have hlow : (G.get u).lowerRanksMaintain (bs.toGuestRules r0) rm.rank asg''
          (rm.rank ((bi''.eval asg'').busId, (bi''.eval asg'').payload)) := by
        intro bj hbj hstj hmultj hlt
        rw [hmsg'', hrank] at hlt
        exact ih _ hlt u asg'' hasg'' bj hbj hstj hmultj rfl
      have hacc : (G.get u).statelessAccepted (bs.toGuestRules r0) asg'' :=
        statelessAccepted_of_sinks hunpack hsinks hGuests hSize hBudget' hsat u asg'' hasg''
      exact absurd (hmsg'' ▸ (hlegal u).sendsMaintain asg''
          (hsat.satisfiesGuest u asg'' hasg'') hacc (hRanks u asg'' hasg'') bi'' hbi'' hst'' h1
          hlow) hno
    · exact Or.inr hm1
  -- Every *non-exempt* host chip is silent too — same argument as before, just narrowed.
  have hzero : ∀ u : Fin host.chips.length, u ≠ idx →
      ((a.hostAssignment u).map (fun effect => effect
        ((bi'.eval asg').busId, (bi'.eval asg').payload))).sum = 0 := by
    intro u hu
    refine List.sum_eq_zero (fun x hx => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    by_contra hcm
    exact hno (payloadOk_of_exists
      (hstateful a.hostAssignment (hsat.satisfiesHost) u hu c hc _ hst' hcm))
  -- So the host's whole net at this message is exactly the exempt chip's own (single) touch.
  have hhost_eq : a.hostAssignment.busEffect ((bi'.eval asg').busId, (bi'.eval asg').payload)
      = ((a.hostAssignment idx).map (fun effect => effect
          ((bi'.eval asg').busId, (bi'.eval asg').payload))).sum :=
    Finset.sum_eq_single idx (fun u _ hu => hzero u hu)
      (fun h => absurd (Finset.mem_univ idx) h)
  -- And that touch, being a single instance, is `0` or `-1` — never a genuine sender either.
  have hlen : (a.hostAssignment idx).length = 1 := hsat.satisfiesHost.2 idx hexempt.singleton
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hlen
  have he : ((a.hostAssignment idx).map (fun effect => effect
        ((bi'.eval asg').busId, (bi'.eval asg').payload))).sum = 0
      ∨ ((a.hostAssignment idx).map (fun effect => effect
        ((bi'.eval asg').busId, (bi'.eval asg').payload))).sum = (-1 : ZMod p) := by
    rw [hc0, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases hc0m : c0 ((bi'.eval asg').busId, (bi'.eval asg').payload) = 0
    · exact Or.inl hc0m
    · exact Or.inr (hexempt.uniform a.hostAssignment (hsat.satisfiesHost) c0
        (hc0 ▸ List.mem_cons_self) _ hst' hc0m)
  -- A pile of receives — guest and (at most) the one exempt host touch — that cannot balance.
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  refine guestNet_add_ne_zero_of_uniform hsat hSize hBudget hneg huni hasg' hbi' rfl hmult' he ?_
  have hbal := hsat.balances ((bi'.eval asg').busId, (bi'.eval asg').payload)
  rw [busEffect_apply, hhost_eq] at hbal
  exact hbal

/-- **`Host.forcesAccepts` is derivable.** Honest table sinks on the stateless buses, host chips
    that maintain the invariants on the stateful ones, bus semantics whose stateful acceptance
    follows from those invariants, and the anti-wraparound budget together give every guest
    instance the full `Circuit.satisfies` — not just its algebraic constraints, and with no
    assumption about acceptance placed on the guest chips themselves. -/
theorem forcesAccepts_of_hostSound [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p} {maxWindow : ℕ}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c → c.legalGuest (bs.toGuestRules r0) rm.rank rm.bound maxWindow)
    (hsinks : host.sinksAreTables bs)
    (hstateful : ∃ idx : Fin host.chips.length,
      host.exemptChip bs idx ∧ host.statefulChipsMaintain bs idx)
    (hbs : bs.statefulAcceptsOfPayloadOk r0) (hpins : host.pinsRanks rm) :
    host.forcesAccepts bs := by
  intro G maxInteractions hGuests hSize hBudget a hsat t asg hasg
  have hBudget' : maxInteractions * host.maxInstances < p := by omega
  have hRanks := hpins G maxInteractions hGuests hSize hBudget' a hsat
  refine ⟨hsat.satisfiesGuest t asg hasg, fun bi hbi hmult => ?_⟩
  by_cases hst : bs.isStateful bi.busId
  · exact hbs _ hst (maintains_of_stateful_active hunpack hsinks hstateful hGuests hSize hBudget
      hsat hRanks hasg hbi hst hmult)
  · exact statelessAccepted_of_sinks hunpack hsinks hGuests hSize hBudget' hsat t asg hasg bi hbi
      (by simpa using hst) hmult

/-- `Host.realizes` gives `Host.forcesAccepts`. -/
theorem Host.realizes.forcesAccepts [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p} {maxWindow : ℕ} (h : host.realizes bs rm r0 maxWindow) :
    host.forcesAccepts bs :=
  forcesAccepts_of_hostSound h.legalGuest h.sinksAreTables h.statefulChipsMaintain
    h.statefulAcceptsOfPayloadOk h.pinsRanks
