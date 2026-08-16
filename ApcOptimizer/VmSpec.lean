import ApcOptimizer.VmSpec.Basic
import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.VmSpec.OpenVm
import ApcOptimizer.VmSpec.Theorems
import ApcOptimizer.VmSpec.Audit.OpenVmLegalAudit
import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.LegalityPreservation
import ApcOptimizer.VmSpec.Implementation.Rank
import ApcOptimizer.VmSpec.Implementation.Counting
import ApcOptimizer.VmSpec.Implementation.Realizes
import ApcOptimizer.VmSpec.Implementation.Connection
import ApcOptimizer.VmSpec.Implementation.OpenVmConnection
import ApcOptimizer.VmSpec.Implementation.Chain
import ApcOptimizer.VmSpec.Implementation.OpenVmChain
import ApcOptimizer.VmSpec.Implementation.Validation

/-! # The VM-level correctness spec

    `Spec.lean` says what it means to replace *one* circuit correctly. This folder says what it
    means to replace the guest chips of a *whole VM* correctly, and connects the two.

    ## What has to be audited

    The split is by directory, matching the convention `AGENTS.md` sets for the repository as a
    whole: **everything directly under `VmSpec/` is audited; nothing under
    `VmSpec/Implementation/` is.**

    ### Audited — the theorems

    * `VmSpec/Theorems.lean` — the VM-level correctness theorems. Statements only: each proof is a
      one-line application of an `Implementation/` lemma, mirroring `ApcOptimizer/Optimizer.lean`.
      Read this to learn what has been established.

    ### Audited — the statement

    * `VmSpec/Basic.lean` — the spec proper. `Host`, `Vm`, `VmSat`, `VmAssignment.effects`,
      `CanProduce`, and the `VmSoundReplacement`/`VmCompleteReplacement`/`VmEquivalent` trio. Every
      field of `Host` here feeds `VmSat` or `effects`, so each one changes what the theorem *means*.
    * `VmSpec/Legal.lean` — `Circuit.legalGuest`, what a VM requires of a guest chip. This is a
      *hypothesis* of the theorems rather than part of the spec, so the risk it carries is the
      opposite one: too strong and the theorem is vacuous rather than wrong.
    * `VmSpec/OpenVm.lean` — the modelled OpenVM: its host chips, and `Circuit.advancesClock`. The
      chips decide which real runs `CanProduce` can represent, so a chip that is too restrictive
      silently narrows the claim.

    ### Audited — files that audit the audit surface

    `VmSpec/Audit/` (its own README has the fuller pitch): nothing in `Basic.lean`/`Legal.lean`/
    `OpenVm.lean`/`Theorems.lean` depends on this folder, and nothing in it proves a new claim about
    a run — each file is evidence that those files' hypotheses are checkable and non-vacuous, not an
    ingredient of the soundness argument. It still lives directly under `VmSpec/`, so the directory
    rule still applies: a mistake here is a mistake in what gets audited, just not a mistake that can
    make a theorem *wrong*, only vacuous or (for the checker) unsound.

    * `Audit/OpenVmLegalAudit.lean` — real OpenVM circuit shapes shown to satisfy the audited
      hypotheses, so that "too strong and the theorem is vacuous" is a checkable worry rather than a
      standing one.
    * `Audit/SendOnlyPolarity.lean` — a decidable, syntactic check that a candidate circuit's
      bus-interaction multiplicities satisfy `Circuit.statelessSendOnly`/`Circuit.statefulPolarity`.
      It proves no new claim, only that a `Bool` a checker computes implies the existing legality
      clauses. What needs auditing is the *statement* of `checkMultiplicities_sound` — that a `true`
      result really does give `statelessSendOnly`/`statefulPolarity` — exactly as a pass's
      correctness statement is audited in `ApcOptimizer/Implementation/OptimizerPasses/`; the
      checker itself (`Expression.foldConst`, `checkMultiplicities`) needs no audit, only that
      theorem to be true of it.
    * `Audit/LegalityPreservation.lean` — a formal counterexample: a per-chip
      `Circuit.isSoundReplacementOf` that violates `Circuit.statelessSendOnly` outright, showing
      `PreservesLegality` cannot be derived from soundness and has to be assumed or separately
      established, as `openVm_vmSoundReplacement` already does.

    ### Not audited — the argument

    Everything under `VmSpec/Implementation/`. These files are load-bearing for the *proof* and
    invisible in every statement, so a mistake in them cannot make a theorem mean the wrong thing —
    it can only make the build fail.

    * `Implementation/Rank.lean` — `RankModel`, the ordering the balancing induction descends on.
      Deliberately *not* a field of `Host`: see that file for why a wrong choice cannot make the
      theorem unsound.
    * `Implementation/Counting.lean` — the anti-wraparound counting lemmas.
    * `Implementation/Realizes.lean` — `Host.realizes` and what it buys (`Host.forcesAccepts`).
    * `Implementation/Connection.lean` — per-chip `isSoundReplacementOf` to `VmSoundReplacement`.
    * `Implementation/OpenVmConnection.lean` — the same, discharged for `openVmHost`.
    * `Implementation/Chain.lean` — the balanced-arc combinatorics that turn a run's
      execution-bridge traffic into an ordering, with no mention of a circuit or a bus.
    * `Implementation/OpenVmChain.lean` — that argument applied to `openVmHost`, giving
      `Host.pinsRanks`: one range-checked boundary timestamp bounds every timestamp in the run.
    * `Implementation/Validation.lean` — sanity lemmas about the spec (that the guest list behaves
      as a set, that `VmSoundReplacement` is a preorder). -/
