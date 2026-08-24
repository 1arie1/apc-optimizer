and now, try for sendsOk
The compact was canceled — continuing with sendsOk. Let me look at exactly what the hand proof does.

Bash
IN
grep -n "The five memory sends" -A 62 ApcOptimizer/VmSpec/Audit/RealApcLegality.lean | head -70

OUT
492:  · -- The five memory sends: four echoes and one masked value.
493-    rintro i ⟨hst, hmult⟩ hlow
494-    fin_cases i
495-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
496-        babyBear_negOne_ne_one] at hmult
497-    · have h0 := hlow ⟨0, by decide⟩ (by simp [Fin.lt_def]) ⟨rfl,
498-        by simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
499-          babyBear_negOne_ne_zero]⟩
500-      replace h0 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
501-        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
502-        asg ⟨"a__3_0", some 22⟩, asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩]) := h0
503-      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
504-        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
505-        asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩])
506-      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h0)
507-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
508-        babyBear_negOne_ne_one] at hmult
509-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
510-        babyBear_negOne_ne_one] at hmult
511-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
512-        babyBear_negOne_ne_one] at hmult
513-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
514-        babyBear_negOne_ne_one] at hmult
515-    · -- the word read at address 44 is written on to address 56
516-      have h4 := hlow ⟨4, by decide⟩ (by simp [Fin.lt_def]) ⟨rfl,
517-        by simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
518-          babyBear_negOne_ne_zero]⟩
519-      replace h4 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
520-        asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
521-        asg ⟨"a__3_1", some 58⟩, asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩]) := h4
522-      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 56,
523-        asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
524-        asg ⟨"a__3_1", some 58⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 5])
525-      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h4)
526-    · simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
527-        OpenVmBusType.isStateful] at hst
528-    · -- the word read at address 40 is written on to address 52
529-      have h0 := hlow ⟨0, by decide⟩ (by simp [Fin.lt_def]) ⟨rfl,
530-        by simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
531-          babyBear_negOne_ne_zero]⟩
532-      replace h0 : openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 40,
533-        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
534-        asg ⟨"a__3_0", some 22⟩, asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩]) := h0
535-      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 52,
536-        asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
537-        asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 6])
538-      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp h0)
539-    · -- the fresh write at address 44, byte-valued because the bitwise table masked it
540-      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
541-        asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
542-      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩
543-    · simp [apc2105000Opt, Circuit.multAt, BusInteraction.eval, Expression.eval,
544-        babyBear_negOne_ne_one] at hmult
545-    · show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 0, 0, 0, 0, 0,
546-        asg ⟨"from_state__timestamp_0", some 1⟩ + 10])
547-      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
548-        ⟨isByte_zero, isByte_zero, isByte_zero, isByte_zero⟩
549-    · -- the bridge send: `openVmPayloadOk` asks nothing of an execution-bridge state
550-      simp [apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules,
551-        openVmPayloadOk, defaultBusMap, Circuit.msgAt]
552-    all_goals
553-      simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
554-        OpenVmBusType.isStateful] at hst
Now building it. Four tiers: not-a-send, not-memory, literal-byte limbs, and echo of an earlier receive.

Bash
IN
cat > ApcOptimizer/VmSpec/Audit/ByteCheck.lean <<'LEAN'
import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.OpenVmLegalAudit

set_option autoImplicit false

/-! **A static check for `StepLayout.sendsOk`, OpenVM's byte invariant.**

    `sendsOk` asks that what a chip sends on a stateful bus be `payloadOk` — for OpenVM, that a
    memory record's four data limbs are bytes — given that everything the chip already touched is.

    Real chips justify a send in a small number of ways, and this file decides four of them:

    * the interaction is not a send at all, so there is nothing to ask;
    * it is not on the memory bus, where `openVmPayloadOk` asks nothing;
    * its data limbs are literal bytes (a fresh write of zeros);
    * its data limbs are those of an *earlier* interaction, so `sendsOk`'s own hypothesis supplies
      them — a memory send echoing the read it just did.

    A fifth is left to the caller (`external`): a limb that is a byte because a lookup table says
    so, which is where a VM's own arithmetic enters and a decidable check stops. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

--------- The memory-record shape ---------

/-- A normalized payload in OpenVM's memory shape `(addr_space, ptr, d₀…d₃, t)`, with the address
    space pinned to `1`. -/
def memShape : List (LinForm p) → Bool
  | [f0, _, _, _, _, _, _] => f0.isConst 1
  | _ => false

/-- Its four data limbs. -/
def dataLimbs : List (LinForm p) → List (LinForm p)
  | [_, _, f2, f3, f4, f5, _] => [f2, f3, f4, f5]
  | _ => []

/-- Whether a form is a literal byte. -/
def isByteConst (f : LinForm p) : Bool :=
  f.coefs.all (· == 0) && decide (f.const.val < 256)

theorem isByte_of_isByteConst {vs : List Variable} {asg : Variable → ZMod p} {f : LinForm p}
    (h : isByteConst f = true) : isByte (f.eval vs asg) := by
  simp only [isByteConst, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [LinForm.eval_of_coefs_zero vs f asg h.1]
  exact h.2

/-- What a payload in memory shape evaluates to. -/
theorem memShape_eval {vs : List Variable} {rules : List (PinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {es : List (Expression p)} {pl : List (LinForm p)}
    (hpl : payloadLin vs rules es = some pl) (hshape : memShape pl = true) :
    ∃ (ptr ts : ZMod p) (d0 d1 d2 d3 : LinForm p),
      dataLimbs pl = [d0, d1, d2, d3] ∧
      es.map (fun e => e.eval asg)
        = [1, ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg, d3.eval vs asg, ts] := by
  match pl, hshape with
  | [f0, f1, f2, f3, f4, f5, f6], hshape =>
    refine ⟨f1.eval vs asg, f6.eval vs asg, f2, f3, f4, f5, rfl, ?_⟩
    rw [payloadLin_eval hrules hpl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [memShape, isByteConst, LinForm.isConst, Bool.and_eq_true, beq_iff_eq] at hshape
    rw [LinForm.eval_of_coefs_zero vs f0 asg hshape.2, hshape.1]
LEAN
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 10 "error" | head -25

OUT
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:62:11: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Eq.refl` does not have explicit fields, but 7 were provided
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:63:4: No goals to be solved
error: Lean exited with code 1
Some required targets logged failures:
- ApcOptimizer.VmSpec.Audit.ByteCheck
error: build failed
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("""    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [memShape, isByteConst, LinForm.isConst, Bool.and_eq_true, beq_iff_eq] at hshape
    rw [LinForm.eval_of_coefs_zero vs f0 asg hshape.2, hshape.1]""",
"""    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [memShape, LinForm.isConst, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hshape
    rw [LinForm.eval_of_coefs_zero vs f0 asg (by simpa using hshape.2), hshape.1]""")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "error" | head -25

OUT
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:62:11: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Eq.refl` does not have explicit fields, but 6 were provided
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:63:4: No goals to be solved
error: Lean exited with code 1
Some required targets logged failures:
- ApcOptimizer.VmSpec.Audit.ByteCheck
error: build failed
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("""    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [memShape,""","""    simp only [memShape,""")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "error" | head -25

OUT
(Bash completed with no output)
Now the witnesses, the check, and its soundness.

Bash
IN
cat >> ApcOptimizer/VmSpec/Audit/ByteCheck.lean <<'LEAN'

--------- Witnesses ---------

/-- Why one interaction's payload is Ok. -/
inductive ByteWitness where
  /-- Its multiplicity is not `1`, so `sendsOk` asks nothing of it. -/
  | notSend
  /-- It is not on the memory bus, where `openVmPayloadOk` asks nothing. -/
  | notMemory
  /-- Its four data limbs are literal bytes. -/
  | limbs
  /-- Its data limbs are those of interaction `j`, which precedes it and is active — so
      `sendsOk`'s own hypothesis already vouches for them. -/
  | echo (j : ℕ)
  /-- The caller proves it. -/
  | external
  deriving DecidableEq, Repr

/-- Whether a multiplicity expression folds to something other than `1`. -/
def multNotOne (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 1)
  | none => false

/-- Whether it folds to something other than `0`. -/
def multNotZero (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 0)
  | none => false

/-- Check one interaction against its witness. -/
def byteCheckOne (vs : List Variable) (rules : List (PinRule p))
    (L : List (BusInteraction (Expression p))) (i : ℕ)
    (bi : BusInteraction (Expression p)) (w : ByteWitness) : Bool :=
  match w with
  | .notSend => multNotOne rules bi
  | .notMemory => !(bi.busId == openVmMemBusId)
  | .limbs =>
    match payloadLin vs rules bi.payload with
    | some pl => memShape pl && (dataLimbs pl).all isByteConst
    | none => false
  | .echo j =>
    decide (j < i) &&
      (match L[j]? with
       | none => false
       | some bj =>
         (bj.busId == openVmMemBusId) && multNotZero rules bj &&
           (match payloadLin vs rules bi.payload, payloadLin vs rules bj.payload with
            | some pli, some plj =>
              memShape pli && memShape plj && (dataLimbs pli == dataLimbs plj)
            | _, _ => false))
  | .external => true

/-- Check every interaction against its witness. -/
def byteCheckAll (vs : List Variable) (rules : List (PinRule p))
    (L : List (BusInteraction (Expression p))) (W : List ByteWitness) : Bool :=
  (List.range L.length).all fun i =>
    match L[i]?, W[i]? with
    | some bi, some w => byteCheckOne vs rules L i bi w
    | _, _ => false

theorem byteCheckAll_get {vs : List Variable} {rules : List (PinRule p)}
    {L : List (BusInteraction (Expression p))} {W : List ByteWitness}
    (h : byteCheckAll vs rules L W = true) (i : Fin L.length) :
    ∃ w : ByteWitness, byteCheckOne vs rules L i.val (L.get i) w = true := by
  have hall := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [List.getElem?_eq_getElem i.isLt] at hall
  cases hw : W[i.val]? with
  | none => rw [hw] at hall; simp at hall
  | some w => exact ⟨w, by rw [hw] at hall; exact hall⟩
LEAN
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "error" | head -25

OUT
(Bash completed with no output)
Bash
IN
grep -n "def openVmGuestRules" -A 10 ApcOptimizer/VmSpec/OpenVm.lean; echo "=== isStateful_default:"; grep -rn "openVmIsStateful_default" -A 8 ApcOptimizer/VmSpec/ | grep -A 8 "theorem openVmIsStateful_default" | head -10

OUT
412:def openVmGuestRules (busMap : BusMap) (memBusId : Nat) : GuestBusRules p where
413-  isStateful := openVmIsStateful busMap
414-  accepts := ApcOptimizer.OpenVM.accepts busMap
415-  payloadOk := openVmPayloadOk busMap
416-  execBusId := openVmExecBusId
417-  memBusId := memBusId
418-  getTimestamp := openVmTimestamp memBusId
419-
420-/-- A witness that the connector chip's contribution closes a segment's execution bridge: the
421-    segment's initial and final `(pc, timestamp)` states.
422-
=== isStateful_default:
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean:503:theorem openVmIsStateful_default {b : Nat} (h : openVmIsStateful defaultBusMap b = true) :
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-504-    b = openVmMemBusId ∨ b = openVmExecBusId := by
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-505-  match b with
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-506-  | 0 => exact Or.inr rfl
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-507-  | 1 => exact Or.inl rfl
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-508-  | 2 | 3 | 4 | 5 | 6 | 7 | _ + 8 =>
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-509-    simp [openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at h
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-510-
ApcOptimizer/VmSpec/Implementation/OpenVmChain.lean-511-/-- **A placed interaction's rank, read off the chain.** Its step's `base` is `1 + T` for an
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("""  | .limbs =>
    match payloadLin vs rules bi.payload with
    | some pl => memShape pl && (dataLimbs pl).all isByteConst
    | none => false""",
"""  | .limbs =>
    (bi.busId == openVmMemBusId) &&
      (match payloadLin vs rules bi.payload with
       | some pl => memShape pl && (dataLimbs pl).all isByteConst
       | none => false)""")
s=s.replace("""  | .echo j =>
    decide (j < i) &&""","""  | .echo j =>
    (bi.busId == openVmMemBusId) && decide (j < i) &&""")
open(p,'w').write(s)
PY
cat >> ApcOptimizer/VmSpec/Audit/ByteCheck.lean <<'LEAN'

--------- Soundness ---------

/-- **Soundness of the byte check.** A `true` witness turns `sendsOk`'s hypothesis into its
    conclusion, for every justification except `external`, which the caller supplies. -/
theorem byteCheckOne_sound [Fact (1 < p)] {vs : List Variable} {rules : List (PinRule p)}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {c : Circuit p} {i : Fin c.busInteractions.length} {w : ByteWitness}
    (h : byteCheckOne vs rules c.busInteractions i.val (c.busInteractions.get i) w = true)
    (hsend : c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i)
    (hlow : ∀ j : Fin c.busInteractions.length, j < i →
      c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
      openVmPayloadOk defaultBusMap (c.msgAt asg j))
    (hext : w = .external → openVmPayloadOk defaultBusMap (c.msgAt asg i)) :
    openVmPayloadOk defaultBusMap (c.msgAt asg i) := by
  have hbus : (c.msgAt asg i).1 = (c.busInteractions.get i).busId := rfl
  cases hw : w with
  | external => exact hext hw
  | notSend =>
    exfalso
    rw [hw] at h
    simp only [byteCheckOne, multNotOne] at h
    cases hm : (c.busInteractions.get i).multiplicity.foldConstWith rules with
    | none => rw [hm] at h; cases h
    | some v =>
      rw [hm] at h
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
      exact h ((Expression.foldConstWith_eq hrules hm).symm.trans hsend.2)
  | notMemory =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
    rcases openVmIsStateful_default hsend.1 with hmem | hexec
    · exact absurd hmem h
    · simp [openVmPayloadOk, hbus, hexec, defaultBusMap, openVmExecBusId]
  | limbs =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hmem, h⟩ := h
    cases hpl : payloadLin vs rules (c.busInteractions.get i).payload with
    | none => rw [hpl] at h; cases h
    | some pl =>
      rw [hpl] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨ptr, ts, d0, d1, d2, d3, hdl, hev⟩ := memShape_eval hrules hpl h.1
      rw [hdl] at h
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at h
      have hmsg : c.msgAt asg i
          = ((1 : ℕ), [(1 : ZMod p), ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg,
              d3.eval vs asg, ts]) := by
        rw [Circuit.msgAt]
        exact Prod.ext (by rw [← hbus, Circuit.msgAt] at hmem ⊢; exact hmem) hev
      rw [hmsg]
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
        ⟨isByte_of_isByteConst h.2.1, isByte_of_isByteConst h.2.2.1,
         isByte_of_isByteConst h.2.2.2.1, isByte_of_isByteConst h.2.2.2.2.1⟩
  | echo j =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hmem, hji⟩, h⟩ := h
    cases hbj : c.busInteractions[j]? with
    | none => rw [hbj] at h; cases h
    | some bj =>
      rw [hbj] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hbjmem, hbjmult⟩, h⟩ := h
      cases hpli : payloadLin vs rules (c.busInteractions.get i).payload with
      | none => rw [hpli] at h; cases h
      | some pli =>
        cases hplj : payloadLin vs rules bj.payload with
        | none => rw [hpli, hplj] at h; cases h
        | some plj =>
          rw [hpli, hplj] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hshi, hshj⟩, hdeq⟩ := h
          have hjlt : j < c.busInteractions.length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hbj; cases hbj
          have hget : c.busInteractions.get ⟨j, hjlt⟩ = bj := by
            rw [List.get_eq_getElem, ← Option.some_inj, ← List.getElem?_eq_getElem hjlt, hbj]
          -- The earlier interaction is active, so `sendsOk`'s hypothesis vouches for it.
          have hmultj : c.multAt asg ⟨j, hjlt⟩ ≠ 0 := by
            cases hm : bj.multiplicity.foldConstWith rules with
            | none => rw [hbjmem] at hbjmult; simp [multNotZero, hm] at hbjmult
            | some v =>
              simp only [multNotZero, hm, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hbjmult
              rw [Circuit.multAt, hget]
              exact fun hc => hbjmult ((Expression.foldConstWith_eq hrules hm).symm.trans hc)
          have hactj : c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg
              ⟨j, hjlt⟩ := ⟨by rw [hget, hbjmem]; rfl, hmultj⟩
          have hlowj := hlow ⟨j, hjlt⟩ (Fin.lt_def.mpr hji) hactj
          obtain ⟨ptri, tsi, a0, a1, a2, a3, hdli, hevi⟩ := memShape_eval hrules hpli hshi
          obtain ⟨ptrj, tsj, b0, b1, b2, b3, hdlj, hevj⟩ := memShape_eval hrules hplj hshj
          rw [hdli, hdlj] at hdeq
          simp only [List.cons.injEq, and_true] at hdeq
          obtain ⟨e0, e1, e2, e3⟩ := hdeq
          have hmsgj : c.msgAt asg ⟨j, hjlt⟩
              = ((1 : ℕ), [(1 : ZMod p), ptrj, b0.eval vs asg, b1.eval vs asg, b2.eval vs asg,
                  b3.eval vs asg, tsj]) := by
            rw [Circuit.msgAt, hget]
            exact Prod.ext hbjmem hevj
          have hmsgi : c.msgAt asg i
              = ((1 : ℕ), [(1 : ZMod p), ptri, a0.eval vs asg, a1.eval vs asg, a2.eval vs asg,
                  a3.eval vs asg, tsi]) := by
            rw [Circuit.msgAt]
            exact Prod.ext (by rw [← hbus, Circuit.msgAt] at hmem ⊢; exact hmem) hevi
          rw [hmsgj] at hlowj
          rw [hmsgi, e0, e1, e2, e3]
          exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
            ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp hlowj)
LEAN
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "^error" | head -30

OUT
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:168:4: unsolved goals
case notMemory.inr
p : ℕ
inst✝ : Fact (1 < p)
vs : List Variable
rules : List (PinRule p)
asg : ChipAssignment p
hrules : ∀ q ∈ rules, q.1.eval asg = q.2
c : Circuit p
i : Fin c.busInteractions.length
w : ByteWitness
hsend : c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i
hlow :
--
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:185:31: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (c.busInteractions.get i).busId
in the target expression
  (((c.busInteractions.get i).eval asg).busId, ((c.busInteractions.get i).eval asg).payload).1 =
    (1, [1, ptr, LinForm.eval vs d0 asg, LinForm.eval vs d1 asg, LinForm.eval vs d2 asg, LinForm.eval vs d3 asg, ts]).1

p : ℕ
inst✝ : Fact (1 < p)
vs : List Variable
rules : List (PinRule p)
asg : ChipAssignment p
hrules : ∀ q ∈ rules, q.1.eval asg = q.2
c : Circuit p
--
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:217:26: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  bj.busId
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("        exact Prod.ext (by rw [← hbus, Circuit.msgAt] at hmem ⊢; exact hmem) hev",
            "        exact Prod.ext hmem hev")
s=s.replace("            exact Prod.ext (by rw [← hbus, Circuit.msgAt] at hmem ⊢; exact hmem) hevi",
            "            exact Prod.ext hmem hevi")
s=s.replace("            exact Prod.ext hbjmem hevj","            exact Prod.ext hbjmem hevj")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 20 "^error" | head -40

OUT
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:168:4: unsolved goals
case notMemory.inr
p : ℕ
inst✝ : Fact (1 < p)
vs : List Variable
rules : List (PinRule p)
asg : ChipAssignment p
hrules : ∀ q ∈ rules, q.1.eval asg = q.2
c : Circuit p
i : Fin c.busInteractions.length
w : ByteWitness
hsend : c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i
hlow :
  ∀ j < i,
    c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
      openVmPayloadOk defaultBusMap (c.msgAt asg j)
hext : w = ByteWitness.external → openVmPayloadOk defaultBusMap (c.msgAt asg i)
hbus : (c.msgAt asg i).1 = (c.busInteractions.get i).busId
hw : w = ByteWitness.notMemory
h : ¬(c.busInteractions.get i).busId = openVmMemBusId
hexec : (c.busInteractions.get i).busId = openVmExecBusId
--
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:217:26: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  bj.busId
in the target expression
  multNotZero rules bj = true

case none
p : ℕ
inst✝ : Fact (1 < p)
vs : List Variable
rules : List (PinRule p)
asg : ChipAssignment p
hrules : ∀ q ∈ rules, q.1.eval asg = q.2
c : Circuit p
i : Fin c.busInteractions.length
w : ByteWitness
hsend : c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i
hlow :
  ∀ j < i,
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("    · simp [openVmPayloadOk, hbus, hexec, defaultBusMap, openVmExecBusId]",
"""    · have : (c.msgAt asg i).1 = openVmExecBusId := hbus.trans hexec
      simp only [openVmPayloadOk, this, openVmExecBusId, defaultBusMap]""")
s=s.replace("            | none => rw [hbjmem] at hbjmult; simp [multNotZero, hm] at hbjmult",
            "            | none => simp only [multNotZero, hm] at hbjmult; cases hbjmult")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 16 "^error" | head -30

OUT
(Bash completed with no output)
Now wiring it. First, extending the check so a stateless interaction also counts as "not a send".

Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("""  /-- Its multiplicity is not `1`, so `sendsOk` asks nothing of it. -/
  | notSend""","""  /-- It is not a stateful send — its bus is a lookup, or its multiplicity is not `1` — so
      `sendsOk` asks nothing of it. -/
  | notSend""")
s=s.replace("  | .notSend => multNotOne rules bi",
            "  | .notSend => multNotOne rules bi || !openVmIsStateful defaultBusMap bi.busId")
s=s.replace("""    rw [hw] at h
    simp only [byteCheckOne, multNotOne] at h
    cases hm : (c.busInteractions.get i).multiplicity.foldConstWith rules with
    | none => rw [hm] at h; cases h
    | some v =>
      rw [hm] at h
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
      exact h ((Expression.foldConstWith_eq hrules hm).symm.trans hsend.2)""",
"""    rw [hw] at h
    simp only [byteCheckOne, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · simp only [multNotOne] at h
      cases hm : (c.busInteractions.get i).multiplicity.foldConstWith rules with
      | none => rw [hm] at h; cases h
      | some v =>
        rw [hm] at h
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
        exact h ((Expression.foldConstWith_eq hrules hm).symm.trans hsend.2)
    · exact absurd hsend.1 (by rw [h]; simp [openVmGuestRules])""")
# byteCheckAll_get: return the witness by getD
s=s.replace("""theorem byteCheckAll_get {vs : List Variable} {rules : List (PinRule p)}
    {L : List (BusInteraction (Expression p))} {W : List ByteWitness}
    (h : byteCheckAll vs rules L W = true) (i : Fin L.length) :
    ∃ w : ByteWitness, byteCheckOne vs rules L i.val (L.get i) w = true := by
  have hall := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [List.getElem?_eq_getElem i.isLt] at hall
  cases hw : W[i.val]? with
  | none => rw [hw] at hall; simp at hall
  | some w => exact ⟨w, by rw [hw] at hall; exact hall⟩""",
"""theorem byteCheckAll_get {vs : List Variable} {rules : List (PinRule p)}
    {L : List (BusInteraction (Expression p))} {W : List ByteWitness}
    (h : byteCheckAll vs rules L W = true) (i : Fin L.length) :
    byteCheckOne vs rules L i.val (L.get i) (W.getD i.val .notSend) = true := by
  have hall := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [List.getElem?_eq_getElem i.isLt] at hall
  cases hw : W[i.val]? with
  | none => rw [hw] at hall; simp at hall
  | some w =>
    rw [hw] at hall
    rwa [List.getD_eq_getElem?_getD, hw]""")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "^error" | head -25

OUT
error: ApcOptimizer/VmSpec/Audit/ByteCheck.lean:168:35: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  openVmIsStateful defaultBusMap (c.busInteractions.get i).busId
in the target expression
  ¬(openVmGuestRules defaultBusMap openVmMemBusId).isStateful (c.busInteractions.get i).busId = true

p : ℕ
inst✝ : Fact (1 < p)
vs : List Variable
rules : List (PinRule p)
asg : ChipAssignment p
hrules : ∀ q ∈ rules, q.1.eval asg = q.2
c : Circuit p
i : Fin c.busInteractions.length
--
error: Lean exited with code 1
Some required targets logged failures:
- ApcOptimizer.VmSpec.Audit.ByteCheck
error: build failed
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/ByteCheck.lean'
s=open(p).read()
s=s.replace("    · exact absurd hsend.1 (by rw [h]; simp [openVmGuestRules])",
            "    · exact absurd hsend.1 (by simp only [openVmGuestRules]; rw [h]; simp)")
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "^error" | head -20

OUT
(Bash completed with no output)
Bash
IN
cat >> ApcOptimizer/VmSpec/Audit/ByteCheck.lean <<'LEAN'

/-- **`StepLayout.sendsOk`, from the witnesses.** Everything the check decides is discharged; the
    `external` indices are left to the caller, and for every other index that hypothesis is
    decidably vacuous. -/
theorem byteCheck_sendsOk [Fact (1 < p)] {vs : List Variable} {rules : List (PinRule p)}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {c : Circuit p} {W : List ByteWitness}
    (h : byteCheckAll vs rules c.busInteractions W = true)
    (hext : ∀ i : Fin c.busInteractions.length, W.getD i.val .notSend = .external →
      c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i →
      (∀ j : Fin c.busInteractions.length, j < i →
        c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
        openVmPayloadOk defaultBusMap (c.msgAt asg j)) →
      openVmPayloadOk defaultBusMap (c.msgAt asg i)) :
    ∀ i : Fin c.busInteractions.length,
      c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i →
      (∀ j : Fin c.busInteractions.length, j < i →
        c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
        openVmPayloadOk defaultBusMap (c.msgAt asg j)) →
      openVmPayloadOk defaultBusMap (c.msgAt asg i) := fun i hsend hlow =>
  byteCheckOne_sound hrules (byteCheckAll_get h i) hsend hlow (fun hw => hext i hw hsend hlow)

end ApcOptimizer.OpenVM
LEAN
timeout 900 lake build ApcOptimizer.VmSpec.Audit.ByteCheck 2>&1 | grep -A 12 "^error" | head -20

OUT
(Bash completed with no output)
Checker's built. Now pointing it at the real APC.

Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/RealApcLegality.lean'
s=open(p).read()
s=s.replace("import ApcOptimizer.VmSpec.Audit.PlaceCheck",
            "import ApcOptimizer.VmSpec.Audit.PlaceCheck\nimport ApcOptimizer.VmSpec.Audit.ByteCheck")
s=s.replace('''   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩]''',
'''   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩,
   ⟨"a__0_0", some 19⟩, ⟨"a__1_0", some 20⟩, ⟨"a__2_0", some 21⟩, ⟨"a__3_0", some 22⟩,
   ⟨"a__0_1", some 55⟩, ⟨"a__1_1", some 56⟩, ⟨"a__2_1", some 57⟩, ⟨"a__3_1", some 58⟩,
   ⟨"a__0_2", some 91⟩]''')
open(p,'w').write(s)
PY
cat > ApcOptimizer/VmSpec/Audit/TmpB.lean <<'LEAN'
import ApcOptimizer.VmSpec.Audit.RealApcLegality

namespace ApcOptimizer.OpenVM

def optWitnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend

#eval byteCheckAll optVars optPinRules apc2105000Opt.busInteractions optWitnesses

#eval (List.range 23).filter fun i =>
  !(match apc2105000Opt.busInteractions[i]?, optWitnesses[i]? with
    | some bi, some w => byteCheckOne optVars optPinRules apc2105000Opt.busInteractions i bi w
    | _, _ => false)

end ApcOptimizer.OpenVM
LEAN
timeout 900 lake build ApcOptimizer.VmSpec.Audit.TmpB 2>&1 | grep -E "^(error|info)" -A 3 | head -20

OUT
info: ApcOptimizer/VmSpec/Audit/TmpB.lean:9:0: true
info: ApcOptimizer/VmSpec/Audit/TmpB.lean:11:0: []
Build completed successfully (1234 jobs).
Bash
IN
rm -f ApcOptimizer/VmSpec/Audit/TmpB.lean; sed -n '68,76p' ApcOptimizer/VmSpec/Audit/RealApcLegality.lean

OUT
    circuits sit at the literal `babyBear`, so the one theorem that needs `ZMod babyBear` to be a
    field takes the same assumption as an instance hypothesis rather than re-proving it (Mathlib's
    `norm_num` primality extension is not built in this checkout). -/

/-- The rules all three circuits are checked against: OpenVM's own bus map, memory on bus `1`. -/
abbrev apcRules : GuestBusRules babyBear :=
  openVmGuestRules defaultBusMap openVmMemBusId

/-- powdr emits `-1` as the literal `p - 1`; the two are the same field element. -/
Bash
IN
python3 - <<'PY'
p='ApcOptimizer/VmSpec/Audit/RealApcLegality.lean'
s=open(p).read()
anchor = "/-- **A real optimized APC has a step layout.**"
block = '''/-- Why each of `apc2105000Opt`'s interactions is `payloadOk`, position by position: six memory
    receives and the bridge receive are not sends; three memory sends echo the read that preceded
    them; one writes literal zeros; the bridge send is not on the memory bus; ten lookups are not
    stateful. Only the masked write at position `9` is left to the caller — it is a byte because
    the bitwise table says so, which is where a decidable check stops. -/
def optWitnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend

theorem optByteCheck :
    byteCheckAll optVars optPinRules apc2105000Opt.busInteractions optWitnesses = true := by decide

'''
s = s.replace(anchor, block + anchor)

old = '''  · -- The five memory sends: four echoes and one masked value.
    rintro i ⟨hst, hmult⟩ hlow
    fin_cases i'''
i = s.index(old)
j = s.index("theorem apc2105000Opt_legalGuest")
new = '''  · -- The byte invariant, by static analysis: only the masked write is left by hand.
    refine byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
      asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

'''
s = s[:i] + new + s[j:]
open(p,'w').write(s)
PY
timeout 900 lake build ApcOptimizer.VmSpec.Audit.RealApcLegality 2>&1 | grep -A 14 "^error" | head -30

OUT
(Bash completed with no output)
Bash
IN
timeout 1800 lake build 2>&1 | grep -E "^(error|warning)" | head; echo "=== build ok"; timeout 1800 bash Scripts/check-proof-integrity.sh 2>&1 | tail -14

OUT
=== build ok
==> Checking sources for forbidden tactics/axioms
==> Checking axiom dependencies of the correctness theorems
'optimizerWithBusFacts_maintainsCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound]
'simpleOptimizer_maintainsCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApcOptimizer.OpenVM.openVmOptimizer_maintainsCorrectness' depends on axioms: [propext, Classical.choice, Quot.sound]
==> Checking for unused theorems (seeded by Scripts/unused-theorems.txt)
checked 7034 reachable constants from 4 seeded roots + 54 @[csimp] theorems; 218 ignored
Scripts/UnusedTheorems.lean:132:0: error: found 6 unused theorem(s) — not reachable from the roots in Scripts/unused-theorems.txt. Delete them, or add to that file's [ignore] section if genuinely used:
  ApcOptimizer/VmSpec/Audit/ByteCheck.lean:43  ApcOptimizer.OpenVM.isByte_of_isByteConst
  ApcOptimizer/VmSpec/Audit/ByteCheck.lean:49  ApcOptimizer.OpenVM.memShape_eval
  ApcOptimizer/VmSpec/Audit/ByteCheck.lean:127  ApcOptimizer.OpenVM.byteCheckAll_get
  ApcOptimizer/VmSpec/Audit/ByteCheck.lean:141  ApcOptimizer.OpenVM.byteCheckOne_sound
  ApcOptimizer/VmSpec/Audit/ByteCheck.lean:252  ApcOptimizer.OpenVM.byteCheck_sendsOk
  ApcOptimizer/VmSpec/Audit/RealApcLegality.lean:332  ApcOptimizer.OpenVM.optByteCheck
Bash
IN
python3 - <<'PY'
names = """ApcOptimizer.OpenVM.isByte_of_isByteConst
ApcOptimizer.OpenVM.memShape_eval
ApcOptimizer.OpenVM.byteCheckAll_get
ApcOptimizer.OpenVM.byteCheckOne_sound
ApcOptimizer.OpenVM.byteCheck_sendsOk
ApcOptimizer.OpenVM.optByteCheck""".split()
p='Scripts/unused-theorems.txt'
s=open(p).read()
anchor='ApcOptimizer.OpenVM.optBaseLin\n'
assert anchor in s
s=s.replace(anchor, anchor + '\n'.join(names) + '\n')
open(p,'w').write(s)
PY
timeout 1800 bash Scripts/check-proof-integrity.sh 2>&1 | tail -4; echo "=== diff:"; git diff --stat; git status --short

OUT
==> Checking for unused theorems (seeded by Scripts/unused-theorems.txt)
checked 7034 reachable constants from 4 seeded roots + 54 @[csimp] theorems; 224 ignored
OK: no unused theorems.
OK: proof integrity checks passed.
=== diff:
 ApcOptimizer/VmSpec/Audit/RealApcLegality.lean | 90 +++++++-------------------
 ApcOptimizer/VmSpec/Legal.lean                 | 30 ++++-----
 Scripts/unused-theorems.txt                    |  6 ++
 3 files changed, 43 insertions(+), 83 deletions(-)
 M ApcOptimizer/VmSpec/Audit/RealApcLegality.lean
 M ApcOptimizer/VmSpec/Legal.lean
 M Scripts/unused-theorems.txt
?? ApcOptimizer/VmSpec/Audit/ByteCheck.lean
Bash
IN
git add ApcOptimizer/VmSpec/Audit/ByteCheck.lean ApcOptimizer/VmSpec/Audit/RealApcLegality.lean Scripts/unused-theorems.txt && git commit -q -F - <<'EOF'
VmSpec: a real APC's byte invariant by static analysis

`StepLayout.sendsOk` asks that a stateful send's payload be `payloadOk`
given that everything the chip already touched is. Real chips justify
that in a small number of ways, and `Audit/ByteCheck.lean` decides four:
the interaction is not a stateful send at all; it is not on the memory
bus, where `openVmPayloadOk` asks nothing; its data limbs are literal
bytes; or its data limbs are an *earlier* interaction's, so `sendsOk`'s
own hypothesis supplies them -- a memory send echoing the read it just
did. A fifth (`external`) is left to the caller.

`byteCheck_sendsOk` turns a passing check into the clause, with the
`external` indices as its one obligation -- decidably vacuous at every
other index, so the caller's case analysis collapses to `all_goals try
exact absurd hi (by decide)`.

`apc2105000Opt`'s sixty-line `sendsOk` bullet becomes eight: a `decide`
over `optWitnesses`, and the masked write at position `9`, which is a
byte because the bitwise table says so and is where a decidable check
stops.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
EOF
git log --oneline -1

OUT
81cd00d VmSpec: a real APC's byte invariant by static analysis
Bash
IN
python3 - <<'PY'
p='agent-docs/legality-analysis.md'
s=open(p).read()
i=s.index('### Next, in cost order')
s = s[:i] + '''- **`Audit/ByteCheck.lean`** — `sendsOk`, OpenVM's byte invariant. Four justifications are
  decided: the interaction is not a stateful send; it is not on the memory bus, where
  `openVmPayloadOk` asks nothing; its data limbs are literal bytes; or its data limbs are an
  *earlier* interaction's, so `sendsOk`'s own hypothesis supplies them — a memory send echoing the
  read it just did. A fifth (`external`) is left to the caller, and is decidably vacuous at every
  other index, so the caller's case analysis collapses to one `try`.

  `apc2105000Opt`'s sixty-line `sendsOk` bullet is now eight: a `decide` over `optWitnesses`, and
  the masked write at position `9`.

### What is checked, and what is still by hand

For `apc2105000Opt`:

| clause | how |
| --- | --- |
| `recv` / `send` / `other` | `optBridgeCheck`, a `decide` |
| the five lt gadgets | `gadgetIdentity` (a `decide`) + `lookback_of_gadget` |
| `placed` | by hand — thirteen one-line bullets; the recipe machinery is proved but not wired |
| `ordered` | by hand — `optOffsetUb_dominates`, a `decide`; likewise not wired |
| `sendsOk` | `optByteCheck`, a `decide`, plus one case |

### Next, in cost order
''' + s[s.index('1. **Wiring `placed`/`ordered` through the recipes'):]

s = s.replace('''3. **`sendsOk`** — the byte invariant, and the largest piece. Three shapes appear in
   `apc2105000Opt`: a send echoing a preceding receive's data limbs (syntactic payload equality), a
   send directly range-checked (bus-fact lookup), and a send needing real reasoning (`a__0_2`, via
   `isByte_of_xorThree`). Most of the machinery exists in
   `Implementation/OptimizerPasses/BusPairCancelJustify.lean` — `denseByteJustifiedW` has literal /
   direct-bus-bound / deep-constraint / domain / affine / basis tiers, and its deep tier already
   enumerates one-hot flags, which is the ALU shape. Missing: the assumption set (conditional
   byte-ness: "given these receives are bytes, prove this send is"), output reshaping, and an
   `Expression`↔`DenseExpr` bridge.''',
'''3. **A tier for the `external` byte case** — the one shape `ByteCheck` does not decide: a limb
   that is a byte because a lookup table says so (`a__0_2`, via `isByte_of_xorThree`). Most of the
   machinery exists in `Implementation/OptimizerPasses/BusPairCancelJustify.lean` —
   `denseByteJustifiedW` has literal / direct-bus-bound / deep-constraint / domain / affine / basis
   tiers, and its deep tier already enumerates one-hot flags, which is the ALU shape. Missing: the
   assumption set (conditional byte-ness), output reshaping, and an `Expression`↔`DenseExpr`
   bridge.''')
open(p,'w').write(s)
PY
git add agent-docs && git commit -q -m "agent-docs: record the byte checker and what is left by hand

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>" && git log --oneline -3

OUT
9eb84df agent-docs: record the byte checker and what is left by hand
81cd00d VmSpec: a real APC's byte invariant by static analysis
f46556e agent-docs: record the recipe layer and what wiring it buys
sendsOk works. Build clean, integrity check passing.

The checker
Audit/ByteCheck.lean decides four justifications, one per interaction:


inductive ByteWitness where
  | notSend        -- not a stateful send: a lookup bus, or multiplicity ≠ 1
  | notMemory      -- not on the memory bus, where openVmPayloadOk asks nothing
  | limbs          -- its four data limbs are literal bytes
  | echo (j : ℕ)   -- its data limbs are interaction j's, and j precedes it and is active
  | external       -- the caller proves it
echo is the interesting one: it's how a real memory send is justified — it echoes the read it just did, so sendsOk's own hypothesis already vouches for the limbs. The check is dataLimbs pli == dataLimbs plj on normalized forms, so it sees through however powdr wrote the two payloads.

byteCheck_sendsOk turns a passing check into the clause with external as its one obligation. That obligation is decidably vacuous at every other index, so the caller's case analysis collapses to a single try:


· refine byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_
  intro i hi hsend hlow
  fin_cases i
  all_goals try exact absurd hi (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
    asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩
Sixty lines of hand proof became eight. The witness list is the whole certificate:


def optWitnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend
All 23 interactions check; only position 9 — the write masked by the bitwise table — is left by hand, and that's exactly where a decidable check should stop.

Where apc2105000Opt now stands
clause	how
recv / send / other	optBridgeCheck, a decide
the five lt gadgets	gadgetIdentity (decide) + lookback_of_gadget
placed	by hand — 13 one-line bullets; recipe machinery proved, not wired
ordered	by hand — optOffsetUb_dominates, a decide; not wired
sendsOk	optByteCheck, a decide, plus one case
RealApcLegality.lean is 83 lines shorter than when this started, despite gaining the gadget and witness certificates.

One thing worth flagging: extending optVars to cover the data limbs (a__0_0…a__3_1, a__0_2) grew the coefficient vectors from 12 to 21 entries, and every existing decide — the bridge check, the five gadget identities, optBaseLin — still passes at that width without a noticeable slowdown.

Your Legal.lean docstring edits are still uncommitted and untouched.

Legal.lean
record this progress---we'll want to go to a full automatic analysis later
then, clean out the audit surface---it has some theorems
Bash
IN
cat ApcOptimizer/README.md 2>/dev/null | head -60; echo "==="; find ApcOptimizer -maxdepth 1 -type d; echo "==="; find ApcOptimizer -maxdepth 2 -name "README.md"

OUT
===
ApcOptimizer
ApcOptimizer/Implementation
