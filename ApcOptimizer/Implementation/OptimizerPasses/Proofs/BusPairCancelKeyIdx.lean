import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelKeyIdx
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.AddrDiseqPre

set_option autoImplicit false

/-! # Soundness of the constant-key index and the combined region test

The key-index builder (`BusPairCancelKeyIdx.lean`) is complete and ordered
(`denseKeyIdxBuild_sound`), skipped positions are refuted by the bus-id or constant-key arm
(`denseAddrKeyOf_ne_*`), and `denseRegionTests` packages a sparse-scan decision together with the
proof converting it back to the full-region forms `denseMkDropResult` consumes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Skipped positions are refuted -/

/-- Over an arbitrary field list: two constant keys that differ force a slot whose constants
    differ, so the constant-disequality test fires. -/
theorem denseKeyFold_ne_any (S m : BusInteraction (DenseExpr p)) :
    ∀ (fields : List Nat) (kS km : List (ZMod p)),
      fields.foldr (fun slot acc =>
        match acc, (S.payload[slot]?).bind DenseExpr.constValue? with
        | some ks, some c => some (c :: ks)
        | _, _ => none) (some []) = some kS →
      fields.foldr (fun slot acc =>
        match acc, (m.payload[slot]?).bind DenseExpr.constValue? with
        | some ks, some c => some (c :: ks)
        | _, _ => none) (some []) = some km →
      kS ≠ km →
      fields.any (fun slot =>
        match S.payload[slot]?, m.payload[slot]? with
        | some e, some e' =>
          (match e.constValue?, e'.constValue? with
           | some c, some c' => decide (c ≠ c')
           | _, _ => false)
        | _, _ => false) = true := by
  intro fields
  induction fields with
  | nil =>
      intro kS km hS hm hne
      simp only [List.foldr_nil, Option.some.injEq] at hS hm
      exact absurd (hS.symm.trans hm) hne
  | cons slot rest ih =>
      intro kS km hS hm hne
      rw [List.foldr_cons] at hS hm
      cases hSr : (rest.foldr (fun slot acc =>
          match acc, (S.payload[slot]?).bind DenseExpr.constValue? with
          | some ks, some c => some (c :: ks)
          | _, _ => none) (some []) : Option (List (ZMod p))) with
      | none => rw [hSr] at hS; exact absurd hS (by simp)
      | some ksr =>
        cases hSc : (S.payload[slot]?).bind DenseExpr.constValue? with
        | none => rw [hSr, hSc] at hS; exact absurd hS (by simp)
        | some cS =>
          rw [hSr, hSc] at hS
          cases hmr : (rest.foldr (fun slot acc =>
              match acc, (m.payload[slot]?).bind DenseExpr.constValue? with
              | some ks, some c => some (c :: ks)
              | _, _ => none) (some []) : Option (List (ZMod p))) with
          | none => rw [hmr] at hm; exact absurd hm (by simp)
          | some kmr =>
            cases hmc : (m.payload[slot]?).bind DenseExpr.constValue? with
            | none => rw [hmr, hmc] at hm; exact absurd hm (by simp)
            | some cm =>
              rw [hmr, hmc] at hm
              simp only [Option.some.injEq] at hS hm
              rw [List.any_cons]
              by_cases hc : cS = cm
              · -- the head slot agrees, so the tails must differ
                have htne : ksr ≠ kmr := fun h => hne (by rw [← hS, ← hm, hc, h])
                rw [ih ksr kmr hSr hmr htne, Bool.or_true]
              · -- the head slot differs: its constants witness the disequality
                obtain ⟨eS, heS, heSc⟩ := Option.bind_eq_some_iff.mp hSc
                obtain ⟨em, hem, hemc⟩ := Option.bind_eq_some_iff.mp hmc
                have hhead : (match S.payload[slot]?, m.payload[slot]? with
                    | some e, some e' =>
                      (match e.constValue?, e'.constValue? with
                       | some c, some c' => decide (c ≠ c')
                       | _, _ => false)
                    | _, _ => false) = true := by
                  simp only [heS, hem, heSc, hemc]
                  exact decide_eq_true hc
                rw [hhead, Bool.true_or]

/-- Two constant keys that differ force a slot whose constants differ, so the constant
    disequality certificate fires. -/
theorem denseAddrKeyOf_ne_constsNeq (shape : MemoryBusShape)
    (S m : BusInteraction (DenseExpr p)) (kS km : List (ZMod p))
    (hS : denseAddrKeyOf shape S = some kS) (hm : denseAddrKeyOf shape m = some km)
    (hne : kS ≠ km) : denseAddrConstsNeq shape S m = true :=
  denseKeyFold_ne_any S m shape.addressFields kS km hS hm hne

/-- A cross-bus message is mid-refuted. -/
theorem denseMidRefuted_of_crossBus (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (h : m.busId ≠ busId) : denseMidRefuted ops shape T busId S m = true := by
  unfold denseMidRefuted
  rw [decide_eq_true h]
  simp

/-- A same-bus message with a different constant key is mid-refuted. -/
theorem denseMidRefuted_of_keyNe (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (kS km : List (ZMod p)) (hS : denseAddrKeyOf shape S = some kS)
    (hm : denseAddrKeyOf shape m = some km) (hne : kS ≠ km) :
    denseMidRefuted ops shape T busId S m = true := by
  unfold denseMidRefuted
  rw [denseAddrKeyOf_ne_constsNeq shape S m kS km hS hm hne]
  simp

/-- Skipped positions are pre-refuted (the shield's `P` test): `densePreRefuted` contains
    `denseMidRefuted` as its first disjunct. -/
theorem densePreRefuted_of_midRefuted (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (h : denseMidRefuted ops shape T busId S m = true) :
    densePreRefuted ops shape T busId S m = true := by
  unfold densePreRefuted
  rw [h]
  simp

/-! ## The builder is sound -/

/-- What the builder guarantees, all in one bundle: completeness (every same-bus position is in
    its key's bucket, or in `sym` when its key is not constant), and strict ascending order of
    every bucket and of `sym`. -/
structure DenseKeyIdx.Sound (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (idx : DenseKeyIdx p) : Prop where
  complete_key : ∀ pos m k, arr[pos]? = some m → m.busId = busId →
    denseAddrKeyOf shape m = some k → pos ∈ idx.byKey.getD (denseKeyHash k) []
  complete_sym : ∀ pos m, arr[pos]? = some m → m.busId = busId →
    denseAddrKeyOf shape m = none → pos ∈ idx.sym
  sorted_key : ∀ h, (idx.byKey.getD h []).Pairwise (· < ·)
  sorted_sym : idx.sym.Pairwise (· < ·)
  mem_key : ∀ h pos, pos ∈ idx.byKey.getD h [] → ∃ m k, arr[pos]? = some m ∧
    m.busId = busId ∧ denseAddrKeyOf shape m = some k ∧ denseKeyHash k = h
  mem_sym : ∀ pos, pos ∈ idx.sym → ∃ m, arr[pos]? = some m ∧ m.busId = busId ∧
    denseAddrKeyOf shape m = none

/-- The fold-step invariant: soundness for the positions processed so far, plus a lower bound
    keeping every stored position strictly above the positions still to be processed. -/
theorem denseKeyIdxBuild_sound_aux (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat), ps.Pairwise (· < ·) →
      (let idx := ps.foldr (denseKeyIdxAdd shape busId arr) ⟨∅, [], ∅, #[]⟩
       (∀ pos m k, pos ∈ ps → arr[pos]? = some m → m.busId = busId →
          denseAddrKeyOf shape m = some k → pos ∈ idx.byKey.getD (denseKeyHash k) []) ∧
       (∀ pos m, pos ∈ ps → arr[pos]? = some m → m.busId = busId →
          denseAddrKeyOf shape m = none → pos ∈ idx.sym) ∧
       (∀ h, (idx.byKey.getD h []).Pairwise (· < ·)) ∧
       idx.sym.Pairwise (· < ·) ∧
       (∀ h pos, pos ∈ idx.byKey.getD h [] → pos ∈ ps ∧ ∃ m k, arr[pos]? = some m ∧
          m.busId = busId ∧ denseAddrKeyOf shape m = some k ∧ denseKeyHash k = h) ∧
       (∀ pos, pos ∈ idx.sym → pos ∈ ps ∧ ∃ m, arr[pos]? = some m ∧ m.busId = busId ∧
          denseAddrKeyOf shape m = none)) := by
  intro ps hps
  induction ps with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Std.HashMap.getD_empty]
  | cons q rest ih =>
      have hqlt : ∀ r ∈ rest, q < r := fun r hr => (List.pairwise_cons.mp hps).1 r hr
      obtain ⟨ck, cs, sk, ss, mk, ms⟩ := ih (List.pairwise_cons.mp hps).2
      simp only [List.foldr_cons]
      set idx := rest.foldr (denseKeyIdxAdd shape busId arr) (⟨∅, [], ∅, #[]⟩ : DenseKeyIdx p) with hidx
      unfold denseKeyIdxAdd
      cases hq : arr[q]? with
      | none =>
          dsimp only
          refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_, sk, ss,
            fun h pos hpos => ?_, fun pos hpos => ?_⟩
          · rcases List.mem_cons.mp hpos with rfl | hpos
            · rw [hq] at hm; exact absurd hm (by simp)
            · exact ck pos m k hpos hm hb hk
          · rcases List.mem_cons.mp hpos with rfl | hpos
            · rw [hq] at hm; exact absurd hm (by simp)
            · exact cs pos m hpos hm hb hk
          · obtain ⟨hin, rest'⟩ := mk h pos hpos
            exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
          · obtain ⟨hin, rest'⟩ := ms pos hpos
            exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
      | some mq =>
          dsimp only
          by_cases hbq : mq.busId = busId
          · rw [if_pos hbq]
            cases hkq : denseAddrKeyOf shape mq with
            | some kq =>
                dsimp only
                refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_,
                  fun h => ?_, ss, fun h pos hpos => ?_, fun pos hpos => ?_⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    obtain rfl := Option.some.inj hk
                    rw [Std.HashMap.getD_insert_self]
                    exact List.mem_cons_self ..
                  · have hmem := ck pos m k hpos hm hb hk
                    by_cases hh : denseKeyHash kq = denseKeyHash k
                    · rw [← hh, Std.HashMap.getD_insert_self]
                      rw [← hh] at hmem
                      exact List.mem_cons_of_mem _ hmem
                    · rw [Std.HashMap.getD_insert,
                        if_neg (fun hc => hh (beq_iff_eq.mp hc))]
                      exact hmem
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    exact absurd hk (by simp)
                  · exact cs pos m hpos hm hb hk
                · by_cases hh : h = denseKeyHash kq
                  · subst hh
                    rw [Std.HashMap.getD_insert_self]
                    refine List.pairwise_cons.mpr ⟨fun r hr => ?_, sk _⟩
                    exact hqlt r (mk _ r hr).1
                  · rw [Std.HashMap.getD_insert,
                      if_neg (fun hc => hh (beq_iff_eq.mp hc).symm)]
                    exact sk h
                · by_cases hh : h = denseKeyHash kq
                  · subst hh
                    rw [Std.HashMap.getD_insert_self] at hpos
                    rcases List.mem_cons.mp hpos with rfl | hpos
                    · exact ⟨List.mem_cons_self .., mq, kq, hq, hbq, hkq, rfl⟩
                    · obtain ⟨hin, rest'⟩ := mk _ pos hpos
                      exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                  · rw [Std.HashMap.getD_insert,
                      if_neg (fun hc => hh (beq_iff_eq.mp hc).symm)] at hpos
                    obtain ⟨hin, rest'⟩ := mk h pos hpos
                    exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                · obtain ⟨hin, rest'⟩ := ms pos hpos
                  exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
            | none =>
                dsimp only
                refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_,
                  sk, ?_, fun h pos hpos => ?_, fun pos hpos => ?_⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    exact absurd hk (by simp)
                  · exact ck pos m k hpos hm hb hk
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _ (cs pos m hpos hm hb hk)
                · refine List.pairwise_cons.mpr ⟨fun r hr => ?_, ss⟩
                  exact hqlt r (ms r hr).1
                · obtain ⟨hin, rest'⟩ := mk h pos hpos
                  exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · exact ⟨List.mem_cons_self .., mq, hq, hbq, hkq⟩
                  · obtain ⟨hin, rest'⟩ := ms pos hpos
                    exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
          · rw [if_neg hbq]
            refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_, sk, ss,
              fun h pos hpos => ?_, fun pos hpos => ?_⟩
            · rcases List.mem_cons.mp hpos with rfl | hpos
              · rw [hq] at hm
                obtain rfl := Option.some.inj hm
                exact absurd hb hbq
              · exact ck pos m k hpos hm hb hk
            · rcases List.mem_cons.mp hpos with rfl | hpos
              · rw [hq] at hm
                obtain rfl := Option.some.inj hm
                exact absurd hb hbq
              · exact cs pos m hpos hm hb hk
            · obtain ⟨hin, rest'⟩ := mk h pos hpos
              exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
            · obtain ⟨hin, rest'⟩ := ms pos hpos
              exact ⟨List.mem_cons_of_mem _ hin, rest'⟩

theorem denseKeyIdxBuild_sound (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) :
    (denseKeyIdxBuild shape busId arr).Sound shape busId arr := by
  have hrange : (List.range arr.size).Pairwise (· < ·) := List.pairwise_lt_range
  obtain ⟨ck, cs, sk, ss, mk, ms⟩ :=
    denseKeyIdxBuild_sound_aux shape busId arr (List.range arr.size) hrange
  have hin : ∀ pos m, arr[pos]? = some m → pos ∈ List.range arr.size := by
    intro pos m hm
    rw [List.mem_range]
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hm
    exact absurd hm (by simp)
  exact ⟨fun pos m k hm hb hk => ck pos m k (hin pos m hm) hm hb hk,
    fun pos m hm hb hk => cs pos m (hin pos m hm) hm hb hk,
    sk, ss,
    fun h pos hpos => (mk h pos hpos).2,
    fun pos hpos => (ms pos hpos).2⟩

/-! ## The array-driven scans are sound

`denseRegionTests` no longer materializes a position list per candidate: the mid test walks the index
arrays with a window gate (`denseLiveAllGated`) and the shield walks them descending with an early
exit (`denseShieldEarly`). Two semantic lemmas turn what those walks establish into the full-region
forms `denseMkDropResult` consumes — per-position facts give the mid `all`
(`denseLiveAllSegP_true_of`), and per-position facts plus the position the shield stopped at give the
shield fold (`denseShieldScanSegP_true_of`). -/

/-- Per-position refutations give the segment `all`. -/
theorem denseLiveAllSegP_true_of {α : Type} (P : α → Bool) (preArr : Array α) (alive : Array Bool)
    (lo0 N : Nat)
    (h : ∀ q, lo0 ≤ q → q < N → alive[q]?.getD false = true →
      ∀ m, preArr[q]? = some m → P m = true) :
    ∀ (n lo : Nat), lo0 ≤ lo → lo + n ≤ N → denseLiveAllSegP preArr alive P lo n = true := by
  intro n
  induction n with
  | zero => intro lo _ _; rfl
  | succ n ih =>
    intro lo hlo hle
    rw [denseLiveAllSegP, Bool.and_eq_true]
    refine ⟨?_, ih (lo + 1) (by omega) (by omega)⟩
    cases halive : alive[lo]?.getD false with
    | false => rw [if_neg (by simp)]
    | true =>
      rw [if_pos rfl]
      cases hm : preArr[lo]? with
      | none => rfl
      | some m => exact h lo hlo (by omega) halive m hm

/-- The shield fold over `[lo, lo + n)` holds when every live position is refuted except possibly
    below a witness position `q0` that is itself a live provable receive. The `.1` conclusion (the
    fold's "a provable receive occurs later" flag) is what carries the witness leftwards. -/
theorem denseShieldScanSegP_true_aux {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) (q0 : Option Nat) (N : Nat)
    (hq0 : ∀ q ∈ q0, ∃ m, alive[q]?.getD false = true ∧ preArr[q]? = some m ∧
      P m = true ∧ Q m = true)
    (hab : ∀ q, q < N → (∀ r ∈ q0, r < q) → alive[q]?.getD false = true →
      ∀ m, preArr[q]? = some m → P m = true) :
    ∀ (n lo : Nat), lo + n ≤ N → (∀ r ∈ q0, r < lo + n) →
      (denseShieldScanSegP P Q preArr alive lo n).2 = true ∧
        ∀ r ∈ q0, lo ≤ r → (denseShieldScanSegP P Q preArr alive lo n).1 = true := by
  intro n
  induction n with
  | zero =>
    intro lo _ hlt
    exact ⟨rfl, fun r hr hle => by have := hlt r hr; omega⟩
  | succ n ih =>
    intro lo hle hlt
    obtain ⟨ih2, ih1⟩ := ih (lo + 1) (by omega) (fun r hr => by have := hlt r hr; omega)
    rw [denseShieldScanSegP]
    cases halive : alive[lo]?.getD false with
    | false =>
      rw [if_neg (by simp)]
      refine ⟨ih2, fun r hr hler => ?_⟩
      rcases Nat.lt_or_ge lo r with h | h
      · exact ih1 r hr (by omega)
      · have hrl : r = lo := by omega
        obtain ⟨m, hal, _, _, _⟩ := hq0 r hr
        rw [hrl, halive] at hal
        exact absurd hal (by simp)
    | true =>
      rw [if_pos rfl]
      cases hm : preArr[lo]? with
      | none =>
        refine ⟨ih2, fun r hr hler => ?_⟩
        rcases Nat.lt_or_ge lo r with h | h
        · exact ih1 r hr (by omega)
        · have hrl : r = lo := by omega
          obtain ⟨m, _, hme, _, _⟩ := hq0 r hr
          rw [hrl, hm] at hme
          exact absurd hme (by simp)
      | some m0 =>
        have hflag : ∀ r ∈ q0, lo ≤ r →
            ((denseShieldScanSegP P Q preArr alive (lo + 1) n).1 || Q m0) = true := by
          intro r hr hler
          rcases Nat.lt_or_ge lo r with h | h
          · rw [ih1 r hr (by omega)]; rfl
          · have hrl : r = lo := by omega
            obtain ⟨m, _, hme, _, hQm⟩ := hq0 r hr
            rw [hrl, hm] at hme
            obtain rfl := Option.some.inj hme
            rw [hQm, Bool.or_true]
        refine ⟨?_, hflag⟩
        dsimp only
        rw [ih2, Bool.true_and]
        by_cases hup : ∃ r ∈ q0, lo < r
        · obtain ⟨r, hr, hlt0⟩ := hup
          rw [ih1 r hr (by omega), Bool.or_true]
        · have hPm : P m0 = true := by
            cases hq0e : q0 with
            | none =>
              exact hab lo (by omega) (by intro r hr; rw [hq0e] at hr; exact absurd hr (by simp))
                halive m0 hm
            | some q =>
              by_cases hqlo : q = lo
              · obtain ⟨m, _, hme, hPm, _⟩ := hq0 q (by rw [hq0e]; exact rfl)
                rw [hqlo, hm] at hme
                obtain rfl := Option.some.inj hme
                exact hPm
              · refine hab lo (by omega) (fun r hr => ?_) halive m0 hm
                rw [hq0e] at hr
                have hrq : q = r := by simpa using hr
                have hnlt : ¬ lo < q := fun hc => hup ⟨q, by rw [hq0e]; exact rfl, hc⟩
                omega
          rw [hPm, Bool.true_or]

/-- The witness form of the shield fold over `[0, n)`. -/
theorem denseShieldScanSegP_true_of {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) (q0 : Option Nat) (n : Nat)
    (hq0 : ∀ q ∈ q0, ∃ m, alive[q]?.getD false = true ∧ preArr[q]? = some m ∧
      P m = true ∧ Q m = true)
    (hab : ∀ q, q < n → (∀ r ∈ q0, r < q) → alive[q]?.getD false = true →
      ∀ m, preArr[q]? = some m → P m = true)
    (hlt : ∀ r ∈ q0, r < n) :
    (denseShieldScanSegP P Q preArr alive 0 n).2 = true :=
  (denseShieldScanSegP_true_aux P Q preArr alive q0 n hq0 hab n 0 (by omega)
    (fun r hr => by simpa using hlt r hr)).1

/-! ### What the array walks establish -/

/-- Entries of an ascending array compare like their indices. -/
theorem denseArrEntry_le {a : Array Nat} (ha : a.toList.Pairwise (· < ·)) {k t q x : Nat}
    (hkt : k ≤ t) (hk : a[k]? = some q) (ht : a[t]? = some x) : q ≤ x := by
  rcases Nat.eq_or_lt_of_le hkt with rfl | hlt
  · rw [hk] at ht; exact Nat.le_of_eq (Option.some.inj ht)
  · have hks : k < a.size := by
      by_contra hc
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hk
      exact absurd hk (by simp)
    have hts : t < a.size := by
      by_contra hc
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at ht
      exact absurd ht (by simp)
    have hkl : k < a.toList.length := by simpa using hks
    have htl : t < a.toList.length := by simpa using hts
    have hkv : a.toList[k] = q := by
      have h := Array.getElem?_toList (xs := a) (i := k)
      rw [hk, List.getElem?_eq_getElem hkl] at h
      exact Option.some.inj h
    have htv : a.toList[t] = x := by
      have h := Array.getElem?_toList (xs := a) (i := t)
      rw [ht, List.getElem?_eq_getElem htl] at h
      exact Option.some.inj h
    have hpw := List.pairwise_iff_getElem.mp ha k t hkl htl hlt
    rw [hkv, htv] at hpw
    exact Nat.le_of_lt hpw

/-- A decided descending step: the position is in the window, live, and a provable receive whose
    `P` value is the verdict. -/
theorem denseShieldDecide_some {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    {bound pos : Nat} {v : Bool} (h : denseShieldDecide P Q preArr alive bound pos = some v) :
    pos < bound ∧ ∃ m, alive[pos]?.getD false = true ∧ preArr[pos]? = some m ∧ P m = v ∧
      (v = true → Q m = true) := by
  unfold denseShieldDecide at h
  split at h
  · rename_i hgate
    rw [Bool.and_eq_true, decide_eq_true_eq] at hgate
    split at h
    · rename_i m hme
      split at h
      · rename_i hP
        obtain rfl := Option.some.inj h
        exact ⟨hgate.1, m, hgate.2, hme, hP, fun hv => absurd hv (by simp)⟩
      · rename_i hP
        split at h
        · rename_i hQ
          obtain rfl := Option.some.inj h
          exact ⟨hgate.1, m, hgate.2, hme, hP, fun _ => hQ⟩
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- An undecided descending step: an in-window live position with a prepared record is `P`-refuted. -/
theorem denseShieldDecide_none {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    {bound pos : Nat} (h : denseShieldDecide P Q preArr alive bound pos = none) :
    pos < bound → alive[pos]?.getD false = true → ∀ m, preArr[pos]? = some m → P m = true := by
  intro hlt hal m hme
  by_contra hP
  have hPf : P m = false := by simpa using hP
  simp [denseShieldDecide, hme, hal, hlt, hPf] at h

/-- The descending early-exit shield over one segment: the position it stopped at is a live in-window
    provable receive, and every live in-window position above it is refuted. -/
theorem denseShieldEarlySeg_sound {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) (bound : Nat) :
    ∀ (n : Nat), denseShieldEarlySeg P Q preArr alive bound n = true →
      ∃ q0 : Option Nat,
        (∀ q ∈ q0, q < bound ∧ ∃ m, alive[q]?.getD false = true ∧ preArr[q]? = some m ∧
          P m = true ∧ Q m = true) ∧
        (∀ q, q < n → (∀ r ∈ q0, r < q) → q < bound → alive[q]?.getD false = true →
          ∀ m, preArr[q]? = some m → P m = true) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨none, by simp, fun q hq => absurd hq (by omega)⟩
  | succ n ih =>
    intro hw
    rw [denseShieldEarlySeg] at hw
    cases hd : denseShieldDecide P Q preArr alive bound n with
    | some v =>
      rw [hd] at hw
      obtain rfl : v = true := hw
      obtain ⟨hlt, m, hal, hme, hPm, hQm⟩ := denseShieldDecide_some P Q preArr alive hd
      refine ⟨some n, ?_, ?_⟩
      · intro q hq
        obtain rfl : n = q := by simpa using hq
        exact ⟨hlt, m, hal, hme, hPm, hQm rfl⟩
      · intro q hq hgt _ _ _ _
        have := hgt n (by simp)
        omega
    | none =>
      rw [hd] at hw
      obtain ⟨q0, hq0, habove⟩ := ih hw
      refine ⟨q0, hq0, fun q hq hgt hqb hal m hme => ?_⟩
      rcases Nat.lt_or_ge q n with h | h
      · exact habove q h hgt hqb hal m hme
      · obtain rfl : q = n := by omega
        exact denseShieldDecide_none P Q preArr alive hd hqb hal m hme

/-- The descending early-exit shield over the two index arrays: same conclusion, with the "above the
    witness" facts restricted to the arrays' entries (every other position is refuted by the
    key-index argument at the use site). -/
theorem denseShieldEarly_sound {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool)
    (b s : Array Nat) (bound : Nat)
    (hbs : b.toList.Pairwise (· < ·)) (hss : s.toList.Pairwise (· < ·)) :
    ∀ (fuel nb ns : Nat), nb + ns ≤ fuel → nb ≤ b.size → ns ≤ s.size →
      denseShieldEarly P Q preArr alive b s bound fuel nb ns = true →
      ∃ q0 : Option Nat,
        (∀ q ∈ q0, q < bound ∧ ∃ m, alive[q]?.getD false = true ∧ preArr[q]? = some m ∧
          P m = true ∧ Q m = true) ∧
        (∀ k q, k < nb → b[k]? = some q → (∀ r ∈ q0, r < q) → q < bound →
          alive[q]?.getD false = true → ∀ m, preArr[q]? = some m → P m = true) ∧
        (∀ k q, k < ns → s[k]? = some q → (∀ r ∈ q0, r < q) → q < bound →
          alive[q]?.getD false = true → ∀ m, preArr[q]? = some m → P m = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro nb ns hf _ _ _
    exact ⟨none, by simp, fun k q hk => absurd hk (by omega), fun k q hk => absurd hk (by omega)⟩
  | succ fuel ih =>
    intro nb ns hf hnb hns hw
    -- one shared step, instantiated by each of the four tail shapes
    have key : ∀ (pos nb' ns' : Nat), nb' + ns' + 1 = nb + ns → nb' ≤ b.size → ns' ≤ s.size →
        (∀ k q, k < nb → b[k]? = some q → q ≤ pos) →
        (∀ k q, k < ns → s[k]? = some q → q ≤ pos) →
        (∀ k q, k < nb → b[k]? = some q → k < nb' ∨ q = pos) →
        (∀ k q, k < ns → s[k]? = some q → k < ns' ∨ q = pos) →
        (match denseShieldDecide P Q preArr alive bound pos with
         | some v => v
         | none => denseShieldEarly P Q preArr alive b s bound fuel nb' ns') = true →
        ∃ q0 : Option Nat,
          (∀ q ∈ q0, q < bound ∧ ∃ m, alive[q]?.getD false = true ∧ preArr[q]? = some m ∧
            P m = true ∧ Q m = true) ∧
          (∀ k q, k < nb → b[k]? = some q → (∀ r ∈ q0, r < q) → q < bound →
            alive[q]?.getD false = true → ∀ m, preArr[q]? = some m → P m = true) ∧
          (∀ k q, k < ns → s[k]? = some q → (∀ r ∈ q0, r < q) → q < bound →
            alive[q]?.getD false = true → ∀ m, preArr[q]? = some m → P m = true) := by
      intro pos nb' ns' hcount hnb' hns' hleb hles hdropb hdrops hstep
      cases hd : denseShieldDecide P Q preArr alive bound pos with
      | some v =>
        rw [hd] at hstep
        obtain rfl : v = true := hstep
        obtain ⟨hlt, m, hal, hme, hPm, hQm⟩ := denseShieldDecide_some P Q preArr alive hd
        refine ⟨some pos, ?_, ?_, ?_⟩
        · intro q hq
          obtain rfl : pos = q := by simpa using hq
          exact ⟨hlt, m, hal, hme, hPm, hQm rfl⟩
        · intro k q hk hkq hgt _ _ _ _
          have h1 := hleb k q hk hkq
          have h2 := hgt pos (by simp)
          omega
        · intro k q hk hkq hgt _ _ _ _
          have h1 := hles k q hk hkq
          have h2 := hgt pos (by simp)
          omega
      | none =>
        rw [hd] at hstep
        obtain ⟨q0, hq0, habB, habS⟩ := ih nb' ns' (by omega) hnb' hns' hstep
        refine ⟨q0, hq0, ?_, ?_⟩
        · intro k q hk hkq hgt hqb hal m hme
          rcases hdropb k q hk hkq with h | rfl
          · exact habB k q h hkq hgt hqb hal m hme
          · exact denseShieldDecide_none P Q preArr alive hd hqb hal m hme
        · intro k q hk hkq hgt hqb hal m hme
          rcases hdrops k q hk hkq with h | rfl
          · exact habS k q h hkq hgt hqb hal m hme
          · exact denseShieldDecide_none P Q preArr alive hd hqb hal m hme
    rw [denseShieldEarly] at hw
    rcases Nat.eq_zero_or_pos nb with rfl | hnbp
    · rcases Nat.eq_zero_or_pos ns with rfl | hnsp
      · exact ⟨none, by simp, fun k q hk => absurd hk (by omega), fun k q hk => absurd hk (by omega)⟩
      · obtain ⟨ps, hps⟩ : ∃ ps, s[ns - 1]? = some ps :=
          ⟨s[ns - 1]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
        rw [if_neg (by omega), if_pos hnsp, hps] at hw
        dsimp only at hw
        exact key ps 0 (ns - 1) (by omega) (by omega) (by omega)
          (fun k q hk => absurd hk (by omega))
          (fun k q hk hkq => denseArrEntry_le hss (by omega) hkq hps)
          (fun k q hk => absurd hk (by omega))
          (fun k q hk hkq => by
            rcases Nat.lt_or_ge k (ns - 1) with h | h
            · exact Or.inl h
            · obtain rfl : k = ns - 1 := by omega
              exact Or.inr (Option.some.inj (hkq.symm.trans hps))) hw
    · obtain ⟨pb, hpb⟩ : ∃ pb, b[nb - 1]? = some pb :=
        ⟨b[nb - 1]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
      rcases Nat.eq_zero_or_pos ns with rfl | hnsp
      · rw [if_pos hnbp, hpb, if_neg (by omega)] at hw
        exact key pb (nb - 1) 0 (by omega) (by omega) (by omega)
          (fun k q hk hkq => denseArrEntry_le hbs (by omega) hkq hpb)
          (fun k q hk => absurd hk (by omega))
          (fun k q hk hkq => by
            rcases Nat.lt_or_ge k (nb - 1) with h | h
            · exact Or.inl h
            · obtain rfl : k = nb - 1 := by omega
              exact Or.inr (Option.some.inj (hkq.symm.trans hpb)))
          (fun k q hk => absurd hk (by omega)) hw
      · obtain ⟨ps, hps⟩ : ∃ ps, s[ns - 1]? = some ps :=
          ⟨s[ns - 1]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
        rw [if_pos hnbp, hpb, if_pos hnsp, hps] at hw
        dsimp only at hw
        by_cases hle : ps ≤ pb
        · rw [if_pos hle] at hw
          exact key pb (nb - 1) ns (by omega) (by omega) hns
            (fun k q hk hkq => denseArrEntry_le hbs (by omega) hkq hpb)
            (fun k q hk hkq => Nat.le_trans (denseArrEntry_le hss (by omega) hkq hps) hle)
            (fun k q hk hkq => by
              rcases Nat.lt_or_ge k (nb - 1) with h | h
              · exact Or.inl h
              · obtain rfl : k = nb - 1 := by omega
                exact Or.inr (Option.some.inj (hkq.symm.trans hpb)))
            (fun k q hk _ => Or.inl hk) hw
        · rw [if_neg hle] at hw
          exact key ps nb (ns - 1) (by omega) hnb (by omega)
            (fun k q hk hkq => Nat.le_of_lt (Nat.lt_of_le_of_lt
              (denseArrEntry_le hbs (by omega) hkq hpb) (by omega)))
            (fun k q hk hkq => denseArrEntry_le hss (by omega) hkq hps)
            (fun k q hk _ => Or.inl hk)
            (fun k q hk hkq => by
              rcases Nat.lt_or_ge k (ns - 1) with h | h
              · exact Or.inl h
              · obtain rfl : k = ns - 1 := by omega
                exact Or.inr (Option.some.inj (hkq.symm.trans hps))) hw

/-- The gated window walk: every live entry of the array inside the window is refuted. -/
theorem denseLiveAllGated_sound {α : Type} (P : α → Bool) (preArr : Array α) (alive : Array Bool)
    (a : Array Nat) (lo hi : Nat) :
    ∀ (n : Nat), denseLiveAllGated P preArr alive a lo hi n = true →
      ∀ k q, k < n → a[k]? = some q → lo ≤ q → q < hi → alive[q]?.getD false = true →
        ∀ m, preArr[q]? = some m → P m = true := by
  intro n
  induction n with
  | zero => intro _ k q hk; exact absurd hk (by omega)
  | succ n ih =>
    intro hw k q hk hkq hlo hhi hal m hme
    rw [denseLiveAllGated, Bool.and_eq_true] at hw
    rcases Nat.lt_or_ge k n with h | h
    · exact ih hw.2 k q h hkq hlo hhi hal m hme
    · obtain rfl : k = n := by omega
      have h1 := hw.1
      rw [hkq] at h1
      dsimp only at h1
      rw [if_pos (by rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq]; exact ⟨⟨hlo, hhi⟩, hal⟩), hme] at h1
      exact h1

/-- The index's arrays are the list buckets, entry for entry. -/
theorem denseKeyIdxBuild_byKeyA_getD (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (h : UInt64) :
    (denseKeyIdxBuild shape busId arr).byKeyA.getD h #[]
      = ((denseKeyIdxBuild shape busId arr).byKey.getD h []).toArray := by
  have hmap : (denseKeyIdxBuild shape busId arr).byKeyA
      = (denseKeyIdxBuild shape busId arr).byKey.map (fun _ l => l.toArray) := rfl
  rw [hmap, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?,
    Std.HashMap.getElem?_map]
  cases hm : (denseKeyIdxBuild shape busId arr).byKey[h]? with
  | none => simp
  | some l => simp

theorem denseKeyIdxBuild_symA (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) :
    (denseKeyIdxBuild shape busId arr).symA = (denseKeyIdxBuild shape busId arr).sym.toArray := rfl

/-! ## The combined region test

One decision for a candidate pair's mid and shield regions, sparse when the candidate's address
key is constant, with the scan results already converted to the forms `denseMkDropResult`
consumes. -/

/-- Decide both region tests for the candidate `S` at `i` with matched receive at `j`. With a
    constant candidate key the scans visit only the same-key bucket and the symbolic-key list;
    every skipped position is refuted by the bus-id or constant-key arm. -/
def denseRegionTests (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (preArr : Array (DenseAddrPre p))
    (hpre : preArr = arr.map (denseAddrPrep shape T.get.tworoot))
    (kIdx : DenseKeyIdx p) (hkIdx : kIdx = denseKeyIdxBuild shape busId arr)
    (S : BusInteraction (DenseExpr p)) (preS : DenseAddrPre p)
    (hpreS : preS = denseAddrPrep shape T.get.tworoot S)
    (i j : Nat) (hij : i < j) :
    { b : Bool // b = true →
      (∀ m0 ∈ denseLiveSeg arr alive (i + 1) (j - i - 1),
        denseMidRefuted ops shape T busId S m0 = true) ∧
      denseShieldOk ops shape T busId S (denseLiveSeg arr alive 0 i) = true } :=
  -- the mid `all` and the shield fold, converted to the forms `denseMkDropResult` consumes
  have hmidOf : denseLiveAllSegP preArr alive
      (denseMidRefutedP ops T.get.nonzero busId preS) (i + 1) (j - i - 1) = true →
      ∀ m0 ∈ denseLiveSeg arr alive (i + 1) (j - i - 1),
        denseMidRefuted ops shape T busId S m0 = true := by
    intro hmidB
    rw [hpre, denseLiveAllSegP_eq] at hmidB
    intro m0 hm0
    have h := List.all_eq_true.mp hmidB m0 hm0
    rw [hpreS] at h
    rwa [denseMidRefutedP_eq] at h
  have hshieldOf : (denseShieldScanSegP
      (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
      (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
      preArr alive 0 i).2 = true →
      denseShieldOk ops shape T busId S (denseLiveSeg arr alive 0 i) = true := by
    intro hshieldA
    rw [hpre, denseShieldScanSegP_eq] at hshieldA
    have hP : (fun m => densePreRefutedP ops T.get.nonzero busId
          (denseSetNewMult ops shape) preS (denseAddrPrep shape T.get.tworoot m))
        = densePreRefuted ops shape T busId S :=
      funext fun m => by rw [hpreS]; exact densePreRefutedP_eq ops shape T busId S m
    have hQ : (fun m => denseProvRecvP busId (denseGetPreviousMult ops shape) preS
          (denseAddrPrep shape T.get.tworoot m))
        = denseProvRecv ops shape busId S :=
      funext fun m => by rw [hpreS]; exact denseProvRecvP_eq ops shape T.get.tworoot busId S m
    rw [hP, hQ, denseShieldScanW_eq] at hshieldA
    exact hshieldA
  -- the prepared record at a position is the prepared record of the interaction there
  have hentry : ∀ q m0, arr[q]? = some m0 →
      preArr[q]? = some (denseAddrPrep shape T.get.tworoot m0) := by
    intro q m0 hq
    rw [hpre, Array.getElem?_map, hq]
    rfl
  have hentry' : ∀ q m, preArr[q]? = some m →
      ∃ m0, arr[q]? = some m0 ∧ m = denseAddrPrep shape T.get.tworoot m0 := by
    intro q m hm
    rw [hpre, Array.getElem?_map] at hm
    cases hq : arr[q]? with
    | none => rw [hq] at hm; exact absurd hm (by simp)
    | some m0 => rw [hq] at hm; exact ⟨m0, hq, (Option.some.inj hm).symm⟩
  match hkS : denseAddrKeyOf shape S with
  | none =>
      ⟨denseLiveAllSegP preArr alive
            (denseMidRefutedP ops T.get.nonzero busId preS) (i + 1) (j - i - 1)
          && denseShieldEarlySeg
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive i i, by
        intro hb
        rw [Bool.and_eq_true] at hb
        obtain ⟨q0, hq0, habove⟩ := denseShieldEarlySeg_sound
          (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
          (denseProvRecvP busId (denseGetPreviousMult ops shape) preS) preArr alive i i hb.2
        refine ⟨hmidOf hb.1, hshieldOf (denseShieldScanSegP_true_of _ _ preArr alive q0 i
          (fun q hq => (hq0 q hq).2)
          (fun q hqi hgt hal m hme => habove q hqi hgt hqi hal m hme)
          (fun r hr => (hq0 r hr).1))⟩⟩
  | some kS =>
      ⟨(denseLiveAllGated (denseMidRefutedP ops T.get.nonzero busId preS) preArr alive
              (kIdx.byKeyA.getD (denseKeyHash kS) #[]) (i + 1) j
              (kIdx.byKeyA.getD (denseKeyHash kS) #[]).size
            && denseLiveAllGated (denseMidRefutedP ops T.get.nonzero busId preS) preArr alive
              kIdx.symA (i + 1) j kIdx.symA.size)
          && denseShieldEarly
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive (kIdx.byKeyA.getD (denseKeyHash kS) #[]) kIdx.symA i
            ((kIdx.byKeyA.getD (denseKeyHash kS) #[]).size + kIdx.symA.size)
            (kIdx.byKeyA.getD (denseKeyHash kS) #[]).size kIdx.symA.size, by
        intro hb
        rw [Bool.and_eq_true, Bool.and_eq_true] at hb
        obtain ⟨⟨hmidB, hmidS⟩, hshieldB⟩ := hb
        have hsound := hkIdx ▸ denseKeyIdxBuild_sound shape busId arr
        -- the arrays are the buckets
        have hbA : kIdx.byKeyA.getD (denseKeyHash kS) #[]
            = (kIdx.byKey.getD (denseKeyHash kS) []).toArray := by
          rw [hkIdx]; exact denseKeyIdxBuild_byKeyA_getD shape busId arr _
        have hsA : kIdx.symA = kIdx.sym.toArray := by
          rw [hkIdx]; exact denseKeyIdxBuild_symA shape busId arr
        -- a list membership is an in-bounds array entry
        have hidxB : ∀ q, q ∈ kIdx.byKey.getD (denseKeyHash kS) [] →
            ∃ k, k < (kIdx.byKeyA.getD (denseKeyHash kS) #[]).size ∧
              (kIdx.byKeyA.getD (denseKeyHash kS) #[])[k]? = some q := by
          intro q hq
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
          have hkA : (kIdx.byKeyA.getD (denseKeyHash kS) #[])[k]? = some q := by
            rw [hbA, List.getElem?_toArray]; exact hk
          refine ⟨k, ?_, hkA⟩
          by_contra hc
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hkA
          exact absurd hkA (by simp)
        have hidxS : ∀ q, q ∈ kIdx.sym →
            ∃ k, k < kIdx.symA.size ∧ kIdx.symA[k]? = some q := by
          intro q hq
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
          have hkA : kIdx.symA[k]? = some q := by
            rw [hsA, List.getElem?_toArray]; exact hk
          refine ⟨k, ?_, hkA⟩
          by_contra hc
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hkA
          exact absurd hkA (by simp)
        -- every position is a bucket entry, a symbolic entry, or refuted by its key
        have hclass : ∀ q m0, arr[q]? = some m0 →
            q ∈ kIdx.byKey.getD (denseKeyHash kS) [] ∨ q ∈ kIdx.sym ∨
              denseMidRefuted ops shape T busId S m0 = true := by
          intro q m0 hq
          by_cases hbus : m0.busId = busId
          · cases hkm : denseAddrKeyOf shape m0 with
            | none => exact Or.inr (Or.inl (hsound.complete_sym q m0 hq hbus hkm))
            | some km =>
                by_cases hkeq : km = kS
                · exact Or.inl (hkeq ▸ hsound.complete_key q m0 km hq hbus hkm)
                · exact Or.inr (Or.inr (denseMidRefuted_of_keyNe ops shape T busId S m0 kS km hkS
                    hkm (fun h => hkeq h.symm)))
          · exact Or.inr (Or.inr (denseMidRefuted_of_crossBus ops shape T busId S m0 hbus))
        -- the mid region
        have hmidPos : ∀ q, i + 1 ≤ q → q < j → alive[q]?.getD false = true →
            ∀ m, preArr[q]? = some m →
              denseMidRefutedP ops T.get.nonzero busId preS m = true := by
          intro q hq1 hq2 hal m hme
          obtain ⟨m0, hq, rfl⟩ := hentry' q m hme
          rcases hclass q m0 hq with hin | hin | href
          · obtain ⟨k, hklt, hkq⟩ := hidxB q hin
            exact denseLiveAllGated_sound _ preArr alive _ (i + 1) j _ hmidB k q hklt hkq hq1 hq2
              hal _ hme
          · obtain ⟨k, hklt, hkq⟩ := hidxS q hin
            exact denseLiveAllGated_sound _ preArr alive _ (i + 1) j _ hmidS k q hklt hkq hq1 hq2
              hal _ hme
          · rw [hpreS, denseMidRefutedP_eq]; exact href
        -- the shield region
        obtain ⟨q0, hq0, habB, habS⟩ := denseShieldEarly_sound
          (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
          (denseProvRecvP busId (denseGetPreviousMult ops shape) preS) preArr alive
          (kIdx.byKeyA.getD (denseKeyHash kS) #[]) kIdx.symA i
          (by rw [hbA, List.toList_toArray]; exact hsound.sorted_key _)
          (by rw [hsA, List.toList_toArray]; exact hsound.sorted_sym)
          _ _ _ (by omega) (le_refl _) (le_refl _) hshieldB
        refine ⟨hmidOf (denseLiveAllSegP_true_of _ preArr alive (i + 1) j hmidPos (j - i - 1)
            (i + 1) (le_refl _) (by omega)), ?_⟩
        refine hshieldOf (denseShieldScanSegP_true_of _ _ preArr alive q0 i
          (fun q hq => (hq0 q hq).2) (fun q hqi hgt hal m hme => ?_) (fun r hr => (hq0 r hr).1))
        obtain ⟨m0, hq, rfl⟩ := hentry' q m hme
        rcases hclass q m0 hq with hin | hin | href
        · obtain ⟨k, hklt, hkq⟩ := hidxB q hin
          exact habB k q hklt hkq hgt hqi hal _ hme
        · obtain ⟨k, hklt, hkq⟩ := hidxS q hin
          exact habS k q hklt hkq hgt hqi hal _ hme
        · rw [hpreS, densePreRefutedP_eq]
          exact densePreRefuted_of_midRefuted ops shape T busId S m0 href⟩
end ApcOptimizer.Dense
