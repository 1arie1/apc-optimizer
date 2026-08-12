import ApcOptimizer.VmSpecConnection
import ApcOptimizer.VmSpecOpenVm

set_option autoImplicit false

/-! Discharging `VmSpecConnection.lean`'s host-side conditions for the concrete `openVmHost`.

    `Host.sinksAreTables` is the manuscript's "each table sink implements its bus's predicate",
    and for `openVmHost` it comes down to a case split over the eight host chips: the four lookup
    chips restate `OpenVM.accepts`'s own conditions, and the four memory-bus chips cannot touch a
    *stateless* message at all, so they are vacuous here. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- A message `busStateOf` gives a nonzero net multiplicity is carried by one of its
    interactions. -/
theorem exists_of_busStateOf_ne_zero {msgs : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : busStateOf msgs m ≠ 0) : ∃ msg ∈ msgs, (msg.busId, msg.payload) = m := by
  by_contra hcon
  refine h (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  exact absurd ⟨y, hy1, of_decide_eq_true hy2⟩ hcon

theorem OutputRead.interactions_busId (r : OutputRead p) (memBusId : Nat) :
    ∀ msg ∈ r.interactions memBusId, msg.busId = memBusId := by
  intro msg hmsg
  obtain ⟨⟨i, w⟩, -, rfl⟩ := List.mem_map.mp hmsg
  rfl

theorem InputRead.interactions_busId (r : InputRead p) (ptrReg countReg memBusId : Nat) :
    ∀ msg ∈ r.interactions ptrReg countReg memBusId, msg.busId = memBusId := by
  intro msg hmsg
  rw [InputRead.interactions, List.mem_append] at hmsg
  rcases hmsg with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨⟨i, b, old⟩, -, h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl

/-- **`openVmHost`'s table sinks are honest.** Each of the four lookup chips restates its bus's
    case of `OpenVM.accepts`, and the four memory-bus chips cannot carry a stateless message at
    all, so they are vacuous.

    With `forcesAccepts_of_sinksAreTables`, this makes `Host.forcesAccepts` hold for a concrete
    OpenVM host — the condition that was outright false before `VmSat` gained its trace budget. -/
theorem openVmHost_sinksAreTables (maxInstances ptrReg countReg : ℕ) :
    (openVmHost (p := p) maxInstances ptrReg countReg 1).sinksAreTables
      (openVmBusSemantics p defaultBusMap) := by
  rintro hA hlegal ⟨mb, ml⟩ hm hnet mult hmult
  obtain ⟨t, c, hc, hcm⟩ := exists_instance_of_hostNet_ne_zero hnet
  have hleg := hlegal.1 t c hc
  show ApcOptimizer.OpenVM.accepts defaultBusMap _
  fin_cases t
  -- PC lookup: arity only, exactly as `OpenVM.accepts` has it.
  · obtain ⟨hbus, hlen⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]; exact hlen
  -- The three remaining tables: the chip's payload predicate *is* `accepts`'s case for that bus,
  -- so once the payload is split to the right arity both sides are the same proposition.
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨op, _ | ⟨w, rest⟩⟩⟩⟩⟩ <;> exact id
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  -- Memory init/finalize pin the bus id directly; the message would have to be stateful.
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  -- Output/input are pinned to an exact witness, every interaction of which is on the memory bus.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    have hbus : mb = 1 :=
      (congrArg Prod.fst heq).symm.trans (OutputRead.interactions_busId r 1 msg hmsg)
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    have hbus : mb = 1 :=
      (congrArg Prod.fst heq).symm.trans
        (InputRead.interactions_busId r ptrReg countReg 1 msg hmsg)
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm

/-- `Host.forcesAccepts`, discharged for a concrete OpenVM host. -/
theorem openVmHost_forcesAccepts [Fact p.Prime] (maxInstances ptrReg countReg : ℕ) :
    (openVmHost (p := p) maxInstances ptrReg countReg 1).forcesAccepts
      (openVmBusSemantics p defaultBusMap) :=
  forcesAccepts_of_sinksAreTables (openVmHost_sinksAreTables maxInstances ptrReg countReg)

end ApcOptimizer.OpenVM
