import PoissonPTX.DotPublicationRegisters
import PoissonPTX.DotPublicationAddress
import PoissonPTX.NativeFlowDecompose

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem publication_fetch : (program count left right output scratch)[22]?=
    some (.flow (.data (.data (.store64 .shared (.offset 2 0) (.reg 8))))) := by
  rw [show 22=20+2 by decide,tree_fetch (by decide)]
  rfl

/-- Each actual initial shared publication contains this thread's computed
rounded partial sum. Its input bytes come from the same admitted whole history;
the store operand is linked to that very input traversal by register tracking. -/
theorem publication_contents
    (whole : NativeFlow.Runs cfg ctx (program count left right output scratch) start events allIndices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (live : start.halted owner=false) (arena : ∀ thread, (ctx thread).arena=base)
    (sameInitial : (start.core.lanes owner).global=initial .global)
    (compatible : Visibility.Compatible initial events source)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : DotInput.Arrays (DotInput.setup (ctx owner) scratch (NativeFlow.lane start owner)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64)
    (member : Event.data owner access∈events) (store : access.data.store=true)
    (initialStore : access.data.pc=22) :
    access.space=.shared ∧
    access.data.address=(scratch+BitVec.ofNat 64 ((ctx owner).lane.toNat*8)).toNat ∧
    decode access.data.value=
      DotInput.partialSum (ctx owner) scratch (NativeFlow.lane start owner) count left right := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,earlierRun,one,observed,history⟩ :=
    NativeFlow.access_decompose whole member
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin one observed
  subst selected
  obtain ⟨sp,addr,src,opcode,shape⟩ := Flow.Observed.store_shape effect store
  have atStore : (before.core.lanes owner).pc=22 := by
    simpa only [shape,NativeFlow.lane] using initialStore
  rw [atStore,publication_fetch] at fetch
  have instruction : i=.data (.data (.store64 .shared (.offset 2 0) (.reg 8))) :=
    (NativeFlow.Instr.flow.inj (Option.some.inj fetch)).symm
  rw [instruction] at opcode
  cases opcode
  have included : ∀ e∈earlier, e∈events := by
    intro e belongs
    rw [history]
    exact List.mem_append_left _ (List.mem_append_left _ belongs)
  have registers := publication_registers whole aligned entry live arena sameInitial compatible
    bounded apart arrays outputFits earlierRun included atStore
  have value : access.data.value=(before.core.lanes owner).regs 8 :=
    congrArg (fun a : Access => a.data.value) shape
  have prepared := (publication_addresses earlierRun aligned entry owner).2 atStore
  have observedAddress : access.data.address=((before.core.lanes owner).regs 2).toNat := by
    have located := congrArg (fun a : Access => a.data.address) shape
    simpa [Operand.eval,NativeFlow.lane] using located
  have wideLane : wide (before.core.lanes owner) 14=BitVec.ofNat 64 ((ctx owner).lane.toNat*8) := by
    simp [wide,registers.2.1,Nat.mod_eq_of_lt (ctx owner).lane.isLt]
  refine ⟨congrArg Access.space shape,?_,by rw [value]; exact registers.2.2⟩
  simp only [NativeFlow.lane] at prepared
  rw [observedAddress,prepared,registers.1,wideLane]

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
