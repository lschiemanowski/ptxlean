import PoissonPTX.DotPublicationTrack
import PoissonPTX.DotCompletedInput

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- The shared base, lane number and accumulator at the first publication are
recovered from the same admitted input traversal, not supplied independently. -/
theorem publication_registers
    (whole : NativeFlow.Runs cfg ctx (program count left right output scratch) start events allIndices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (live : start.halted owner=false) (arena : ∀ thread, (ctx thread).arena=base)
    (sameInitial : (start.core.lanes owner).global=initial .global)
    (compatible : Visibility.Compatible initial events source)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : DotInput.Arrays (DotInput.setup (ctx owner) scratch (NativeFlow.lane start owner)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64)
    (earlierRun : NativeFlow.Runs cfg ctx (program count left right output scratch) start earlier earlierIndices before)
    (included : ∀ e∈earlier, e∈events) (atStore : (before.core.lanes owner).pc=22) :
    (before.core.lanes owner).regs 3=scratch ∧
    (before.core.lanes owner).regs 14=(ctx owner).lane.setWidth 64 ∧
    decode ((before.core.lanes owner).regs 8)=
      DotInput.partialSum (ctx owner) scratch (NativeFlow.lane start owner) count left right := by
  obtain ⟨ready,words,indices,input,done,saved,wordMem⟩ :=
    publication_input earlierRun aligned (entry owner) atStore
  have room := arrays_room arrays
  rw [arena owner] at room
  have scalar := admitted_input whole aligned entry arena sameInitial compatible input
    (fun a member => included _ (wordMem a member)) bounded apart room outputFits
  obtain ⟨result,stable⟩ := DotInput.input_correct scalar (entry owner) live done bounded arrays
  obtain ⟨_,_,_,_,_,_,_,baseReg,laneReg⟩ := stable
  refine ⟨?_,?_,?_⟩
  · rw [saved 3 (by decide) (by decide),baseReg]
    simp [DotInput.setup,assign,advance]
  · rw [saved 14 (by decide) (by decide),laneReg]
    simp [DotInput.setup,assign,advance]
  · rw [saved 8 (by decide) (by decide)]
    exact result

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
