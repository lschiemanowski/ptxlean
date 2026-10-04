import PoissonPTX.DotInputAdmitted

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem arrays_room
    (arrays : DotInput.Arrays (DotInput.setup ctx scratch s).core count left right) :
    ∀ off∈[left,right], ctx.arena.toNat+off.toNat+count*8≤2^64 := by
  intro off member
  have allocated := arrays.2.2.1
  have field := (arrays.2.2.2 off member).2
  have base := arrays.1
  simp [DotInput.setup,assign,advance] at base allocated field
  omega

/-- Every returned lane has performed the actual strided input calculation
from initialized input bytes. The source proof considers every store in the
complete interleaving, including the output epilogue. This still precedes the
separate proof connecting these partial sums through the concurrent tree. -/
theorem completed_input_correct
    (whole : NativeFlow.Runs cfg ctx (program count left right output scratch) start events allIndices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (live : start.halted owner=false) (returned : final.halted owner=true)
    (arena : ∀ thread, (ctx thread).arena=base)
    (sameInitial : (start.core.lanes owner).global=initial .global)
    (compatible : Visibility.Compatible initial events source)
    (bounded : count<2^30) (apart : OutputApart count left right output)
    (arrays : DotInput.Arrays (DotInput.setup (ctx owner) scratch (NativeFlow.lane start owner)).core count left right)
    (outputFits : base.toNat+output.toNat+8≤2^64) :
    ∃ next words indices,
      Flow.Observed.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
        (NativeFlow.lane start owner) words indices next ∧
      (∀ a∈words, Event.data owner a∈events) ∧
      Flow.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
        (NativeFlow.lane start owner) next ∧ next.core.pc=20 ∧ next.halted=false ∧
      decode (next.core.regs 8)=DotInput.partialSum (ctx owner) scratch (NativeFlow.lane start owner) count left right ∧
      DotInput.Stable (DotInput.setup (ctx owner) scratch (NativeFlow.lane start owner)).core next.core := by
  obtain ⟨next,words,indices,observed,done,stillLive,recorded,_⟩ :=
    completed_input whole aligned (entry owner) live returned
  have room := arrays_room arrays
  rw [arena owner] at room
  have scalar := admitted_input whole aligned entry arena sameInitial compatible observed recorded
    bounded apart room outputFits
  have result := DotInput.input_correct scalar (entry owner) live done bounded arrays
  exact ⟨next,words,indices,observed,recorded,scalar,done,stillLive,result⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
