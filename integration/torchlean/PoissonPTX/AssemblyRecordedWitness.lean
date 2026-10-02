import PoissonPTX.AssemblyBeforeStore
import PoissonPTX.ObservedReadWitness

namespace PtxTorchLean.Poisson.PTX.Assembly
open ObservedAddress

/-- Record a returning scalar execution using actual input bytes. The native
instruction order proves that every read precedes the sole output store. -/
theorem recorded_witness
    (run : Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s t)
    (ready : BeforeStore memory mask s) :
    ∃ words indices, Flow.Observed.Runs ctx (entryCode count offsets entries element mask boundary output) s words indices t ∧
      (∀ read∈words, read.data.store=false → read.space=.global ∧ read.data.value=read64 memory read.data.address) ∧
      (∀ read∈indices, read.value=read32 memory read.address) := by
  induction run with
  | nil => exact ⟨[],[],.nil,by simp,by simp⟩
  | @cons s middle t step rest ih =>
    obtain ⟨access,indexRecord,observed,wordValues,indexValues⟩ := Flow.Observed.step_read_witness step
    have wordInitial : ∀ read, access=some read → read.data.store=false →
        read.space=.global ∧ read.data.value=read64 memory read.data.address := by
      intro read eq load
      have one := observed
      rw [eq] at one
      obtain ⟨global,pc,_⟩ := word_site one load
      have mem : s.core.global=memory := ready (by cases mask <;> simp [pc])
      refine ⟨global,?_⟩
      have value := wordValues read eq load
      simpa only [global,PTX.State.memory,mem] using value
    have indexInitial : ∀ read, indexRecord=some read → read.value=read32 memory read.address := by
      intro read eq
      have one := observed
      rw [eq] at one
      obtain ⟨_,_,sites⟩ := index_site one
      have mem : s.core.global=memory := ready (by rcases sites with h|h|h|⟨enabled,h⟩ <;> cases mask <;> simp_all)
      rw [indexValues read eq,mem]
    obtain ⟨words,indices,tail,tailWords,tailIndices⟩ := ih (before_store_step observed ready)
    refine ⟨_,_,.cons observed tail,?_,?_⟩
    · intro read member load
      rcases List.mem_append.mp member with head | tail
      · exact wordInitial read (by simpa using head) load
      · exact tailWords read tail load
    · intro read member
      rcases List.mem_append.mp member with head | tail
      · exact indexInitial read (by simpa using head)
      · exact tailIndices read tail

end PtxTorchLean.Poisson.PTX.Assembly
