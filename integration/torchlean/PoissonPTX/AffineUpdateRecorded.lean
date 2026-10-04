import PoissonPTX.AffineUpdateAccess
import PoissonPTX.ObservedReadWitness
import PoissonPTX.ObservedTemporalReplay
import PoissonPTX.ObservedPublication

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

/-- Until the sole store executes, all initial global bytes remain available.
This concerns the actual local trace, including arbitrary numerical inputs. -/
def BeforeStore (memory : Memory) (s : Flow.State) : Prop := s.core.pc≤23 → s.core.global=memory

theorem before_store_step (step : Flow.Observed.Step ctx (entry count coefficient input shift output) s t access index)
    (addresses : AddressReady ctx coefficient input shift output s)
    (ready : BeforeStore memory s) : BeforeStore memory t := by
  intro before
  have one := step
  obtain ⟨running,op,fetch,effect⟩ := one
  have pc := Flow.Observed.eval_linear_pc effect (entry_linear op (List.mem_of_getElem? fetch))
  have initial : s.core.global=memory := ready (by omega)
  rw [Flow.Observed.step_memory step]
  cases access with
  | none => exact initial
  | some a =>
    have shape := access_step step addresses
    have position := (Concurrent.NativeFlow.eval_access_pc effect).1
    simp only [Flow.Observed.applyAccess]
    split
    · rename_i write
      simp only [AccessAt,write.2,↓reduceIte] at shape
      omega
    · exact initial

/-- A scalar execution supplies candidate observations whose reads are actual
initial bytes. Every load precedes the in-place output write. -/
theorem recorded_witness (run : Flow.Runs ctx (entry count coefficient input shift output) s t)
    (addresses : AddressReady ctx coefficient input shift output s) (ready : BeforeStore memory s) :
    ∃ words indices, Flow.Observed.Runs ctx (entry count coefficient input shift output) s words indices t ∧
      (∀ read∈words, read.data.store=false → read.space=.global ∧ read.data.value=read64 memory read.data.address) ∧
      indices=[] := by
  induction run with
  | nil => exact ⟨[],[],.nil,by simp,rfl⟩
  | @cons s middle t step rest ih =>
    obtain ⟨access,index,observed,wordValues,indexValues⟩ := Flow.Observed.step_read_witness step
    have wordInitial : ∀ read, access=some read → read.data.store=false →
        read.space=.global ∧ read.data.value=read64 memory read.data.address := by
      intro read eq load
      have one := eq ▸ observed
      have shape := access_step one addresses
      simp only [AccessAt,load,Bool.false_eq_true,↓reduceIte] at shape
      obtain ⟨_,_,_,effect⟩ := one
      have position := (Concurrent.NativeFlow.eval_access_pc effect).1
      have mem : s.core.global=memory := ready (by rcases shape.2 with h|h|h <;> omega)
      refine ⟨shape.1,?_⟩
      have value := wordValues read eq load
      simpa only [shape.1,PTX.State.memory,mem] using value
    obtain ⟨words,indices,tail,tailWords,empty⟩ := ih (address_step observed addresses) (before_store_step observed addresses ready)
    refine ⟨_,_,.cons observed tail,?_,?_⟩
    · intro read member load
      rcases List.mem_append.mp member with head | tail
      · exact wordInitial read (by simpa using head) load
      · exact tailWords read tail load
    · simp [no_index_step observed,empty]

end PtxTorchLean.Poisson.PTX.AffineUpdate
