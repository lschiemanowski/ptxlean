import PoissonPTX.RestartVectorsInputs
import PoissonPTX.ObservedReadWitness

namespace PtxTorchLean.Poisson.PTX.RestartVectors
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {i : Fin n} {s t : Flow.State}

/-- Record an ordinary execution with actual loaded bits. The read-only inputs
remain intact throughout all actual local stores. -/
theorem Arena.recorded_witness (run : Flow.Runs (a.context i) a.program s t)
    (addresses : AddressReady (a.context i) (a.vector .source) (a.vector .r) (a.vector .diagonal)
      a.boundary (a.vector .z) (a.vector .p) s)
    (inputs : a.Inputs memory i s) :
    ∃ words indices, Flow.Observed.Runs (a.context i) a.program s words indices t ∧
      (∀ read∈words, read.data.store=false → read.space=.global ∧ read.data.value=read64 memory read.data.address) ∧
      (∀ read∈indices, read.value=read32 memory read.address) := by
  induction run with
  | nil => exact ⟨[],[],.nil,by simp,by simp⟩
  | @cons s middle t step rest ih =>
    obtain ⟨access,index,observed,wordValues,indexValues⟩ := Flow.Observed.step_read_witness step
    have wordInitial : ∀ read, access=some read → read.data.store=false →
        read.space=.global ∧ read.data.value=read64 memory read.data.address := by
      intro read eq load
      have one := eq ▸ observed
      have shape := a.access_shape (access_step one addresses)
      simp only [load,Bool.false_eq_true,↓reduceIte] at shape
      refine ⟨shape.1,?_⟩
      have value := wordValues read eq load
      simp only [shape.1,PTX.State.memory] at value
      rw [value]
      obtain ⟨field,input,address⟩ := shape.2
      rw [address]; exact inputs.1 field input
    have indexInitial : ∀ read, index=some read → read.value=read32 memory read.address := by
      intro read eq
      have one := eq ▸ observed
      have shape := index_step one addresses
      have address : read.address=a.base.toNat+a.boundary.toNat+i.val*4 := by
        rw [shape.2]
        exact a.boundary_address i
      rw [indexValues read eq,address]
      exact inputs.2
    obtain ⟨words,indices,tail,tailWords,tailIndices⟩ := ih (address_step observed addresses) (a.inputs_step observed addresses inputs)
    refine ⟨_,_,.cons observed tail,?_,?_⟩
    · intro read member load
      rcases List.mem_append.mp member with head | tail
      · exact wordInitial read (by simpa using head) load
      · exact tailWords read tail load
    · intro read member
      rcases List.mem_append.mp member with head | tail
      · exact indexInitial read (by simpa using head)
      · exact tailIndices read tail

end PtxTorchLean.Poisson.PTX.RestartVectors
