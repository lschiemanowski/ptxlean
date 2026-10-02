import PoissonPTX.AssemblyParallelStores
import PoissonPTX.GlobalPublication

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Actual assembly stores cannot change a disjoint input word. Their addresses
follow from fetched execution, independently of proposed read values. -/
theorem Arena.parallel_preserves_word (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices final)
    (address : Nat)
    (apart : ∀ thread : Fin n, Sources.Disjoint (a.base.toNat+a.output.toNat+thread.val*8) address) :
    read64 (Concurrent.GlobalPublication.publish memory words) address=read64 memory address := by
  apply Sources.word_eq_of_bytes
  intro k
  simp only [Sources.byte_read64]
  apply Concurrent.GlobalPublication.outside
  intro owner access member global store
  have exactAddress := (a.parallel_store memory regs run member store).2
  rw [exactAddress]
  have disjoint := apart owner
  unfold Sources.Disjoint at disjoint
  have bound := k.isLt
  omega

end PtxTorchLean.Poisson.PTX.Assembly
