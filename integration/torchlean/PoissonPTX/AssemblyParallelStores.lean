import PoissonPTX.AssemblyObservedStores
import PoissonPTX.ObservedParallelReplay
import PoissonPTX.AssemblyArenaSafety

namespace PtxTorchLean.Poisson.PTX.Assembly
variable {n : Nat} {contexts : Fin n → Kernel.Context} {s t : Fin n → Flow.State}
  {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- All recorded stores in any interleaving have their owner's actual output
address. Neither source compatibility nor read values are needed for this. -/
theorem parallel_stores (run : Flow.Parallel.Runs contexts
    (entryCode count offsets entries element mask boundary output) s words indices t)
    (pc : ∀ thread, (s thread).core.pc=0)
    (member : Concurrent.Event.data thread access∈words) (store : access.data.store=true) :
    access.space=.global ∧ access.data.address=(address64 (contexts thread).arena (Kernel.Residual.index (contexts thread)) output).toNat :=
  ObservedAddress.stores (Flow.Parallel.project run thread) (ObservedAddress.initial (pc thread)) access
    (Flow.Parallel.word_member.mpr member) store

/-- For the physical active-lane launch, recorded store ownership reduces to
nonwrapping, disjoint eight-byte node slots. -/
theorem Arena.parallel_store (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (member : Concurrent.Event.data thread access∈words) (store : access.data.store=true) :
    access.space=.global ∧ access.data.address=a.base.toNat+a.output.toNat+thread.val*8 := by
  obtain ⟨global,address⟩ := parallel_stores run (fun _ => rfl) member store
  constructor
  · exact global
  · rw [address]
    change (address64 a.base (Kernel.Residual.index (a.context thread)) a.output).toNat=_
    rw [address64_exact _ _ _ (by rw [a.index]; have := a.outputFit; have := a.noWrap; have := thread.isLt; omega),a.index]
    omega

/-- Distinct threads' actual writes are disjoint independently of candidate
load bits, instruction interleaving and floating-point output encodings. -/
theorem Arena.parallel_owners (a : Arena n) (memory : Memory) (regs : Fin n → Registers)
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (left : Concurrent.Event.data i one∈words) (leftStore : one.data.store=true)
    (right : Concurrent.Event.data j two∈words) (rightStore : two.data.store=true) (different : i≠j) :
    Sources.Disjoint one.data.address two.data.address := by
  rw [(a.parallel_store memory regs run left leftStore).2,(a.parallel_store memory regs run right rightStore).2]
  exact a.owners i j different

end PtxTorchLean.Poisson.PTX.Assembly
