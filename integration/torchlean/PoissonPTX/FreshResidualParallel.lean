import PoissonPTX.FreshResidualArena
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.FreshResidual
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

def Arena.value (a : Arena n) (memory : Memory) (i : Fin n) : Float :=
  decode (read64 memory (a.slot a.rhs i))-decode (read64 memory (a.slot a.ap i))

theorem Arena.separated
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t) :
    Flow.Parallel.Separate words indices := by
  constructor
  · intro writer wa written store reader ra readmem read same
    have write := a.parallel_access run written
    have load := a.parallel_access run readmem
    simp only [store,↓reduceIte] at write
    simp only [read,Bool.false_eq_true,↓reduceIte] at load
    rw [write.2]
    rcases load.2 with rhs|ap
    · rw [rhs]; exact a.separate writer reader a.rhs (by simp)
    · rw [ap]; exact a.separate writer reader a.ap (by simp)
  · intro writer wa written store global reader ra readmem
    rw [a.indices_empty run] at readmem
    simp at readmem

theorem Arena.publication
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot a.output thread)=
      read64 (t thread).core.global (a.slot a.output thread) := by
  apply Flow.Parallel.publication_word run rfl
  intro owner access member different global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  rw [write.2]
  exact a.owners thread owner (Ne.symm different)

theorem Arena.local_value {regs : Registers}
    (run : Flow.Runs (a.context i) a.program (a.start memory regs) final) (done : final.halted=true) :
    decode (read64 final.core.global (a.slot a.output i))=a.value memory i := by
  have result := entry_correct run rfl rfl done (a.live i)
    (a.valid i a.rhs (by simp)) (a.valid i a.ap (by simp)) (a.valid i a.output (by simp))
  change decode (read64 final.core.global (address64 a.base (Kernel.Residual.index (a.context i)) a.output).toNat)=
    decode (read64 memory (address64 a.base (Kernel.Residual.index (a.context i)) a.rhs).toNat)-
    decode (read64 memory (address64 a.base (Kernel.Residual.index (a.context i)) a.ap).toNat) at result
  simpa only [Arena.value,a.address i a.rhs (by simp),a.address i a.ap (by simp),a.address i a.output (by simp)] using result


/-- Every completed source-compatible interleaving publishes the separately
rounded subtraction of the actual initial input words. -/
theorem Arena.parallel_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    decode (read64 (GlobalPublication.publish memory words) (a.slot a.output thread))=a.value memory thread := by
  have indexCompatible : IndexSources.Compatible memory words indices (fun _ _ => .initial) := by
    rw [a.indices_empty run]; intro r reader read located; simp at located
  rw [a.publication run thread]
  exact a.local_value (Flow.Parallel.replay run compatible indexCompatible (a.separated run) (fun _ => rfl) thread) (done thread)

theorem Arena.publication_outside {byte : Nat}
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (outside : byte<a.base.toNat+a.output.toNat ∨ a.base.toNat+a.output.toNat+n*8≤byte) :
    GlobalPublication.publish memory words byte=memory byte := by
  apply GlobalPublication.outside
  intro owner access member global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  rw [write.2]
  unfold Arena.slot
  have := owner.isLt
  omega

end PtxTorchLean.Poisson.PTX.FreshResidual
