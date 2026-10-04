import PoissonPTX.UpdateXRZParallelExists
import PoissonPTX.RoundedLaunch
import PoissonPTX.ObservedRoundedSources

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ
open Concurrent

/-- A complete rounded launch exists for arbitrary input words. All physical
lanes execute, active lanes publish the proved values, and padding adds no
memory observations. Necessary source admission is retained. -/
theorem Arena.rounded_exists (a : Arena n) (memory : Memory) (regs : Fin (Rounded.count n) → Registers) :
    ∃ words indices final,
      Flow.Parallel.Runs (Rounded.context a.base) a.program (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) ∧
      Visibility.GlobalThreadSources words (fun _ _ => .initial) ∧
      ∀ field, field=Field.x ∨ field=Field.r ∨ field=Field.z → ∀ i,
        decode (read64 (GlobalPublication.publish memory words) (a.slot field i))=a.value memory field i := by
  obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,admitted,value⟩ :=
    a.parallel_exists memory (fun i => regs (i.castLE Rounded.enough))
  obtain ⟨result,run,halted,_⟩ := Rounded.run a.base a.small (fun t => a.start memory (regs t))
    (fun _ => rfl) (fun _ => rfl) actual done
  refine ⟨_,_,result,run,halted,Flow.Parallel.rename_compatible compatible,
    Flow.Parallel.rename_index_compatible indexCompatible,Visibility.initial_thread_sources,?_⟩
  simpa only [Flow.Parallel.rename_publication] using value

end PtxTorchLean.Poisson.PTX.UpdateXRZ
