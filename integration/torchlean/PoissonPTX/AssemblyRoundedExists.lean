import PoissonPTX.AssemblyParallelExists
import PoissonPTX.AssemblyRoundedProgram
import PoissonPTX.ObservedRoundedSources

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Include every rounded hardware lane in the actual admitted assembly run,
retaining the ordered row sums and optional boundary mask. -/
theorem Arena.rounded_exists (a : Arena n) (memory : Memory) (regs : Fin (Rounded.count n) → Registers)
    (contents : a.Contents memory) (separated : a.InputSeparation) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs (Rounded.context a.base)
        (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
        (fun i => a.start memory (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) ∧
      ∀ i, decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a i))=a.value memory i mask := by
  obtain ⟨words,indices,final,actual,done,compatible,indexCompatible,value⟩ :=
    a.parallel_exists_correct memory (fun i => regs (i.castLE Rounded.enough)) contents separated mask
  obtain ⟨result,run,halted,_⟩ := Rounded.run a.base a.small (fun t => a.start memory (regs t))
    (fun _ => rfl) (fun _ => rfl) (by rw [← entry_guarded]; exact actual) done
  refine ⟨_,_,result,by rw [entry_guarded]; exact run,halted,
    Flow.Parallel.rename_compatible compatible,Flow.Parallel.rename_index_compatible indexCompatible,?_⟩
  simpa only [Flow.Parallel.rename_publication] using value

end PtxTorchLean.Poisson.PTX.Assembly
