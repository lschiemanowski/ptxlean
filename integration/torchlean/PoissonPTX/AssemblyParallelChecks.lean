import PoissonPTX.AssemblyParallelExists
import PoissonPTX.AssemblyArenaChecks

namespace PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks
open ArenaChecks

theorem separated : arena.InputSeparation := by constructor <;> unfold Arena.FieldApart <;> decide +kernel

/-- Both nonzero rows have admitted returning joint executions. With the
boundary mask enabled, only the marked node changes to zero. These outputs
follow from the general actual-history theorem, not a supplied output trace. -/
theorem nonzero_admitted (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs arena.context (entryCode 2 64 0 32 mask 80 96)
        (fun _ => arena.start memory (fun _ => 0)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible memory words indices (fun _ _ => .initial) ∧
      decode (read64 (Concurrent.GlobalPublication.publish memory words) 4192)=5 ∧
      decode (read64 (Concurrent.GlobalPublication.publish memory words) 4200)=(if mask then 0 else 4) := by
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible,correct⟩ :=
    arena.parallel_exists_correct memory (fun _ _ => 0) contents separated mask
  refine ⟨words,indices,final,run,done,compatible,indexCompatible,?_,?_⟩
  · have value := correct 0
    change decode (read64 _ 4192)=_ at value
    rw [value]
    cases mask
    · exact values.1
    · exact values.2.2.1
  · have value := correct 1
    change decode (read64 _ 4200)=_ at value
    rw [value]
    cases mask
    · exact values.2.1
    · exact values.2.2.2

/-- Separation permits an input field above the output vector, as in the
emitted host arena. It rejects an input overlapping either output word. -/
theorem separation_cases : arena.FieldApart 112 24 ∧ ¬arena.FieldApart 100 8 := by
  constructor <;> unfold Arena.FieldApart <;> decide +kernel

end PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks
