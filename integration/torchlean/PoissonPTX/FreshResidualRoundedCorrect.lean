import PoissonPTX.FreshResidualRounded
import PoissonPTX.RoundedLaunchProjection

namespace PtxTorchLean.Poisson.PTX.FreshResidual
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin (Rounded.count n) → Registers}
  {t : Fin (Rounded.count n) → Flow.State} {words : List (Event (Rounded.count n))}
  {indices : List (Fin (Rounded.count n) × IndexSources.Access)}

/-- Universal numerical publication for a completed admitted rounded launch.
The actual inactive guards eliminate padding records; arbitrary interleavings
retain the existing active-coordinate result and floating-point policy. -/
theorem Arena.rounded_correct
    (run : Flow.Parallel.Runs (Rounded.context a.base) a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    decode (read64 (GlobalPublication.publish memory words) (a.slot a.output thread))=a.value memory thread := by
  obtain ⟨sameWords,sameIndices⟩ := Rounded.history a.small (by rw [← entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  have activeCompatible := Flow.Parallel.unrename_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=n))) (words:=words.filterMap (Flow.Parallel.restrictEvent n))
    (by rw [sameWords]; exact compatible)
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact a.parallel_value activeRun activeCompatible (fun i => done (i.castLE Rounded.enough)) thread

/-- A completed rounded launch preserves every byte outside its actual output arrays. -/
theorem Arena.rounded_outside
    (run : Flow.Parallel.Runs (Rounded.context a.base) a.program (fun i => a.start memory (regs i)) words indices t)
    (done : ∀ i, (t i).halted=true)
    (outside : p<a.base.toNat+a.output.toNat ∨ a.base.toNat+a.output.toNat+n*8≤p) :
    GlobalPublication.publish memory words p=memory p := by
  obtain ⟨sameWords,_⟩ := Rounded.history a.small (by rw [← entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact a.publication_outside activeRun outside

end PtxTorchLean.Poisson.PTX.FreshResidual
