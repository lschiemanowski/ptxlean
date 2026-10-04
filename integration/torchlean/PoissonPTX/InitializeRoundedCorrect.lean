import PoissonPTX.InitializeRounded
import PoissonPTX.RoundedLaunchProjection

namespace PtxTorchLean.Poisson.PTX.Initialize
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
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot .rhs thread)=a.loadWord memory thread ∧
    read64 (GlobalPublication.publish memory words) (a.slot .r thread)=a.loadWord memory thread ∧
    decode (read64 (GlobalPublication.publish memory words) (a.slot .z thread))=a.quotient memory thread ∧
    read64 (GlobalPublication.publish memory words) (a.slot .p thread)=read64 (GlobalPublication.publish memory words) (a.slot .z thread) ∧
    read64 (GlobalPublication.publish memory words) (a.slot .x thread)=0 := by
  obtain ⟨sameWords,sameIndices⟩ := Rounded.history a.small run (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  have activeCompatible := Flow.Parallel.unrename_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=n))) (words:=words.filterMap (Flow.Parallel.restrictEvent n))
    (by rw [sameWords]; exact compatible)
  have activeIndices := Flow.Parallel.unrename_index_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=n))) (words:=words.filterMap (Flow.Parallel.restrictEvent n))
    (indices:=indices.filterMap (Flow.Parallel.restrictIndex n))
    (by rw [sameWords,sameIndices]; exact indexCompatible)
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact a.parallel_correct activeRun activeCompatible activeIndices (fun i => done (i.castLE Rounded.enough)) thread

/-- A completed rounded launch preserves every byte outside its actual output arrays. -/
theorem Arena.rounded_outside {byte : Nat}
    (run : Flow.Parallel.Runs (Rounded.context a.base) a.program (fun i => a.start memory (regs i)) words indices t)
    (done : ∀ i, (t i).halted=true)
    (outside : ∀ f, f=Field.rhs ∨ f=Field.r ∨ f=Field.z ∨ f=Field.p ∨ f=Field.x →
      byte<a.base.toNat+(a.vector f).toNat ∨ a.base.toNat+(a.vector f).toNat+n*8≤byte) :
    GlobalPublication.publish memory words byte=memory byte := by
  obtain ⟨sameWords,_⟩ := Rounded.history a.small run (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact a.publication_outside activeRun outside

end PtxTorchLean.Poisson.PTX.Initialize
