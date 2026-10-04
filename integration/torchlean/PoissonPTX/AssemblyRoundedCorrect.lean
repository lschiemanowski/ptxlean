import PoissonPTX.AssemblyRoundedExists
import PoissonPTX.RoundedLaunchProjection

namespace PtxTorchLean.Poisson.PTX.Assembly
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin (Rounded.count n) → Registers}
  {t : Fin (Rounded.count n) → Flow.State} {words : List (Concurrent.Event (Rounded.count n))}
  {indices : List (Fin (Rounded.count n) × IndexSources.Access)}

/-- Universal assembly publication for the full rounded launch. -/
theorem Arena.rounded_value
    (run : Flow.Parallel.Runs (Rounded.context a.base)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a thread))=
      a.value memory thread mask := by
  obtain ⟨sameWords,sameIndices⟩ := Rounded.history a.small
    (by rw [← entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  have activeCompatible := Flow.Parallel.unrename_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=n))) (words:=words.filterMap (Flow.Parallel.restrictEvent n))
    (by rw [sameWords]; exact compatible)
  have activeIndices := Flow.Parallel.unrename_index_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=n))) (words:=words.filterMap (Flow.Parallel.restrictEvent n))
    (indices:=indices.filterMap (Flow.Parallel.restrictIndex n))
    (by rw [sameWords,sameIndices]; exact indexCompatible)
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact a.parallel_value activeRun activeCompatible activeIndices contents separated
    (fun i => done (i.castLE Rounded.enough)) thread

/-- The rounded assembly launch writes only its actual n output words. -/
theorem Arena.rounded_outside {byte : Nat}
    (run : Flow.Parallel.Runs (Rounded.context a.base)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (done : ∀ i, (t i).halted=true)
    (outside : byte<a.base.toNat+a.output.toNat ∨ a.base.toNat+a.output.toNat+n*8≤byte) :
    Concurrent.GlobalPublication.publish memory words byte=memory byte := by
  obtain ⟨sameWords,_⟩ := Rounded.history a.small
    (by rw [← entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  rw [← sameWords,Flow.Parallel.rename_publication]
  apply Concurrent.GlobalPublication.outside
  intro owner access member global store
  rw [(a.parallel_store memory (fun i => regs (i.castLE Rounded.enough)) activeRun member store).2]
  have := owner.isLt
  omega

end PtxTorchLean.Poisson.PTX.Assembly
