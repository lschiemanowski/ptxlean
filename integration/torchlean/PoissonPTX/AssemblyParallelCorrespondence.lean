import PoissonPTX.AssemblyParallelReplay
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.Assembly
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- The actual joint store history publishes each thread's actual final output
word. Ownership alone establishes this; numerical correspondence comes next. -/
theorem Arena.parallel_publication
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t) (thread : Fin n) :
    read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a thread)=
      read64 (t thread).core.global (Snapshot.address a thread) := by
  apply Flow.Parallel.publication_word run rfl
  intro owner access member different global store
  rw [(a.parallel_store memory regs run member store).2]
  rcases a.owners thread owner (Ne.symm different) with left | right
  · exact Or.inl left
  · exact Or.inr right

/-- Universal assembly correspondence for an actual completed interleaving.
All source assignments refer to that same history. Input layout, separated
fields and valid initial index bytes imply the ordered rounded row sum at each
published node, with the emitted optional boundary mask. -/
theorem Arena.parallel_value
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a thread))=
      a.value memory thread mask := by
  rw [a.parallel_publication run thread]
  exact (Snapshot.written (a.finished run compatible indexCompatible contents separated done) contents thread).2

/-- Ordered mesh representation is an input condition on the serialized index
lists. The result is computed by the actual jointly observed assembly launch. -/
theorem Arena.parallel_scatter
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation)
    (done : ∀ i, (t i).halted=true)
    (locations : List (Nat × Nat)) (represented : ∀ i, a.row memory i=Rows.selected locations i.val)
    (thread : Fin n) :
    decode (read64 (Concurrent.GlobalPublication.publish memory words) (Snapshot.address a thread))=
      if mask=true ∧ read32 memory (a.base.toNat+a.boundary.toNat+thread.val*4)≠0 then 0 else
        (Rows.contributions locations (a.elementValue memory)).foldl Correspondence.scatterStep (fun _ => 0) thread.val := by
  rw [a.parallel_value run compatible indexCompatible contents separated done thread]
  unfold Arena.value
  rw [represented thread,Rows.ordered]

end PtxTorchLean.Poisson.PTX.Assembly
