import PoissonPTX.AssemblyReadFootprints
import PoissonPTX.AssemblySnapshotPublication

namespace PtxTorchLean.Poisson.PTX.Assembly
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- Physical input/output separation implies actual read/write separation for
all threads. Contribution-index bounds are established from the admitted
index bytes before this result is used to justify floating-point reads. -/
theorem Arena.parallel_separate
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation) :
    Flow.Parallel.Separate words indices := by
  constructor
  · intro writer write member store reader read observed load same
    have stored := (a.parallel_store memory regs run member store).2
    obtain ⟨_,field,count,k,located,inside,apart⟩ :=
      (a.read_footprints run compatible contents separated reader).1 read
        (Flow.Parallel.word_member.mpr observed) load
    rw [stored,located]
    unfold Arena.FieldApart at apart
    have := writer.isLt
    omega
  · intro writer write member store global reader read observed
    have stored := (a.parallel_store memory regs run member store).2
    obtain ⟨field,count,k,located,inside,apart⟩ :=
      (a.read_footprints run compatible contents separated reader).2 read
        (Flow.Parallel.index_member.mpr observed)
    rw [stored,located]
    unfold Arena.FieldApart at apart
    have := writer.isLt
    omega

/-- Replay of every active thread is derived from the actual joint execution,
its joint byte-source assignments, and initial layout/index validity. There
is no assumed loop traversal, input-read oracle, or local snapshot execution. -/
theorem Arena.parallel_replay
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation) (thread : Fin n) :
    Flow.Runs (a.context thread)
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (a.start memory (regs thread)) (t thread) := by
  apply Flow.Parallel.replay run compatible indexCompatible
    (a.parallel_separate run indexCompatible contents separated)
  intro i
  funext space
  cases space <;> rfl

/-- The completed snapshot view is constructed from the joint execution; it
is an output of the visibility proof, rather than a correspondence premise. -/
def Arena.finished
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : Concurrent.Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation)
    (done : ∀ i, (t i).halted=true) : Snapshot.Finished a memory mask where
  regs := regs
  final := t
  run := a.parallel_replay run compatible indexCompatible contents separated
  done := done

end PtxTorchLean.Poisson.PTX.Assembly
