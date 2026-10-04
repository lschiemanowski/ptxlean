import PoissonPTX.AffineUpdateSources
import PoissonPTX.ObservedTemporalReplay
import PoissonPTX.ObservedParallelPublication

namespace PtxTorchLean.Poisson.PTX.AffineUpdate
open Concurrent
variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Event n)} {indices : List (Fin n × IndexSources.Access)}

theorem Arena.replay
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (admitted : Visibility.GlobalThreadSources words source) (thread : Fin n) :
    Flow.Runs (a.context thread) a.program (a.start memory (regs thread)) (t thread) := by
  have localRun := Flow.Parallel.project run thread
  have empty := no_indices localRun
  apply Flow.Observed.replay_temporal (initial:=fun space => match space with | .global => memory | .shared => fun _ => 0)
    localRun entry_linear
  · intro access member read
    have member := Flow.Parallel.word_member.mp member
    obtain ⟨r,found⟩ := List.mem_iff_getElem?.mp member
    have global := (a.parallel_access run member).1
    simpa only [global] using a.read_value run compatible admitted found read
  · simp [empty]
  · intro w stored store r readmem read same before
    have write := a.parallel_access run (Flow.Parallel.word_member.mp stored)
    have load := a.parallel_access run (Flow.Parallel.word_member.mp readmem)
    simp only [store,↓reduceIte] at write
    simp only [read,Bool.false_eq_true,↓reduceIte] at load
    rcases load.2 with h|h|h <;> omega
  · simp [empty]
  · exact ⟨by intros; rfl,by intros; rfl⟩

theorem Arena.publication
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (thread : Fin n) :
    read64 (GlobalPublication.publish memory words) (a.slot thread)=read64 (t thread).core.global (a.slot thread) := by
  apply Flow.Parallel.publication_word run rfl
  intro owner access member different global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  rw [write.2.2]
  exact a.owners thread owner (Ne.symm different)

/-- Only the direction array can change, byte for byte, even in an incomplete
execution. Coefficients, other vectors and arena padding are preserved. -/
theorem Arena.publication_outside
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (outside : p<a.base.toNat+a.direction.toNat ∨ a.base.toNat+a.direction.toNat+n*8≤p) :
    GlobalPublication.publish memory words p=memory p := by
  apply GlobalPublication.outside
  intro owner access member global store
  have write := a.parallel_access run member
  simp only [store,↓reduceIte] at write
  rw [write.2.2]
  unfold Arena.slot
  have := owner.isLt
  omega

theorem Arena.local_value {regs : Registers}
    (run : Flow.Runs (a.context i) a.program (a.start memory regs) final) (done : final.halted=true) :
    decode (read64 final.core.global (a.slot i))=a.value memory i := by
  have result := entry_correct run rfl rfl done (a.live i)
    (a.vector_valid memory regs i a.direction a.directionFit a.directionAligned)
    (a.vector_valid memory regs i a.shift a.shiftFit a.shiftAligned)
    (a.vector_valid memory regs i a.direction a.directionFit a.directionAligned)
  rw [a.setup_address memory regs i a.direction a.directionFit] at result
  have value : AffineUpdate.result (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core
      a.coefficient a.direction a.shift=a.value memory i := by
    unfold AffineUpdate.result product
    rw [a.setup_address memory regs i a.shift a.shiftFit,a.setup_address memory regs i a.direction a.directionFit]
    change decode (read64 memory _)+decode (read64 memory (a.base+a.coefficient).toNat)*decode (read64 memory _)=_
    rw [a.scalar_address]
    rfl
  exact result.1.trans value

/-- Universal in-place direction update for any completed admitted
interleaving: the published p vector is z + beta*p with two binary64 roundings.
The old p reads are derived from actual ownership and instruction order. -/
theorem Arena.parallel_value
    (run : Flow.Parallel.Runs a.context a.program (fun i => a.start memory (regs i)) words indices t)
    (compatible : Visibility.Compatible (fun space => match space with | .global => memory | .shared => fun _ => 0) words source)
    (admitted : Visibility.GlobalThreadSources words source)
    (done : ∀ i, (t i).halted=true) (thread : Fin n) :
    decode (read64 (GlobalPublication.publish memory words) (a.slot thread))=a.value memory thread := by
  rw [a.publication run thread]
  exact a.local_value (a.replay run compatible admitted thread) (done thread)

end PtxTorchLean.Poisson.PTX.AffineUpdate
