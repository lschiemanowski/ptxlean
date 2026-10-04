import PoissonPTX.DotInputTreeCandidate
import PoissonPTX.DotTailWave
import PoissonPTX.NativeFlowLayout
import PoissonPTX.DotStores

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def CandidateEvent (memory : Memory) (input : Nat → Word) (event : Event 256) : Prop :=
  InputEvent memory event ∨ Expected input event ∨ TailEvent (words input 8 0) event

/-- One finite native schedule runs the actual input loops, nine barrier
rounds, reduction bodies and epilogue. No extra barrier or shared snapshot is
introduced. The exact candidate event values are retained for admission. -/
theorem complete_candidate (start : NativeFlow.State 256)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (noSite : start.core.site=none)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=memory)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (bounded : count<2^30)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (aligned : scratch.toNat%8=0)
    (shared : ∀ thread, (start.core.lanes thread).sharedStart=scratch.toNat ∧
      2048≤(start.core.lanes thread).sharedBytes ∧ scratch.toNat+(start.core.lanes thread).sharedBytes≤2^64)
    (outputs : ∀ thread, Valid64 (start.core.lanes thread).globalStart (start.core.lanes thread).globalBytes
      ((ctx thread).arena+output).toNat) :
    ∃ final events indices input, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      (∀ t, final.halted t=true) ∧ (final.core.lanes 0).pc=104 ∧ ∀ e∈events, CandidateEvent memory input e := by
  obtain ⟨middle,treeFinal,inputEvents,treeEvents,inputIndices,treeIndices,first,second,ready,goodInput,goodTree⟩ :=
    input_tree_candidate (cfg:=cfg) start entry live reset noSite sameInitial laneMap bounded arrays aligned shared
  have prefixRun := NativeFlow.append first second
  have launchAligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have outputValid : ∀ t, Valid64 (treeFinal.core.lanes t).globalStart (treeFinal.core.lanes t).globalBytes
      ((treeFinal.core.lanes t).regs 0+output).toNat := by
    intro t
    have layout := NativeFlow.runs_layout prefixRun launchAligned t
    have reg := (run_addresses prefixRun launchAligned entry t).1 (by change 2≤(treeFinal.core.lanes t).pc; rw [ready.2.1]; decide)
    have begins := congrArg (fun x : Nat×Nat×Nat×Nat => x.1) layout
    have sizes := congrArg (fun x : Nat×Nat×Nat×Nat => x.2.1) layout
    change (treeFinal.core.lanes t).globalStart=(start.core.lanes t).globalStart at begins
    change (treeFinal.core.lanes t).globalBytes=(start.core.lanes t).globalBytes at sizes
    change (treeFinal.core.lanes t).regs 0=(ctx t).arena at reg
    rw [begins,sizes,reg]; exact outputs t
  obtain ⟨final,tailEvents,tailIndices,last,returned,zeroPC,goodTail⟩ := tail_wave (word:=words (inputWords middle) 8 0) treeFinal ready aligned outputValid
  refine ⟨final,(inputEvents++treeEvents)++tailEvents,(inputIndices++treeIndices)++tailIndices,inputWords middle,
    NativeFlow.append prefixRun last,returned,zeroPC,?_⟩
  intro e member
  rcases List.mem_append.mp member with first | last
  · rcases List.mem_append.mp first with input | tree
    · exact Or.inl (goodInput e input)
    · exact Or.inr (Or.inl (goodTree e tree))
  · exact Or.inr (Or.inr (goodTail e last))

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
