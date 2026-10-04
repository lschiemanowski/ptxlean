import PoissonPTX.DotInputWave
import PoissonPTX.DotTreeWitness

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def inputWords (s : NativeFlow.State 256) (index : Nat) : Word :=
  if bound : index<256 then (s.core.lanes ⟨index,bound⟩).regs 8 else 0

/-- Construct input loops followed by the physical native tree, with their
actual event segments retained for subsequent whole-history source admission. -/
theorem input_tree_candidate (start : NativeFlow.State 256)
    (entry : ∀ thread, (start.core.lanes thread).pc=0) (live : ∀ thread, start.halted thread=false)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (noSite : start.core.site=none)
    (sameInitial : ∀ thread, (start.core.lanes thread).global=memory)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (bounded : count<2^30)
    (arrays : ∀ thread, DotInput.Arrays (DotInput.setup (ctx thread) scratch (NativeFlow.lane start thread)).core count left right)
    (aligned : scratch.toNat%8=0)
    (shared : ∀ thread, (start.core.lanes thread).sharedStart=scratch.toNat ∧
      2048≤(start.core.lanes thread).sharedBytes ∧ scratch.toNat+(start.core.lanes thread).sharedBytes≤2^64) :
    ∃ middle final inputEvents treeEvents inputIndices treeIndices,
      NativeFlow.Runs cfg ctx (program count left right output scratch) start inputEvents inputIndices middle ∧
      NativeFlow.Runs cfg ctx (program count left right output scratch) middle treeEvents treeIndices final ∧
      ReadyAt scratch.toNat 96 (generation+9) final ∧
      (∀ e∈inputEvents, InputEvent memory e) ∧
      (∀ e∈treeEvents, Expected (inputWords middle) e) := by
  obtain ⟨middle,inputEvents,inputIndices,first,barrier,site,lanes,goodInput⟩ := input_wave start entry live reset sameInitial bounded arrays
  have ready : ReadyAt scratch.toNat 20 generation middle := by
    refine ⟨?_,fun t => (lanes t).1,fun t => (lanes t).2.1,barrier.trans reset,site.trans noSite⟩
    intro thread
    obtain ⟨_,_,_,_,sharedStart,sharedBytes,_,baseReg,laneReg⟩ := (lanes thread).2.2.2
    have base : (middle.core.lanes thread).regs 3=scratch := by
      simpa [DotInput.setup,NativeFlow.lane,assign,advance] using baseReg
    have lane : (middle.core.lanes thread).regs 14=(ctx thread).lane.setWidth 64 := by
      simpa [DotInput.setup,NativeFlow.lane,assign,advance] using laneReg
    have startEq : (middle.core.lanes thread).sharedStart=(start.core.lanes thread).sharedStart := sharedStart
    have bytesEq : (middle.core.lanes thread).sharedBytes=(start.core.lanes thread).sharedBytes := sharedBytes
    refine ⟨congrArg BitVec.toNat base,?_,startEq.trans (shared thread).1,?_,?_⟩
    · simp [lane,BitVec.toNat_setWidth,laneMap,Nat.mod_eq_of_lt (show thread.val<18446744073709551616 by have := thread.isLt; omega)]
    · rw [bytesEq]; exact (shared thread).2.1
    · rw [bytesEq]; exact (shared thread).2.2
  obtain ⟨final,treeEvents,treeIndices,second,finished,goodTree⟩ := tree_candidate middle ready aligned
    (input:=inputWords middle) (by intro t; simp [inputWords,t.isLt])
  exact ⟨middle,final,inputEvents,treeEvents,inputIndices,treeIndices,first,second,finished,goodInput,goodTree⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
