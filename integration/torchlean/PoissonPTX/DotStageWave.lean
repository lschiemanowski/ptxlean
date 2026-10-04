import PoissonPTX.DotInitialWave

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

def stageTarget (phase : Fin 8) (input : Nat → Word) (thread : Fin 256) (s : Flow.State) : Flow.State :=
  let guardState := guarded phase s
  if thread.val<stride phase then
    {guardState with core:=finish guardState.core (words input phase.val thread.val) (words input phase.val (thread.val+stride phase))}
  else guardState

/-- Execute the actual native guards, each active six-instruction update, and
one all-participant barrier. Inactive lanes execute their branch and barrier. -/
theorem stage_wave (start : NativeFlow.State 256) (phase : Fin 8)
    (ready : ReadyAt base (24+9*phase.val) generation start) (aligned : base%8=0) (input : Nat → Word) :
    ∃ final events indices, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      ReadyAt base (24+9*(phase.val+1)) (generation+1) final ∧ ∀ e∈events, Expected input e := by
  let target := fun t => stageTarget phase input t (NativeFlow.lane start t)
  obtain ⟨body,bodyIndices,bodyRun,bodyGood⟩ := NativeFlow.Serial.run_lanes start target (Expected input)
    (fun thread state same barrierEq siteEq => by
      have eq : state.core.lanes thread=start.core.lanes thread := congrArg Flow.State.core same
      have isLive : state.halted thread=false := (congrArg Flow.State.halted same).trans (ready.2.2.1 thread)
      have fresh : state.core.barrier.arrived thread=false := by rw [barrierEq,ready.2.2.2.1]; rfl
      let guardState := guarded phase (NativeFlow.lane start thread)
      let middle := NativeFlow.update state thread guardState
      have first : NativeFlow.Runs cfg ctx (program count left right output scratch) state [] [] middle := by
        simpa only [same,middle,guardState] using guard_run (count:=count) (left:=left) (right:=right)
          (output:=output) (scratch:=scratch) state thread phase ((congrArg PTX.State.pc eq).trans (ready.2.1 thread)) fresh isLive
      have laneEq : NativeFlow.lane middle thread=guardState := NativeFlow.lane_update_self _ _ _
      by_cases active : thread.val<stride phase
      · have guardPC : guardState.core.pc=26+9*phase.val := by
          dsimp only [guardState]
          rw [guarded_pc (s:=NativeFlow.lane start thread) (ready.1 thread).2.1]
          simp only [active,ite_true,NativeFlow.lane,ready.2.1]; omega
        have valid := update_valid (guarded_frame (s:=NativeFlow.lane start thread) (phase:=phase) (ready.1 thread)) aligned phase active
        have block := update_block guardState.core (Reduction.Control.readOffset phase true)
          (words input phase.val thread.val) (words input phase.val (thread.val+stride phase)) valid
        have fetch : ∀ (j : Nat) (op : Op), (PTX.Reduction.Update.code (Reduction.Control.readOffset phase true))[j]?=some op →
            (program count left right output scratch)[(middle.core.lanes thread).pc+j]?=some (.flow (.data (.data op))) := by
          intro j op found
          have bound := (List.getElem?_eq_some_iff.mp found).1
          have h := update_fetch (count:=count) (left:=left) (right:=right) (output:=output) (scratch:=scratch)
            phase ⟨j,by simpa [PTX.Reduction.Update.code] using bound⟩
          have counter : (middle.core.lanes thread).pc=26+9*phase.val := (congrArg (fun s : Flow.State => s.core.pc) laneEq).trans guardPC
          simpa only [counter,found,Option.map_some] using h
        have rest := NativeFlow.lift_block (cfg:=cfg) (ctx:=ctx) (start:=middle)
          ((congrArg Flow.State.core laneEq) ▸ block) fresh
          (by simpa only [middle,NativeFlow.update,Function.update_self,guardState,guarded_live,NativeFlow.lane] using ready.2.2.1 thread) fetch
        refine ⟨(updateEvents guardState.core (Reduction.Control.readOffset phase true)
          (words input phase.val thread.val) (words input phase.val (thread.val+stride phase))).map (Event.data thread),[],?_,?_⟩
        · simpa [middle,laneEq,NativeFlow.update_twice,target,stageTarget,active,guardState] using NativeFlow.append first rest
        · intro e member
          obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
          exact update_expected input _ phase thread guardPC active a ha
      · exact ⟨[],[],by simpa [middle,target,stageTarget,active,guardState] using first,by simp⟩)
  let middle := NativeFlow.Serial.allLanes start target
  have pcs : ∀ t, (middle.core.lanes t).pc=barrierSite ⟨phase.val+1,by omega⟩ := by
    intro t
    change (stageTarget phase input t (NativeFlow.lane start t)).core.pc=_
    unfold stageTarget
    split
    · rename_i active
      rw [update_pc,guarded_pc (s:=NativeFlow.lane start t) (ready.1 t).2.1]
      simp only [active,ite_true,NativeFlow.lane,ready.2.1]
      simp only [barrierSite]; omega
    · rename_i inactive
      rw [guarded_pc (s:=NativeFlow.lane start t) (ready.1 t).2.1]
      simp only [inactive,ite_false]
  have middleLive : ∀ t, middle.halted t=false := by
    intro t
    change (stageTarget phase input t (NativeFlow.lane start t)).halted=false
    unfold stageTarget; split <;> exact (guarded_live).trans (ready.2.2.1 t)
  obtain ⟨barriers,barrierRun,barrierGood⟩ := round_expected (input:=input) middle ⟨phase.val+1,by omega⟩
    pcs middleLive ready.2.2.2.1 ready.2.2.2.2
  refine ⟨NativeFlow.afterRound middle generation,body++barriers,bodyIndices,?_,?_,?_⟩
  · simpa using NativeFlow.append bodyRun barrierRun
  · refine ⟨?_,?_,middleLive,rfl,rfl⟩
    · intro t
      apply frame_advance
      change Frame base t (stageTarget phase input t (NativeFlow.lane start t)).core
      unfold stageTarget; split
      · exact frame_update (guarded_frame (s:=NativeFlow.lane start t) (phase:=phase) (ready.1 t))
      · exact guarded_frame (s:=NativeFlow.lane start t) (phase:=phase) (ready.1 t)
    · intro t
      change (middle.core.lanes t).pc+1=24+9*(phase.val+1)
      rw [pcs]; simp only [barrierSite]; omega
  · intro e member
    rcases List.mem_append.mp member with earlier | later
    · exact bodyGood e earlier
    · exact barrierGood e later

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
