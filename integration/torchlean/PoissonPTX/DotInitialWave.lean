import PoissonPTX.DotWitnessGuard

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256

/-- Run all initial publications and the first actual barrier round. The
accumulator bits come from the supplied entry state, and are stored unchanged. -/
theorem initial_wave (start : NativeFlow.State 256) (ready : ReadyAt base 20 generation start)
    (aligned : base%8=0) (inputs : ∀ t, (start.core.lanes t).regs 8=input t.val) :
    ∃ final events indices, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      ReadyAt base 24 (generation+1) final ∧ ∀ e∈events, Expected input e := by
  let target := fun t => {NativeFlow.lane start t with core:=SharedStore.finish (start.core.lanes t) 0 8}
  obtain ⟨body,bodyIndices,bodyRun,bodyGood⟩ := NativeFlow.Serial.run_lanes start target (Expected input)
    (fun thread state same barrierEq siteEq => by
      have eq : state.core.lanes thread=start.core.lanes thread := congrArg Flow.State.core same
      have isLive : state.halted thread=false := (congrArg Flow.State.halted same).trans (ready.2.2.1 thread)
      have valid := initial_valid (ready.1 thread) aligned
      have block := initial_block (start.core.lanes thread) valid
      have fetch : ∀ (j : Nat) (op : Op), (SharedStore.code 0 8)[j]?=some op →
          (program count left right output scratch)[(state.core.lanes thread).pc+j]?=some (.flow (.data (.data op))) := by
        intro j op found
        have bound := (List.getElem?_eq_some_iff.mp found).1
        have h := initial_fetch (count:=count) (left:=left) (right:=right) (output:=output) (scratch:=scratch)
          ⟨j,by simpa [SharedStore.code] using bound⟩
        simpa only [eq,ready.2.1,found,Option.map_some] using h
      have run := NativeFlow.lift_block (cfg:=cfg) (ctx:=ctx) (start:=state)
        (eq ▸ block) (by rw [barrierEq,ready.2.2.2.1]; rfl) isLive fetch
      refine ⟨(initialEvents (start.core.lanes thread)).map (Event.data thread),[],?_,?_⟩
      · simpa only [same,eq,target] using run
      · intro e member
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
        exact initial_expected _ thread (ready.2.1 thread) (inputs thread) a ha)
  let middle := NativeFlow.Serial.allLanes start target
  have pcs : ∀ t, (middle.core.lanes t).pc=barrierSite 0 := by
    intro t; change (SharedStore.finish (start.core.lanes t) 0 8).pc=23
    rw [initial_pc,ready.2.1]
  have middleLive : ∀ t, middle.halted t=false := ready.2.2.1
  obtain ⟨barriers,barrierRun,barrierGood⟩ := round_expected (input:=input) middle 0 pcs middleLive
    ready.2.2.2.1 ready.2.2.2.2
  refine ⟨NativeFlow.afterRound middle generation,body++barriers,bodyIndices,?_,?_,?_⟩
  · simpa using NativeFlow.append bodyRun barrierRun
  · refine ⟨?_,?_,middleLive,rfl,rfl⟩
    · intro t; exact frame_advance (frame_initial (ready.1 t))
    · intro t
      change (middle.core.lanes t).pc+1=24
      rw [pcs]; rfl
  · intro e member
    rcases List.mem_append.mp member with earlier | later
    · exact bodyGood e earlier
    · exact barrierGood e later

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
