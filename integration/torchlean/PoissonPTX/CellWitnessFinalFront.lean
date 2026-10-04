import PoissonPTX.CellWitnessFront

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

theorem final_data_fetch (found : (stageBody width 3)[j]?=some op) :
    (WithOutput.front width)[startPC width 3+1+j]?=some (.data op) := by
  rw [WithOutput.front,List.getElem?_map,stage_fetch 3 found]
  rfl

/-- Execute the emitted final guard: active lanes reach the real output tail;
padding lanes jump directly to its return instruction. -/
theorem final_front_lane (start : State n) (thread : Fin n) (memory : Space → Memory)
    (bounds : AccessBounds width) (fresh : start.barrier.arrived thread=false)
    (position : (start.lanes thread).pc=startPC width 3)
    (physical : Allocation width bases (start.lanes thread))
    (related : thread.val<width*width → Matches bases (fun _ _ => 0)
      (atPC .addresses (program width) (Numeric.seed width thread.val) (start.lanes thread).pc) (start.lanes thread)) :
    ∃ final events,
      Runs cfg (WithOutput.front width) start events (setLane start thread final) ∧
      ByteHistory.Recorded memory events ∧
      final.pc=(WithOutput.front width).length+(if thread.val<width*width then 0 else 5) ∧
      Allocation width bases final := by
  have guard : (WithOutput.front width)[(start.lanes thread).pc]?=
      some (.skip (width*width) ((WithOutput.front width).length+5)) := by
    rw [position]; exact WithOutput.padding_return
  by_cases active : thread.val<width*width
  · let middle := setLane start thread (advance (start.lanes thread))
    have first : Runs cfg (WithOutput.front width) start [] middle := by
      have step : Step cfg (WithOutput.front width) thread start ⟨middle,[]⟩ := by
        refine ⟨fresh,_,guard,?_⟩
        simpa only [active,↓reduceIte,middle,advance] using
          (Dispatch.skip (cfg:=cfg) (thread:=thread) (s:=start) (active:=width*width)
            (target:=(WithOutput.front width).length+5))
      exact .cons step .nil
    have ready : Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) (advance (start.lanes thread)).pc)
        (advance (start.lanes thread)) := by
      change Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) ((start.lanes thread).pc+1)) _
      rw [position,at_next (stage_guard (width:=width) 3)]
      simpa only [position,transfer,Matches,advance] using related active
    obtain ⟨final,accesses,actual,recorded,afterPhysical,afterReady⟩ :=
      block_exists (stageBody width 3) (advance (start.lanes thread)) memory bounds thread active physical ready
        (by intro j op found; simpa only [advance,position] using stage_fetch (width:=width) 3 found)
    have later := Local.lift (cfg:=cfg) (program:=WithOutput.front width) (start:=middle) (thread:=thread)
      (by simpa only [middle,setLane,Function.update_self] using actual) fresh
      (by intro j op found; simpa only [middle,setLane,Function.update_self,advance,position] using final_data_fetch found)
    have done := Local.pc actual
    have endPC : final.pc=(WithOutput.front width).length := by
      rw [WithOutput.front_length,← last_end]
      simpa only [advance,position] using done
    refine ⟨final,accesses.map (Event.data thread),?_,recorded,by simp only [active,↓reduceIte,Nat.add_zero]; exact endPC,afterPhysical⟩
    have same : setLane middle thread final=setLane start thread final := by simp [middle,setLane]
    simpa only [same,List.nil_append] using runs_append first later
  · let final : PTX.State := {(start.lanes thread) with pc:=(WithOutput.front width).length+5}
    have step : Step cfg (WithOutput.front width) thread start ⟨setLane start thread final,[]⟩ := by
      refine ⟨fresh,_,guard,?_⟩
      simpa only [active,↓reduceIte] using (Dispatch.skip (cfg:=cfg) (thread:=thread) (s:=start)
        (active:=width*width) (target:=(WithOutput.front width).length+5))
    exact ⟨final,[],.cons step .nil,.nil,by simp [active,final],physical⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
