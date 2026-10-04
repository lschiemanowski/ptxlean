import PoissonPTX.CellWitnessBlock
import PoissonPTX.ConcurrentBarrier

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- Execute the fetched phase guard and body for one lane. Padding lanes take
the real skip; active lanes use the checked byte-address expressions. -/
theorem lane_phase_exists (start : State n) (thread : Fin n) (code : List Op) (memory : Space → Memory)
    (bounds : AccessBounds width) (fresh : start.barrier.arrived thread=false)
    (physical : Allocation width bases (start.lanes thread))
    (related : thread.val<width*width → Matches bases (fun _ _ => 0)
      (atPC .addresses (program width) (Numeric.seed width thread.val) (start.lanes thread).pc) (start.lanes thread))
    (guard : (program width)[(start.lanes thread).pc]?=
      some (.skip (width*width) ((start.lanes thread).pc+1+code.length)))
    (fetch : ∀ j op, code[j]?=some op →
      (program width)[(start.lanes thread).pc+1+j]?=some (.data op)) :
    ∃ final events,
      Runs cfg (program width) start events (setLane start thread final) ∧
      ByteHistory.Recorded memory events ∧ final.pc=(start.lanes thread).pc+1+code.length ∧
      Allocation width bases final ∧
      (thread.val<width*width → Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) final.pc) final) := by
  by_cases active : thread.val<width*width
  · let middle := setLane start thread (advance (start.lanes thread))
    have first : Runs cfg (program width) start [] middle := by
      have step : Step cfg (program width) thread start ⟨middle,[]⟩ := by
        refine ⟨fresh,_,guard,?_⟩
        simpa only [active,↓reduceIte,middle,advance] using (Dispatch.skip (cfg:=cfg) (thread:=thread)
          (s:=start) (active:=width*width) (target:=(start.lanes thread).pc+1+code.length))
      exact .cons step .nil
    have ready : Matches bases (fun _ _ => 0)
        (atPC .addresses (program width) (Numeric.seed width thread.val) (advance (start.lanes thread)).pc)
        (advance (start.lanes thread)) := by
      rw [show (advance (start.lanes thread)).pc=(start.lanes thread).pc+1 from rfl,at_next guard]
      exact related active
    obtain ⟨final,accesses,actual,recorded,afterPhysical,afterReady⟩ :=
      block_exists code (advance (start.lanes thread)) memory bounds thread active physical ready fetch
    have later := Local.lift (cfg:=cfg) (program:=program width) (start:=middle) (thread:=thread)
      (by simpa only [middle,setLane,Function.update_self] using actual) fresh
      (by simpa only [middle,setLane,Function.update_self,advance] using fetch)
    have done := Local.pc actual
    refine ⟨final,accesses.map (Event.data thread),?_,recorded,done,afterPhysical,fun _ => afterReady⟩
    have same : setLane middle thread final=setLane start thread final := by simp [middle,setLane]
    simpa only [same,List.nil_append] using runs_append first later
  · let final : PTX.State := {(start.lanes thread) with pc:=(start.lanes thread).pc+1+code.length}
    have step : Step cfg (program width) thread start ⟨setLane start thread final,[]⟩ := by
      refine ⟨fresh,_,guard,?_⟩
      simpa only [active,↓reduceIte] using (Dispatch.skip (cfg:=cfg) (thread:=thread)
        (s:=start) (active:=width*width) (target:=(start.lanes thread).pc+1+code.length))
    exact ⟨final,[],.cons step .nil,.nil,rfl,physical,fun h => False.elim (active h)⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
