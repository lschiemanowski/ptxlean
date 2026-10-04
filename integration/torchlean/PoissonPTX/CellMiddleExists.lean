import PoissonPTX.CellWitnessRound
import PoissonPTX.CellWitnessProgram
import PoissonPTX.CellAccessCertified

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- Construct all three middle barrier rounds.
Shared loads are selected from actual earlier recorded stores. The initial byte
view is an explicit input here; the whole-entry composition must obtain it from
the real gather prefix, not install it into the machine. -/
theorem middle_exists (start : State n) (memory : Space → Memory)
    (lo : 2≤width) (hi : width≤5) (ready : Ready width bases start)
    (pcs : ∀ t, (start.lanes t).pc=0)
    (reset : start.barrier=Ptx.Barrier.reset generation) (site : start.site=none) :
    ∃ final events, Runs cfg (program width) start events final ∧
      ByteHistory.Recorded memory events ∧ Ready width bases final ∧
      (∀ t, (final.lanes t).pc=startPC width 3) ∧
      final.barrier=Ptx.Barrier.reset (generation+3) ∧ final.site=none := by
  have bounds := access_bounds lo hi
  have forward := checked_forward (checked width lo hi)
  have phases : ∀ count, (bound : count≤3) → ∃ state events,
      Runs cfg (program width) start events state ∧ ByteHistory.Recorded memory events ∧ Ready width bases state ∧
      (∀ t, (state.lanes t).pc=startPC width ⟨count,by omega⟩) ∧
      state.barrier=Ptx.Barrier.reset (generation+count) ∧ state.site=none := by
    intro count bound
    induction count with
    | zero => exact ⟨start,[],.nil,.nil,ready,pcs,by simpa using reset,site⟩
    | succ count ih =>
      obtain ⟨state,earlier,first,recorded,stateReady,positions,barrier,noSite⟩ := ih (by omega)
      let stage : Fin 4 := ⟨count,by omega⟩
      obtain ⟨middle,bodyEvents,bodyRun,bodyRecorded,bodyReady,bodyPC,bodyBarrier,bodySite⟩ :=
        body_wave (cfg:=cfg) state (stageBody width stage) (ByteHistory.publish memory earlier)
          bounds stateReady positions barrier (stage_guard stage) (fun _ _ found => stage_fetch stage found)
      obtain ⟨barriers,roundRun,roundRecorded,roundReady⟩ := round_exists (cfg:=cfg)
        middle (ByteHistory.publish (ByteHistory.publish memory earlier) bodyEvents) bodyReady bodyPC
        (bodyBarrier.trans barrier) (bodySite.trans noSite) (stage_sync stage (by dsimp [stage]; omega)) forward
      refine ⟨afterRound middle (generation+count),earlier++bodyEvents++barriers,
        runs_append (runs_append first bodyRun) roundRun,?_,roundReady,?_,?_,rfl⟩
      · exact ByteHistory.recorded_append (ByteHistory.recorded_append recorded bodyRecorded)
          (by simpa only [ByteHistory.publish_append] using roundRecorded)
      · intro t
        change (middle.lanes t).pc+1=startPC width ⟨count+1,by omega⟩
        rw [bodyPC]
        exact (next_stage (width:=width) ⟨count,by omega⟩).symm
      · simp [afterRound,Nat.add_assoc]
  exact phases 3 (by omega)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
