import PoissonPTX.CellMiddleExists

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- Construct all three middle barrier rounds and the final arithmetic phase.
Shared loads are selected from actual earlier recorded stores. The initial byte
view is an explicit input here; the whole-entry composition must obtain it from
the real gather prefix, not install it into the machine. -/
theorem arithmetic_exists (start : State n) (memory : Space → Memory)
    (lo : 2≤width) (hi : width≤5) (ready : Ready width bases start)
    (pcs : ∀ t, (start.lanes t).pc=0)
    (reset : start.barrier=Ptx.Barrier.reset generation) (site : start.site=none) :
    ∃ final events, Runs cfg (program width) start events final ∧
      ByteHistory.Recorded memory events ∧ Ready width bases final ∧
      (∀ t, (final.lanes t).pc=(program width).length) ∧
      final.barrier=Ptx.Barrier.reset (generation+3) ∧ final.site=none := by
  have bounds := access_bounds lo hi
  obtain ⟨state,earlier,first,recorded,stateReady,positions,barrier,noSite⟩ :=
    middle_exists (cfg:=cfg) start memory lo hi ready pcs reset site
  obtain ⟨final,last,lastRun,lastRecorded,lastReady,lastPC,lastBarrier,lastSite⟩ :=
    body_wave (cfg:=cfg) state (stageBody width 3) (ByteHistory.publish memory earlier)
      bounds stateReady positions barrier (stage_guard 3) (fun _ _ found => stage_fetch 3 found)
  exact ⟨final,earlier++last,runs_append first lastRun,ByteHistory.recorded_append recorded lastRecorded,
    lastReady,by intro t; exact (lastPC t).trans last_end,lastBarrier.trans barrier,lastSite.trans noSite⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
