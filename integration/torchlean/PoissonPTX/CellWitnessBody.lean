import PoissonPTX.CellWitnessFinalWave
import PoissonPTX.CellWitnessTailWave

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

/-- A complete arbitrary-input continuation: three actual barrier rounds,
final arithmetic, all output stores and all returns. Physical allocation and
launch/address representation are the only requirements on input states. -/
theorem body_exists (start : WithTail.State n) (memory : Space → Memory)
    (lo : 2≤width) (hi : width≤5) (ready : Ready width bases start.core)
    (pcs : ∀ t, (start.core.lanes t).pc=0) (running : ∀ t, start.halted t=false)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (site : start.core.site=none)
    (valid : ∀ t, t.val<width*width → Valid64 (start.core.lanes t).globalStart
      (start.core.lanes t).globalBytes (CellFinal.location (start.core.lanes t) width output).toNat) :
    ∃ final events, WithTail.Runs cfg ctx (WithOutput.front width) (CellFinal.tail width output) start events final ∧
      ByteHistory.Recorded memory events ∧ (∀ t, final.halted t=true) ∧
      (∀ t, (final.core.lanes t).pc=(WithOutput.front width).length+6) ∧
      final.core.barrier=Ptx.Barrier.reset (generation+3) ∧ final.core.site=none := by
  obtain ⟨middle,earlier,middleRun,middleRecords,middleReady,middlePC,middleBarrier,middleSite⟩ :=
    middle_exists (cfg:=cfg) start.core memory lo hi ready pcs reset site
  have middleFront := middle_front lo hi middleRun middlePC
  obtain ⟨finished,later,finalRun,finalRecords,finalPC,finalBarrier,finalSite⟩ :=
    final_front_wave (cfg:=cfg) middle (ByteHistory.publish memory earlier) (access_bounds lo hi)
      middleReady middlePC middleBarrier
  have frontRun := runs_append middleFront finalRun
  have frontRecords := ByteHistory.recorded_append middleRecords finalRecords
  let tailStart : WithTail.State n := {start with core:=finished}
  obtain ⟨final,tailEvents,tailRun,tailRecords,halted,done,tailBarrier,tailSite⟩ :=
    tail_wave (cfg:=cfg) (ctx:=ctx) tailStart (ByteHistory.publish memory (earlier++later)) running
      finalPC (finalBarrier.trans middleBarrier)
      (fun t active => front_output_valid lo hi frontRun (valid t active))
  exact ⟨final,(earlier++later)++tailEvents,
    WithTail.runs_append (lift_front frontRun running) tailRun,
    ByteHistory.recorded_append frontRecords tailRecords,halted,done,
    tailBarrier.trans (finalBarrier.trans middleBarrier),tailSite.trans (finalSite.trans middleSite)⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
