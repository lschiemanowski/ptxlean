import PoissonPTX.ConcurrentCut
import PoissonPTX.CellConsumerOutput

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
open CellMiddle Correspondence

/-- Recover the existing last-barrier cut from a single actual execution. Only
one observed thread needs to have finished; other final consumers may lag. -/
theorem split (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (thread : Fin 32) (finished : (final.lanes thread).pc=(program width).length) :
    ∃ before after ready,
      events=before++after ∧ Runs cfg (Checks.program width) start before ready ∧
      (∀ t, (ready.lanes t).pc=(Checks.program width).length) ∧
      Runs cfg (program width) ready after final := by
  have size : (Checks.program width).length=Checks.boundary width 2+1 := by
    interval_cases width <;> decide +kernel
  obtain ⟨barrier,stops⟩ := boundaries width lo hi 2
  apply Cut.split_run run launch.aligned size barrier (Checks.bounded_stops stops)
    (fun t => by rw [launch.pcs]; omega) thread
  rw [finished]
  have len : (program width).length=(Checks.program width).length+(suffix width).length :=
    List.length_append
  omega

/-- One concurrent run suffices for local-cell arithmetic correspondence. The
last-barrier state, prefix completion and common source history are derived. -/
theorem completed_run (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (compatible : Visibility.Compatible initial events source)
    (performed : Visibility.Performed events source)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (final.lanes thread).pc=(program width).length) :
    decode ((final.lanes thread).regs 11)=Spec.get2 (localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0)) i j := by
  obtain ⟨before,after,ready,eventsEq,middle,done,rest⟩ := split launch lo hi run thread finished
  subst events
  exact completed_arithmetic launch lo hi middle done rest compatible performed thread i j lane finished

/-- The final fetched tail starts from the actual single-run result. Concurrent
global stores and their interaction with other readers remain a separate task. -/
theorem stored_run (launch : Numeric.Launch width bases start) (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (compatible : Visibility.Compatible initial events source)
    (performed : Visibility.Performed events source)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (final.lanes thread).pc=(program width).length)
    (valid : Valid64 (final.lanes thread).globalStart (final.lanes thread).globalBytes
      (CellFinal.location (final.lanes thread) width output).toNat)
    (precode : List Kernel.Instr) (pc : (final.lanes thread).pc=precode.length)
    (tailRun : Kernel.Run ctx (precode++CellFinal.tail width output)
      ⟨final.lanes thread,false,false⟩ stored) :
    decode (read64 stored.core.global (CellFinal.location (final.lanes thread) width output).toNat)=
      Spec.get2 (localAction
        (Numeric.initialTensor width bases initial .global 0)
        (Numeric.initialTensor width bases initial .global (width*width*8+32))
        (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width bases initial .shared 0)) i j := by
  have h := CellFinal.tail_correct rfl valid (Kernel.run_exec tailRun precode _ rfl pc)
  exact h.1.trans (completed_run launch lo hi run compatible performed thread i j lane finished)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer
