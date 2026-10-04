import PoissonPTX.CellWitnessFinalFront
import PoissonPTX.ConcurrentAllocation
import PoissonPTX.CellTailShape

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

/-- Finish every real arithmetic lane before starting the output tails. This
is one legal witness schedule, not a restriction on the correctness theorem. -/
theorem final_front_wave (start : State n) (memory : Space → Memory)
    (bounds : AccessBounds width) (ready : Ready width bases start)
    (pcs : ∀ t, (start.lanes t).pc=startPC width 3)
    (reset : start.barrier=Ptx.Barrier.reset generation) :
    ∃ final events, Runs cfg (WithOutput.front width) start events final ∧
      ByteHistory.Recorded memory events ∧
      (∀ t, (final.lanes t).pc=(WithOutput.front width).length+(if t.val<width*width then 0 else 5)) ∧
      final.barrier=start.barrier ∧ final.site=start.site := by
  have construct : ∀ count, count≤n → ∃ state events,
      Runs cfg (WithOutput.front width) start events state ∧ ByteHistory.Recorded memory events ∧
      (∀ t, count≤t.val → state.lanes t=start.lanes t) ∧
      (∀ t, t.val<count → (state.lanes t).pc=(WithOutput.front width).length+(if t.val<width*width then 0 else 5)) ∧
      state.barrier=start.barrier ∧ state.site=start.site := by
    intro count bound
    induction count with
    | zero => exact ⟨start,[],.nil,.nil,by simp,by simp,rfl,rfl⟩
    | succ count ih =>
      obtain ⟨state,earlier,first,recorded,untouched,positions,barrier,site⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      have same := untouched thread (by rfl)
      obtain ⟨next,later,run,records,nextPC,physical⟩ := final_front_lane (cfg:=cfg)
        state thread (ByteHistory.publish memory earlier) bounds (by rw [barrier,reset]; rfl)
        (by rw [same]; exact pcs thread) (by rw [same]; exact ready.1 thread)
        (by rw [same]; exact ready.2 thread)
      refine ⟨setLane state thread next,earlier++later,runs_append first run,
        ByteHistory.recorded_append recorded records,?_,?_,barrier,site⟩
      · intro t after
        have different : t≠thread := by intro eq; subst t; dsimp [thread] at after; omega
        simpa only [setLane,Function.update_of_ne different] using untouched t (by omega)
      · intro t before
        by_cases equal : t=thread
        · subst t; simpa only [setLane,Function.update_self] using nextPC
        · have different : t.val≠count := by intro eq; exact equal (Fin.ext eq)
          simpa only [setLane,Function.update_of_ne equal] using positions t (by omega)
  obtain ⟨final,events,run,recorded,_,positions,barrier,site⟩ := construct n (Nat.le_refl n)
  exact ⟨final,events,run,recorded,fun t => positions t t.isLt,barrier,site⟩

/-- Output validity follows from the launch allocation and address registers;
no assumption is made about the value later stored there. -/
theorem front_output_valid (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (WithOutput.front width) start events final)
    (valid : Valid64 (start.lanes thread).globalStart (start.lanes thread).globalBytes
      (CellFinal.location (start.lanes thread) width output).toNat) :
    Valid64 (final.lanes thread).globalStart (final.lanes thread).globalBytes
      (CellFinal.location (final.lanes thread) width output).toNat := by
  have kept (r) (reg : r=0 ∨ r=14 ∨ r=15) :=
    Concurrent.Address.runs_keeps run (WithOutput.Address.front_keeps lo hi reg) thread
  have loc := WithOutput.Address.location_eq (kept 0 (Or.inl rfl))
    (kept 14 (Or.inr (Or.inl rfl))) (kept 15 (Or.inr (Or.inr rfl))) (width:=width) (output:=output)
  have frame := runs_allocation run thread
  have base := congrFun frame.1 .global
  have bytes := congrFun frame.2 .global
  change (final.lanes thread).globalStart=(start.lanes thread).globalStart at base
  change (final.lanes thread).globalBytes=(start.lanes thread).globalBytes at bytes
  simpa only [loc,base,bytes] using valid

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
