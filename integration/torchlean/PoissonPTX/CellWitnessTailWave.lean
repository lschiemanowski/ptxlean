import PoissonPTX.CellWitnessTail

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

theorem runs_append (first : Runs cfg ctx front tail start before middle)
    (second : Runs cfg ctx front tail middle after final) :
    Runs cfg ctx front tail start (before++after) final := by
  induction first with
  | nil => exact second
  | cons step rest ih => simpa only [List.append_assoc] using Runs.cons step (ih second)

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

/-- Execute every output tail, including the padding returns. Each selected
thread keeps its actual kernel state; other lanes remain untouched. -/
theorem tail_wave (start : WithTail.State n) (memory : Space → Memory)
    (running : ∀ t, start.halted t=false)
    (pcs : ∀ t, (start.core.lanes t).pc=(WithOutput.front width).length+(if t.val<width*width then 0 else 5))
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (valid : ∀ t, t.val<width*width → Valid64 (start.core.lanes t).globalStart
      (start.core.lanes t).globalBytes (CellFinal.location (start.core.lanes t) width output).toNat) :
    ∃ final events, WithTail.Runs cfg ctx (WithOutput.front width) (CellFinal.tail width output) start events final ∧
      ByteHistory.Recorded memory events ∧ (∀ t, final.halted t=true) ∧
      (∀ t, (final.core.lanes t).pc=(WithOutput.front width).length+6) ∧
      final.core.barrier=start.core.barrier ∧ final.core.site=start.core.site := by
  have construct : ∀ count, count≤n → ∃ state events,
      WithTail.Runs cfg ctx (WithOutput.front width) (CellFinal.tail width output) start events state ∧
      ByteHistory.Recorded memory events ∧
      (∀ t, count≤t.val → WithTail.lane state t=WithTail.lane start t) ∧
      (∀ t, t.val<count → state.halted t=true ∧ (state.core.lanes t).pc=(WithOutput.front width).length+6) ∧
      state.core.barrier=start.core.barrier ∧ state.core.site=start.core.site := by
    intro count bound
    induction count with
    | zero => exact ⟨start,[],.nil,.nil,by simp,by simp,rfl,rfl⟩
    | succ count ih =>
      obtain ⟨state,earlier,first,recorded,untouched,positions,barrier,site⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      have same := untouched thread (by rfl)
      have halted := congrArg Kernel.State.halted same
      obtain ⟨next,later,run,records,stopped,nextPC⟩ := tail_lane (cfg:=cfg) (ctx:=ctx)
        state thread (ByteHistory.publish memory earlier)
        (halted.trans (running thread)) (by rw [barrier,reset]; rfl)
        (by change (WithTail.lane state thread).core.pc=_; rw [same]; exact pcs thread)
        (by intro active; change Valid64 (WithTail.lane state thread).core.globalStart
              (WithTail.lane state thread).core.globalBytes (CellFinal.location (WithTail.lane state thread).core width output).toNat
            rw [same]; exact valid thread active)
      refine ⟨WithTail.update state thread next,earlier++later,WithTail.runs_append first run,
        ByteHistory.recorded_append recorded records,?_,?_,barrier,site⟩
      · intro t after
        have different : t≠thread := by intro eq; subst t; dsimp [thread] at after; omega
        simpa only [WithTail.update,WithTail.lane,setLane,Function.update_of_ne different] using untouched t (by omega)
      · intro t before
        by_cases equal : t=thread
        · subst t
          simpa only [WithTail.update,setLane,Function.update_self] using And.intro stopped nextPC
        · have different : t.val≠count := by intro eq; exact equal (Fin.ext eq)
          simpa only [WithTail.update,setLane,Function.update_of_ne equal] using positions t (by omega)
  obtain ⟨final,events,run,recorded,_,positions,barrier,site⟩ := construct n (Nat.le_refl n)
  exact ⟨final,events,run,recorded,fun t => (positions t t.isLt).1,fun t => (positions t t.isLt).2,barrier,site⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
