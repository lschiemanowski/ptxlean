import PoissonPTX.CellWitnessPhase

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

def Ready (width : Nat) (bases : Space → Word) (state : State n) : Prop :=
  (∀ t, Allocation width bases (state.lanes t)) ∧
  ∀ t, t.val<width*width → Matches bases (fun _ _ => 0)
    (atPC .addresses (program width) (Numeric.seed width t.val) (state.lanes t).pc) (state.lanes t)

theorem ready_update (ready : Ready width bases state)
    (physical : Allocation width bases next)
    (related : thread.val<width*width → Matches bases (fun _ _ => 0)
      (atPC .addresses (program width) (Numeric.seed width thread.val) next.pc) next) :
    Ready width bases (setLane state thread next) := by
  constructor
  · intro t
    by_cases same : t=thread
    · subst t; simpa only [setLane,Function.update_self] using physical
    · simpa only [setLane,Function.update_of_ne same] using ready.1 t
  · intro t active
    by_cases same : t=thread
    · subst t; simpa only [setLane,Function.update_self] using related active
    · simpa only [setLane,Function.update_of_ne same] using ready.2 t active

/-- Serialize only the chosen existence witness. Each lane's read policy is
threaded through the actual accumulated stores; other lanes retain their state. -/
theorem body_wave (start : State n) (code : List Op) (memory : Space → Memory)
    (bounds : AccessBounds width) (ready : Ready width bases start)
    (pcs : ∀ t, (start.lanes t).pc=pc)
    (reset : start.barrier=Ptx.Barrier.reset generation)
    (guard : (program width)[pc]?=some (.skip (width*width) (pc+1+code.length)))
    (fetch : ∀ j op, code[j]?=some op → (program width)[pc+1+j]?=some (.data op)) :
    ∃ final events, Runs cfg (program width) start events final ∧
      ByteHistory.Recorded memory events ∧ Ready width bases final ∧
      (∀ t, (final.lanes t).pc=pc+1+code.length) ∧
      final.barrier=start.barrier ∧ final.site=start.site := by
  have construct : ∀ count, count≤n → ∃ state events, Runs cfg (program width) start events state ∧
      ByteHistory.Recorded memory events ∧ Ready width bases state ∧
      (∀ t, (state.lanes t).pc=if t.val<count then pc+1+code.length else pc) ∧
      state.barrier=start.barrier ∧ state.site=start.site := by
    intro count bound
    induction count with
    | zero => exact ⟨start,[],.nil,.nil,ready,by simpa using pcs,rfl,rfl⟩
    | succ count ih =>
      obtain ⟨state,earlier,first,recorded,stateReady,positions,barrier,site⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      have atGuard : (state.lanes thread).pc=pc := by simp [positions,thread]
      obtain ⟨next,later,run,records,nextPC,physical,related⟩ :=
        lane_phase_exists (cfg:=cfg) state thread code (ByteHistory.publish memory earlier) bounds
          (by rw [barrier,reset]; rfl) (stateReady.1 thread) (stateReady.2 thread)
          (by simpa only [atGuard] using guard) (by simpa only [atGuard] using fetch)
      refine ⟨setLane state thread next,earlier++later,runs_append first run,
        ByteHistory.recorded_append recorded records,ready_update stateReady physical related,?_,barrier,site⟩
      intro t
      by_cases same : t=thread
      · subst t
        simpa [setLane,thread,atGuard] using nextPC
      · have different : t.val≠count := by intro eq; exact same (Fin.ext eq)
        have sameRange : (t.val<count+1) ↔ (t.val<count) := by omega
        simp only [setLane,Function.update_of_ne same,positions,sameRange]
  obtain ⟨final,events,actual,recorded,afterReady,positions,barrier,site⟩ := construct n (Nat.le_refl n)
  exact ⟨final,events,actual,recorded,afterReady,by simpa using positions,barrier,site⟩

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
