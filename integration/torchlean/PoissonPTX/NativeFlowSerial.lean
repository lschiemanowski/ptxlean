import PoissonPTX.NativeFlowLocal

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial

def allLanes (start : State n) (target : Fin n → Flow.State) : State n :=
  ⟨{start.core with lanes:=fun t => (target t).core},fun t => (target t).predicates,fun t => (target t).halted⟩

def partialState (start : State n) (target : Fin n → Flow.State) (count : Nat) : State n :=
  allLanes start (fun t => if t.val<count then target t else lane start t)

theorem prefix_zero : partialState start target 0=start := by
  cases start
  simp [partialState,allLanes,lane]

theorem prefix_all {n : Nat} {start : State n} {target : Fin n → Flow.State} : partialState start target n=allLanes start target := by simp [partialState]

theorem prefix_next (start : State n) (target : Fin n → Flow.State) (count : Nat) (bound : count<n) :
    update (partialState start target count) ⟨count,bound⟩ (target ⟨count,bound⟩)=partialState start target (count+1) := by
  have tables : Function.update (fun t : Fin n => if t.val<count then target t else lane start t)
      ⟨count,bound⟩ (target ⟨count,bound⟩)=(fun t => if t.val<count+1 then target t else lane start t) := by
    funext t
    by_cases same : t=⟨count,bound⟩
    · subst t; simp
    · have different : t.val≠count := by intro eq; exact same (Fin.ext eq)
      simp only [Function.update_of_ne same]
      have range : (t.val<count) ↔ (t.val<count+1) := by omega
      simp only [range]
  have updated : ∀ (s : State n) (f : Fin n → Flow.State) (thread : Fin n) next,
      update (allLanes s f) thread next=allLanes s (Function.update f thread next) := by
    intro s f thread next
    simp only [update,allLanes,setLane]
    congr 2
    all_goals funext t; by_cases same : t=thread <;> simp [Function.update,same]
  rw [partialState,updated,tables]
  rfl

/-- Choose one finite schedule by running each lane's local body in turn.
This constructs existence without restricting the universal execution model. -/
theorem run_lanes (start : State n) (target : Fin n → Flow.State) (good : Event n → Prop)
    (each : ∀ (thread : Fin n) (state : State n),
      lane state thread=lane start thread → state.core.barrier=start.core.barrier → state.core.site=start.core.site →
      ∃ events indices, Runs cfg ctx program state events indices (update state thread (target thread)) ∧
        ∀ e, e∈events → good e) :
    ∃ events indices, Runs cfg ctx program start events indices (allLanes start target) ∧
      ∀ e, e∈events → good e := by
  have go : ∀ count, count≤n → ∃ events indices, Runs cfg ctx program start events indices (partialState start target count) ∧
      ∀ e, e∈events → good e := by
    intro count bound
    induction count with
    | zero => exact ⟨[],[],by rw [prefix_zero]; exact .nil,by simp⟩
    | succ count ih =>
      obtain ⟨before,beforeIndices,first,firstGood⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      obtain ⟨after,afterIndices,last,lastGood⟩ := each thread (partialState start target count)
        (by simp [partialState,allLanes,lane,thread]) rfl rfl
      rw [show update (partialState start target count) thread (target thread)=partialState start target (count+1)
        from prefix_next start target count thread.isLt] at last
      refine ⟨before++after,beforeIndices++afterIndices,NativeFlow.append first last,?_⟩
      intro e member
      rcases List.mem_append.mp member with first | last
      · exact firstGood e first
      · exact lastGood e last
  simpa only [prefix_all] using go n (Nat.le_refl n)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial
