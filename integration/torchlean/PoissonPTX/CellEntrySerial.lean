import PoissonPTX.CellEntryRecordLocal

namespace PtxTorchLean.Poisson.PTX.CellEntry.Serial

def allLanes (start : State n) (target : Fin n → CellPrologue.State) : State n :=
  ⟨{start.core with lanes:=fun t => (target t).core},fun t => (target t).live⟩

def partialState (start : State n) (target : Fin n → CellPrologue.State) (count : Nat) : State n :=
  allLanes start (fun t => if t.val<count then target t else lane start t)

theorem prefix_zero : partialState start target 0=start := by
  cases start
  simp [partialState,allLanes,lane]

theorem prefix_all {n : Nat} {start : State n} {target : Fin n → CellPrologue.State} : partialState start target n=allLanes start target := by simp [partialState]

theorem prefix_next (start : State n) (target : Fin n → CellPrologue.State) (count : Nat) (bound : count<n) :
    setLane (partialState start target count) ⟨count,bound⟩ (target ⟨count,bound⟩)=partialState start target (count+1) := by
  have tables : Function.update (fun t : Fin n => if t.val<count then target t else lane start t)
      ⟨count,bound⟩ (target ⟨count,bound⟩)=(fun t => if t.val<count+1 then target t else lane start t) := by
    funext t
    by_cases same : t=⟨count,bound⟩
    · subst t; simp
    · have different : t.val≠count := by intro eq; exact same (Fin.ext eq)
      simp only [Function.update_of_ne same]
      have range : (t.val<count) ↔ (t.val<count+1) := by omega
      simp only [range]
  have updated : ∀ (s : State n) (f : Fin n → CellPrologue.State) (thread : Fin n) next,
      setLane (allLanes s f) thread next=allLanes s (Function.update f thread next) := by
    intro s f thread next
    simp only [setLane,allLanes,Concurrent.setLane]
    congr 2
    all_goals funext t; by_cases same : t=thread <;> simp [Function.update,same]
  rw [partialState,updated,tables]
  rfl

/-- Choose one finite schedule by running each lane's local body in turn.
This constructs existence without restricting the universal execution model. -/
theorem append (first : Runs cfg ctx code s left leftIndices middle)
    (second : Runs cfg ctx code middle right rightIndices final) :
    Runs cfg ctx code s (left++right) (leftIndices++rightIndices) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => simpa [List.append_assoc] using Runs.cons step (ih second)

theorem run_lanes (start : State n) (target : Fin n → CellPrologue.State) (good : Concurrent.Event n → Prop)
    (indexGood : Fin n × IndexSources.Access → Prop)
    (each : ∀ (thread : Fin n) (state : State n),
      lane state thread=lane start thread → state.core.barrier=start.core.barrier → state.core.site=start.core.site →
      ∃ events indices, Runs cfg ctx code state events indices (setLane state thread (target thread)) ∧
        (∀ e, e∈events → good e) ∧ ∀ i∈indices, indexGood i) :
    ∃ events indices, Runs cfg ctx code start events indices (allLanes start target) ∧
      (∀ e, e∈events → good e) ∧ ∀ i∈indices, indexGood i := by
  have go : ∀ count, count≤n → ∃ events indices, Runs cfg ctx code start events indices (partialState start target count) ∧
      (∀ e, e∈events → good e) ∧ ∀ i∈indices, indexGood i := by
    intro count bound
    induction count with
    | zero => exact ⟨[],[],by rw [prefix_zero]; exact .nil,by simp,by simp⟩
    | succ count ih =>
      obtain ⟨before,beforeIndices,first,firstGood,firstIx⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      obtain ⟨after,afterIndices,last,lastGood,lastIx⟩ := each thread (partialState start target count)
        (by simp [partialState,allLanes,lane,thread]) rfl rfl
      rw [show setLane (partialState start target count) thread (target thread)=partialState start target (count+1)
        from prefix_next start target count thread.isLt] at last
      refine ⟨before++after,beforeIndices++afterIndices,append first last,?_,?_⟩
      · intro e member
        rcases List.mem_append.mp member with first | last
        · exact firstGood e first
        · exact lastGood e last
      · intro i member
        rcases List.mem_append.mp member with first | last
        · exact firstIx i first
        · exact lastIx i last
  simpa only [prefix_all] using go n (Nat.le_refl n)

end PtxTorchLean.Poisson.PTX.CellEntry.Serial
