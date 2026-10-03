import PoissonPTX.ConcurrentLocalBlock

/-! Run a finite family of independent local instruction blocks sequentially.
This chooses a schedule only to witness existence, not for universal results. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Serial

def partialState (start : State n) (target : Fin n → PTX.State) (count : Nat) : State n :=
  {start with lanes := fun t => if t.val<count then target t else start.lanes t}

theorem prefix_zero {start : State n} {target : Fin n → PTX.State} : partialState start target 0=start := by simp [partialState]

theorem prefix_all {start : State n} {target : Fin n → PTX.State} : partialState start target n={start with lanes:=target} := by
  simp [partialState]

theorem prefix_next (start : State n) (target : Fin n → PTX.State) (count : Nat) (bound : count<n) :
    setLane (partialState start target count) ⟨count,bound⟩ (target ⟨count,bound⟩)=partialState start target (count+1) := by
  unfold setLane partialState
  congr 1
  funext t
  by_cases eq : t=⟨count,bound⟩
  · subst t; simp
  · have diff : t.val≠count := by intro h; exact eq (Fin.ext h)
    simp only [Function.update_of_ne eq]
    have eqBound : (t.val<count) ↔ (t.val<count+1) := by omega
    simp only [eqBound]

/-- The per-lane proof is reusable in a state where other lanes have already
finished. Its trace property is retained through the serialized schedule. -/
theorem run_lanes (start : State n) (target : Fin n → PTX.State) (good : Event n → Prop)
    (each : ∀ (thread : Fin n) (state : State n),
      state.lanes thread=start.lanes thread → state.barrier=start.barrier → state.site=start.site →
      ∃ events, Runs cfg program state events (setLane state thread (target thread)) ∧
        ∀ e, e∈events → good e) :
    ∃ events, Runs cfg program start events {start with lanes:=target} ∧ ∀ e, e∈events → good e := by
  have go : ∀ count, count≤n → ∃ events, Runs cfg program start events (partialState start target count) ∧
      ∀ e, e∈events → good e := by
    intro count bound
    induction count with
    | zero => exact ⟨[],by rw [prefix_zero]; exact Runs.nil,by simp⟩
    | succ count ih =>
      obtain ⟨before,first,hfirst⟩ := ih (by omega)
      let thread : Fin n := ⟨count,by omega⟩
      obtain ⟨after,last,hlast⟩ := each thread (partialState start target count) (by simp [partialState,thread]) rfl rfl
      rw [show setLane (partialState start target count) thread (target thread)=partialState start target (count+1)
        from prefix_next start target count thread.isLt] at last
      refine ⟨before++after,runs_append first last,?_⟩
      intro e member
      rcases List.mem_append.mp member with h|h
      · exact hfirst e h
      · exact hlast e h
  simpa only [prefix_all] using go n (Nat.le_refl n)

end PtxTorchLean.Poisson.PTX.Concurrent.Serial
