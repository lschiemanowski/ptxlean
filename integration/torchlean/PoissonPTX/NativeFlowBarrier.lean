import PoissonPTX.NativeFlowRegion
import PoissonPTX.NativeFlowHistory

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

def StopsAt (program : List Instr) (boundary : Nat) : Prop :=
  ∀ pc i, program[pc]?=some (.flow i) → pc≤boundary → targets (·≤boundary) i

theorem step_crosses_barrier
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (before : (s.core.lanes owner).pc≤boundary) (after : boundary<(out.state.core.lanes owner).pc) :
    ∃ key, Event.barrier (.completion key)∈out.events ∧ key.site=boundary := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch effect =>
    by_cases same : owner=selected
    · subst owner
      have strictlyBefore : (s.core.lanes selected).pc<boundary := by
        by_contra past
        have atBarrier : (s.core.lanes selected).pc=boundary := by omega
        rw [atBarrier,barrier] at fetch
        cases fetch
      have upper := eval_upper effect strictlyBefore (stops _ _ fetch before)
      simp only [update,setLane,Function.update_self] at after
      omega
    · simp [update,setLane,Function.update,same] at after
      omega
  | @sync _ resource running fresh fetch =>
    have released : (Ptx.Barrier.step (barrierConfig cfg s.core selected) s.core.barrier
        (barrierRequest cfg s.core selected resource)).disposition=.released := by
      by_contra blocked
      simp only [synchronize] at after
      split at after <;> simp only at after
      · omega
      · omega
      · exact False.elim (blocked (by assumption))
    have alignedPC := release_aligned cfg s.core selected resource aligned released owner
    have atBarrier : (s.core.lanes owner).pc=boundary := by
      simp only [synchronize,released,advance] at after
      omega
    let request := barrierRequest cfg s.core selected resource
    obtain ⟨same,fresh,complete⟩ := (Ptx.Barrier.released_iff _ _ _).mp released
    refine ⟨request.key,?_,?_⟩
    · simp only [synchronize,released]
      apply List.mem_map.mpr
      refine ⟨.completion request.key,?_,rfl⟩
      exact (Ptx.Barrier.completion_event_iff _ _ _ _).mpr ⟨same,fresh,complete,rfl⟩
    · change (s.core.lanes selected).pc=boundary
      exact alignedPC.symm.trans atBarrier

/-- Passing a protected barrier entails a completion emitted by the fetched
execution, rather than a supplied phase boundary. -/
theorem crossed_barrier
    (run : Runs cfg ctx program start events indices final) (aligned : Aligned start.core)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (before : (start.core.lanes owner).pc≤boundary) (after : boundary<(final.core.lanes owner).pc) :
    ∃ key, Event.barrier (.completion key)∈events ∧ key.site=boundary := by
  induction run with
  | nil => omega
  | @cons selected s out restWords restIndices final one rest ih =>
    by_cases passed : boundary<(out.state.core.lanes owner).pc
    · obtain ⟨key,found,site⟩ := step_crosses_barrier one aligned barrier stops before passed
      exact ⟨key,List.mem_append_left _ found,site⟩
    · obtain ⟨key,found,site⟩ := ih (step_aligned one aligned) (by omega) after
      exact ⟨key,List.mem_append_right _ found,site⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
