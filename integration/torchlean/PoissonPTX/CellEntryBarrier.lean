import PoissonPTX.CellEntryInputs

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx
variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

theorem skip_target {pc : Nat} (fetch : (program width cells source)[pc]?=some (.skip target)) : target=20 := by
  have member := List.mem_of_getElem? fetch
  simp only [program,List.mem_append,List.mem_map,List.mem_singleton] at member
  rcases member with ((⟨op,_,same⟩ | same) | ⟨op,_,same⟩) | same
  · cases same
  · cases same; rfl
  · cases same
  · cases same

/-- Crossing the prefix boundary requires a genuine barrier release and moves
all lanes to the same next instruction, including inactive matrix lanes. -/
theorem crossing (step : Step cfg ctx (program width cells source) selected s out)
    (aligned : Concurrent.Aligned s.core) (thread : Fin n)
    (before : (s.core.lanes thread).pc≤20) (after : 20<(out.state.core.lanes thread).pc) :
    (∀ u, (out.state.core.lanes u).pc=21) ∧ out.state.core.site=none ∧
    ∃ generation key, out.state.core.barrier=Barrier.reset (generation+1) ∧
      key.site=20 ∧ Concurrent.Event.barrier (.completion key)∈out.events := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup he =>
    by_cases same : thread=selected
    · subst thread
      have pc := setup_pc he
      simp only [setLane,Concurrent.setLane,Function.update_self,lane] at after pc
      have here : (s.core.lanes selected).pc=20 := by omega
      rw [here,barrier_fetch] at fetch; cases fetch
    · simp [setLane,Concurrent.setLane,Function.update,same] at after
      omega
  | gather he =>
    by_cases same : thread=selected
    · subst thread
      have pc := Indexed.Candidate.data_pc he
      simp only [Concurrent.setLane,Function.update_self] at after
      have here : (s.core.lanes selected).pc=20 := by omega
      rw [here,barrier_fetch] at fetch; cases fetch
    · simp [Concurrent.setLane,Function.update,same] at after
      omega
  | skip =>
    have target := skip_target fetch
    by_cases same : thread=selected
    · subst thread
      simp only [Concurrent.setLane,Function.update_self,target] at after
      split at after
      · have here : (s.core.lanes selected).pc=20 := by omega
        rw [here,barrier_fetch] at fetch; cases fetch
      · omega
    · simp [Concurrent.setLane,Function.update,same] at after
      omega
  | sync =>
    let c := Concurrent.barrierConfig cfg s.core selected
    let r := Concurrent.barrierRequest cfg s.core selected 0
    by_cases same : r.key=Barrier.key c s.core.barrier
    · have notOld : ¬s.core.barrier.arrived r.thread=true := by simp [r,Concurrent.barrierRequest,fresh]
      by_cases complete : Barrier.Complete (Barrier.mark s.core.barrier r.thread)
      · have released : (Barrier.step c s.core.barrier r).disposition=.released := by
          simp [Barrier.step,same,notOld,complete]
        have pcs := Concurrent.release_aligned cfg s.core selected 0 aligned released
        have here : (s.core.lanes thread).pc=20 := by
          simp [synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
            ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,
            Barrier.step,same,notOld,complete,advance] at after
          omega
        have every : ∀ u, (s.core.lanes u).pc=20 := fun u => (pcs u).trans ((pcs thread).symm.trans here)
        simp only [synchronize,Concurrent.synchronize,
          ← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
          ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,
          Barrier.step,same,notOld,complete,↓reduceIte]
        refine ⟨?_,rfl,s.core.barrier.generation,r.key,rfl,?_,?_⟩
        · intro u; simp [advance,every]
        · exact every selected
        · simpa using same
      · simp [synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
          ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,
          Barrier.step,same,notOld,complete] at after
        omega
    · simp [synchronize,Concurrent.synchronize,← show c=Concurrent.barrierConfig cfg s.core selected from rfl,
        ← show r=Concurrent.barrierRequest cfg s.core selected 0 from rfl,
        Barrier.step,same] at after
      omega

theorem terminal (done : ∀ thread, (s.core.lanes thread).pc=21) :
    ¬Step cfg ctx (program width cells source) selected s out := by
  rintro ⟨_,i,fetch,_⟩
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [done,program_length] at bound
  omega

theorem terminal_runs (run : Runs cfg ctx (program width cells source) s events indices t)
    (done : ∀ thread, (s.core.lanes thread).pc=21) : s=t ∧ events=[] ∧ indices=[] := by
  cases run with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons step _ => exact False.elim (terminal done step)

theorem completed_barrier (run : Runs cfg ctx (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).pc≤20)
    (thread : Fin n) (done : 20<(t.core.lanes thread).pc) :
    (∀ u, (t.core.lanes u).pc=21) ∧ t.core.site=none ∧
    ∃ generation key, t.core.barrier=Barrier.reset (generation+1) ∧
      key.site=20 ∧ Concurrent.Event.barrier (.completion key)∈events := by
  induction run with
  | nil => have := initial thread; omega
  | @cons selected s out rest indices final step tail ih =>
    by_cases crossed : ∃ u, 20<(out.state.core.lanes u).pc
    · obtain ⟨u,hu⟩ := crossed
      obtain ⟨pcs,site,generation,key,barrier,atSite,record⟩ := crossing step aligned u (initial u) hu
      obtain ⟨rfl,rfl,rfl⟩ := terminal_runs tail pcs
      exact ⟨pcs,site,generation,key,barrier,atSite,by simpa using record⟩
    · obtain ⟨pcs,site,generation,key,barrier,atSite,record⟩ :=
        ih (step_aligned step aligned) (fun u => Nat.le_of_not_gt (fun h => crossed ⟨u,h⟩)) done
      exact ⟨pcs,site,generation,key,barrier,atSite,List.mem_append_right _ record⟩

end PtxTorchLean.Poisson.PTX.CellEntry
