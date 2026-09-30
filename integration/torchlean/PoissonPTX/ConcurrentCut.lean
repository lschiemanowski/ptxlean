import PoissonPTX.ConcurrentOrder

namespace PtxTorchLean.Poisson.PTX.Concurrent.Cut
open Ptx
variable {n : Nat} {cfg : Config n} {start final : State n}

/-- Crossing a protected barrier advances every participant from that same site.
The boundary state is derived from the fetched transition, not supplied. -/
theorem crossing_state {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (barrier : program[boundary]?=some (.sync 0))
    (stops : StopsAt program boundary) (thread : Fin n)
    (before : (s.lanes thread).pc≤boundary) (after : boundary<(out.state.lanes thread).pc) :
    ∀ t, (out.state.lanes t).pc=boundary+1 := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    by_cases eq : thread=selected
    · subst thread
      have nextPC := data_pc hd
      simp only [setLane,Function.update_self] at after
      have pc : (s.lanes selected).pc=boundary := by omega
      rw [pc,barrier] at fetch; simp at fetch
    · simp [setLane,Function.update,eq] at after
      omega
  | skip =>
    by_cases eq : thread=selected
    · subst thread
      have targetBound := stops _ _ _ fetch before
      simp only [setLane,Function.update_self] at after
      split at after
      · have pc : (s.lanes selected).pc=boundary := by omega
        rw [pc,barrier] at fetch; simp at fetch
      · omega
    · simp [setLane,Function.update,eq] at after
      omega
  | @sync resource =>
    let c := barrierConfig cfg s selected
    let r := barrierRequest cfg s selected resource
    by_cases same : r.key=Barrier.key c s.barrier
    · have notOld : ¬s.barrier.arrived r.thread=true := by simp [r,barrierRequest,fresh]
      by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      · have rel : (Barrier.step c s.barrier r).disposition=.released := by
          simp [Barrier.step,same,notOld,complete]
        have pcs := release_aligned cfg s selected resource aligned rel thread
        have pc : (s.lanes thread).pc=boundary := by
          simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
            ← show r=barrierRequest cfg s selected resource from rfl,
            Barrier.step,same,notOld,complete,advance] at after
          omega
        intro t
        have allPC := release_aligned cfg s selected resource aligned rel t
        have atSite : (s.lanes t).pc=boundary := allPC.trans (pcs.symm.trans pc)
        simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
          ← show r=barrierRequest cfg s selected resource from rfl,
          Barrier.step,same,notOld,complete,advance,atSite]
      · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
          ← show r=barrierRequest cfg s selected resource from rfl,
          Barrier.step,same,notOld,complete] at after
        omega
    · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
        ← show r=barrierRequest cfg s selected resource from rfl,
        Barrier.step,same] at after
      omega

/-- Before the cut, fetches from extended code are fetches from its prefix. -/
theorem step_prefix (step : Step cfg (precode++suffix) thread s out)
    (bound : (s.lanes thread).pc<precode.length) : Step cfg precode thread s out := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  exact ⟨fresh,i,by simpa [List.getElem?_append_left bound] using fetch,dispatch⟩

/-- Recover an actual prefix execution and continuation at a protected final
barrier of the prefix. No schedule or intermediate state is an input. -/
theorem split_run (run : Runs cfg (precode++suffix) start events final)
    (aligned : Aligned start)
    (size : precode.length=boundary+1)
    (barrier : (precode++suffix)[boundary]?=some (.sync 0))
    (stops : StopsAt (precode++suffix) boundary)
    (initial : ∀ t, (start.lanes t).pc≤boundary)
    (thread : Fin n) (after : boundary<(final.lanes thread).pc) :
    ∃ before later ready,
      events=before++later ∧ Runs cfg precode start before ready ∧
      (∀ t, (ready.lanes t).pc=precode.length) ∧
      Runs cfg (precode++suffix) ready later final := by
  induction run with
  | nil => have := initial thread; omega
  | @cons selected current out rest final step tail ih =>
    have early := step_prefix step (by have := initial selected; omega)
    by_cases crossed : ∃ t, boundary<(out.state.lanes t).pc
    · obtain ⟨t,ht⟩ := crossed
      have atCut := crossing_state step aligned barrier stops t (initial t) ht
      exact ⟨out.events,rest,out.state,rfl,by simpa using Runs.cons early Runs.nil,
        fun t => (atCut t).trans size.symm,tail⟩
    · have bounds : ∀ t, (out.state.lanes t).pc≤boundary := by
        intro t; have := not_exists.mp crossed t; omega
      obtain ⟨before,later,ready,eventsEq,first,done,last⟩ :=
        ih (step_aligned step aligned) bounds after
      exact ⟨out.events++before,later,ready,by simp [eventsEq,List.append_assoc],
        .cons early first,done,last⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Cut
