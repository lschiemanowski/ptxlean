import PoissonPTX.BarrierClock
import PoissonPTX.CellEntry

namespace PtxTorchLean.Poisson.PTX.Concurrent.Clock
open Ptx

/-- Barrier history facts composable across arbitrary instruction schedules. -/
structure Progress (s t : Barrier.State n) (events : List (Event n)) : Prop where
  monotone : s.generation≤t.generation
  carries : ∀ event, Before s event → Before t event
  emitted : ∀ event, Event.barrier event∈events → s.generation≤generation event ∧ Before t event

theorem Progress.refl (s : Barrier.State n) : Progress s s [] :=
  ⟨le_rfl,fun _ h => h,by intro event member; simp at member⟩

theorem Progress.trans (first : Progress s t before) (second : Progress t u after) :
    Progress s u (before++after) := by
  refine ⟨first.monotone.trans second.monotone,fun e h => second.carries e (first.carries e h),?_⟩
  intro event member
  rcases List.mem_append.mp member with early | late
  · have h := first.emitted event early
    exact ⟨h.1,second.carries event h.2⟩
  · have h := second.emitted event late
    exact ⟨first.monotone.trans h.1,h.2⟩

theorem unchanged (same : t=s) (none : ∀ event, Event.barrier event∉events) : Progress s t events := by
  subst t
  exact ⟨le_rfl,fun _ h => h,fun e h => False.elim (none e h)⟩

theorem sync_barrier (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) :
    (synchronize cfg s thread resource).state.barrier=
      (Barrier.step (barrierConfig cfg s thread) s.barrier (barrierRequest cfg s thread resource)).state := by
  by_cases same : (barrierRequest cfg s thread resource).key=Barrier.key (barrierConfig cfg s thread) s.barrier <;>
    by_cases old : s.barrier.arrived (barrierRequest cfg s thread resource).thread=true <;>
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier (barrierRequest cfg s thread resource).thread) <;>
    simp [synchronize,Barrier.step,same,old,complete]

theorem sync_events (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) :
    (synchronize cfg s thread resource).events=
      (Barrier.step (barrierConfig cfg s thread) s.barrier (barrierRequest cfg s thread resource)).events.map Event.barrier := by
  by_cases same : (barrierRequest cfg s thread resource).key=Barrier.key (barrierConfig cfg s thread) s.barrier <;>
    by_cases old : s.barrier.arrived (barrierRequest cfg s thread resource).thread=true <;>
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier (barrierRequest cfg s thread resource).thread) <;>
    simp [synchronize,Barrier.step,same,old,complete]

theorem sync_progress (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16) :
    Progress s.barrier (synchronize cfg s thread resource).state.barrier (synchronize cfg s thread resource).events := by
  rw [sync_barrier,sync_events]
  refine ⟨monotone _ _ _,fun event h => carry h _ _,?_⟩
  intro event member
  have actual : event∈(Barrier.step (barrierConfig cfg s thread) s.barrier (barrierRequest cfg s thread resource)).events := by
    simpa using member
  have h := emitted actual
  exact ⟨by omega,h.2⟩

variable {n : Nat} {cfg : Config n} {s : State n} {out : Outcome n}

theorem dispatch_progress (step : Dispatch cfg thread i s out) : Progress s.barrier out.state.barrier out.events := by
  cases step with
  | data => exact unchanged rfl (by intro event; simp)
  | skip => exact unchanged rfl (by intro event; simp)
  | sync => exact sync_progress _ _ _ _

end PtxTorchLean.Poisson.PTX.Concurrent.Clock

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Every prefix event remains accounted for through the actual barrier reset. -/
theorem clock_step (step : Step cfg ctx code thread s out) :
    Concurrent.Clock.Progress s.core.barrier out.state.core.barrier out.events := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => exact Concurrent.Clock.unchanged rfl (by intro event; simp)
  | gather => exact Concurrent.Clock.unchanged rfl (by intro event; simp)
  | skip => exact Concurrent.Clock.unchanged rfl (by intro event; simp)
  | sync => exact Concurrent.Clock.sync_progress _ _ _ _

theorem clock_run (run : Runs cfg ctx code s events indices t) :
    Concurrent.Clock.Progress s.core.barrier t.core.barrier events := by
  induction run with
  | nil => exact Concurrent.Clock.Progress.refl _
  | cons one rest ih => exact (clock_step one).trans ih

end PtxTorchLean.Poisson.PTX.CellEntry

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail

theorem clock_step (step : Step cfg ctx front tail thread s out) :
    Clock.Progress s.core.barrier out.state.core.barrier out.events := by
  cases step with
  | front _ one => obtain ⟨fresh,i,fetch,dispatch⟩ := one; exact Clock.dispatch_progress dispatch
  | tail => exact Clock.unchanged rfl (by intro event; simp)

theorem clock_run (run : Runs cfg ctx front tail s events t) :
    Clock.Progress s.core.barrier t.core.barrier events := by
  induction run with
  | nil => exact Clock.Progress.refl _
  | cons one rest ih => exact (clock_step one).trans ih

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail
