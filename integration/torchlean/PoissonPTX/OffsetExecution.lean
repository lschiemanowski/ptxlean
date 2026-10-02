import PoissonPTX.RelocateKernel

namespace PtxTorchLean.Poisson.PTX.Concurrent.AtOffset

/-- Fetched execution at an absolute instruction origin. The counter, records
and barrier sites remain absolute; only list indexing subtracts the origin.
Branch destinations are relocated before dispatch. -/
inductive Step (origin : Nat) (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) : Fin n → WithTail.State n → WithTail.Outcome n → Prop where
  | front (running : s.halted thread=false) (fresh : s.core.barrier.arrived thread=false)
      (past : origin≤(s.core.lanes thread).pc)
      (fetch : front[(s.core.lanes thread).pc-origin]?=some i)
      (dispatch : Concurrent.Dispatch cfg thread (Relocate.instruction origin i) s.core out) :
      Step origin cfg ctx front tail thread s ⟨{s with core:=out.state},out.events⟩
  | tail (running : s.halted thread=false) (fresh : s.core.barrier.arrived thread=false)
      (past : origin+front.length≤(s.core.lanes thread).pc)
      (fetch : tail[(s.core.lanes thread).pc-(origin+front.length)]?=some i)
      (eval : Kernel.Eval (ctx thread) i (WithTail.lane s thread) next) :
      Step origin cfg ctx front tail thread s
        ⟨WithTail.update s thread next,(WithTail.access i (WithTail.lane s thread) next).toList.map (Event.data thread)⟩

inductive Runs (origin : Nat) (cfg : Config n) (ctx : Fin n → Kernel.Context)
    (front : List Instr) (tail : List Kernel.Instr) : WithTail.State n → List (Event n) → WithTail.State n → Prop where
  | nil : Runs origin cfg ctx front tail s [] s
  | cons : Step origin cfg ctx front tail thread s out → Runs origin cfg ctx front tail out.state rest final →
      Runs origin cfg ctx front tail s (out.events++rest) final

variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {s start final : WithTail.State n} {out : WithTail.Outcome n}

theorem aligned (step : Step origin cfg ctx front tail thread s out) (aligned : Concurrent.Aligned s.core) :
    Concurrent.Aligned out.state.core := by
  cases step with
  | front _ fresh _ _ dispatch =>
    generalize hi : Relocate.instruction origin _=i at dispatch
    cases dispatch with
    | data => exact setLane_aligned aligned fresh _
    | skip => exact setLane_aligned aligned fresh _
    | sync => exact synchronize_aligned _ _ _ _ aligned
  | tail _ fresh _ _ _ => exact setLane_aligned aligned fresh _

/-- A local fetched step relocates to an absolute fetched step. -/
theorem step_forward (step : WithTail.Step cfg ctx front tail thread s out) :
    Step origin cfg ctx front tail thread (Relocate.tailState origin s) (Relocate.tailOutcome origin out) := by
  cases step with
  | front running one =>
    obtain ⟨fresh,i,fetch,dispatch⟩ := one
    have next := Step.front (s:=Relocate.tailState origin s) (origin:=origin) (front:=front)
      (tail:=tail) (ctx:=ctx) (cfg:=cfg) running fresh (by simp [Relocate.tailState,Relocate.core,Relocate.scalar])
      (by simpa [Relocate.tailState,Relocate.core,Relocate.scalar] using fetch)
      (Relocate.dispatch dispatch)
    simpa only [Relocate.tailOutcome,Relocate.tailState,Relocate.outcome] using next
  | tail running fresh past fetch eval =>
    rename_i i actualNext
    have bound : origin+front.length≤((Relocate.tailState origin s).core.lanes thread).pc := by
      change origin+front.length≤(s.core.lanes thread).pc+origin; omega
    have seen : tail[((Relocate.tailState origin s).core.lanes thread).pc-(origin+front.length)]?=some i := by
      simpa [Relocate.tailState,Relocate.core,Relocate.scalar,Nat.add_sub_add_right,Nat.add_comm origin] using fetch
    have next := Step.tail (s:=Relocate.tailState origin s) (origin:=origin) (front:=front)
      (tail:=tail) (ctx:=ctx) (cfg:=cfg) running fresh bound seen (Relocate.kernel_eval (offset:=origin) eval)
    simpa [Relocate.tailOutcome,Relocate.event,List.map_map,Function.comp_def,Option.toList_map] using next

/-- Recover local execution from every absolute step starting in a relocated
state. No schedule, numerical result or intermediate state is supplied. -/
theorem step_back (step : Step origin cfg ctx front tail thread (Relocate.tailState origin s) out) :
    ∃ localOut, out=Relocate.tailOutcome origin localOut ∧ WithTail.Step cfg ctx front tail thread s localOut := by
  cases step with
  | front running fresh past fetch dispatch =>
    obtain ⟨localOut,same,localStep⟩ := Relocate.dispatch_back dispatch
    refine ⟨⟨{s with core:=localOut.state},localOut.events⟩,?_,WithTail.Step.front running ⟨fresh,_,?_,localStep⟩⟩
    · simp [same,Relocate.tailOutcome,Relocate.tailState,Relocate.outcome]
    · simpa [Relocate.tailState,Relocate.core,Relocate.scalar] using fetch
  | tail running fresh past fetch eval =>
    rename_i i actualNext
    obtain ⟨next,same,localStep⟩ := Relocate.kernel_back (s:=WithTail.lane s thread) (offset:=origin) (by simpa only [Relocate.tail_lane] using eval)
    have bound : front.length≤(s.core.lanes thread).pc := by
      change origin+front.length≤(s.core.lanes thread).pc+origin at past; omega
    have seen : tail[(s.core.lanes thread).pc-front.length]?=some i := by
      simpa [Relocate.tailState,Relocate.core,Relocate.scalar,Nat.add_sub_add_right,Nat.add_comm origin] using fetch
    refine ⟨_,?_,WithTail.Step.tail running fresh bound seen localStep⟩
    simp [same,Relocate.tailOutcome,Relocate.event,List.map_map,Function.comp_def,Option.toList_map]

theorem run_forward (run : WithTail.Runs cfg ctx front tail s events t) :
    Runs origin cfg ctx front tail (Relocate.tailState origin s) (events.map (Relocate.event origin))
      (Relocate.tailState origin t) := by
  induction run with
  | nil => exact .nil
  | cons one rest ih => simpa [List.map_append,Relocate.tailOutcome] using Runs.cons (step_forward one) ih

theorem run_back (run : Runs origin cfg ctx front tail start events final)
    (same : start=Relocate.tailState origin s) :
    ∃ localEvents localFinal, events=localEvents.map (Relocate.event origin) ∧
      final=Relocate.tailState origin localFinal ∧ WithTail.Runs cfg ctx front tail s localEvents localFinal := by
  induction run generalizing s with
  | nil => exact ⟨[],s,rfl,same,.nil⟩
  | cons one rest ih =>
    obtain ⟨localOut,outEq,localStep⟩ := step_back (same ▸ one)
    obtain ⟨last,done,eventsEq,finalEq,path⟩ := ih (s:=localOut.state) (by rw [outEq]; rfl)
    refine ⟨localOut.events++last,done,?_,finalEq,.cons localStep path⟩
    simp [outEq,eventsEq,Relocate.tailOutcome,List.map_append]

end PtxTorchLean.Poisson.PTX.Concurrent.AtOffset
