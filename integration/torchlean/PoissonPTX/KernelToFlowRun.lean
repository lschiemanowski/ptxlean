import PoissonPTX.KernelToFlow

namespace PtxTorchLean.Poisson.PTX.Kernel.ToFlow

/-- Every old kernel step has the same effect in the indexed representation. -/
theorem eval_lift (actual : Kernel.Eval ctx i s t) :
    Flow.Eval ctx (instruction i) (state s) (state t) := by
  cases actual with
  | data actual => exact .data (.data actual)
  | simple ordinary =>
    cases i with
    | data op => exact False.elim (ordinary op rfl)
    | mad32 dst a scale b => exact .data .mad32
    | parameter dst => exact .simple (by intro op same; cases same)
    | lane dst => exact .simple (by intro op same; cases same)
    | group dst => exact .simple (by intro op same; cases same)
    | ret => exact .simple (by intro op same; cases same)
    | predRet =>
      cases predicate : s.predicate <;>
        simpa [instruction,state,Flow.simple,Kernel.simple,predicate,Flow.halt,Flow.next,Kernel.halt,Kernel.advance] using
          (Flow.Eval.simple (ctx:=ctx) (s:=state s) (i:=.predRet 0 true) (by intro op same; cases same))
    | ge32 src limit =>
      have same : Flow.simple ctx (instruction (.ge32 src limit)) (state s)=state (Kernel.simple ctx (.ge32 src limit) s) := by
        simp [instruction,state,Flow.simple,Flow.next,Flow.Compare.apply,Operand.eval,Kernel.u32,Kernel.simple,Kernel.advance]
        funext r
        by_cases zero : r=0 <;> simp [Function.update,zero]
      rw [← same]
      exact .simple (by intro op same; cases same)

theorem step_lift (actual : Kernel.Step ctx code s t) :
    Flow.Step ctx (code.map instruction) (state s) (state t) := by
  obtain ⟨running,i,fetch,eval⟩ := actual
  exact ⟨running,instruction i,by simp only [state,List.getElem?_map,fetch,Option.map_some],eval_lift eval⟩

theorem run_lift (actual : Kernel.Run ctx code s t) :
    Flow.Runs ctx (code.map instruction) (state s) (state t) := by
  induction actual with
  | stop step _ => exact .cons (step_lift step) .nil
  | next step _ _ ih => exact .cons (step_lift step) ih

theorem step_project (actual : Flow.Step ctx (code.map instruction) s t) :
    Kernel.Step ctx code (project s) (project t) := by
  obtain ⟨running,i,fetch,eval⟩ := actual
  rw [List.getElem?_map] at fetch
  obtain ⟨old,found,rfl⟩ := Option.map_eq_some_iff.mp fetch
  exact ⟨running,old,found,eval_project eval⟩

theorem halted_run (actual : Flow.Runs ctx code s t) (halted : s.halted=true) : t=s := by
  cases actual with
  | nil => rfl
  | cons step _ => have running := step.1; rw [halted] at running; contradiction

/-- A completed indexed execution projects to the original fetched kernel
execution. Return and instruction selection are retained in both directions. -/
theorem run_project (actual : Flow.Runs ctx (code.map instruction) s t)
    (running : s.halted=false) (done : t.halted=true) :
    Kernel.Run ctx code (project s) (project t) := by
  induction actual with
  | nil => rw [running] at done; contradiction
  | @cons s middle t step rest ih =>
    by_cases stopped : middle.halted=true
    · have same := halted_run rest stopped
      subst t
      exact .stop (step_project step) stopped
    · have continues : middle.halted=false := by cases h : middle.halted <;> simp_all
      exact .next (step_project step) continues (ih continues done)

end PtxTorchLean.Poisson.PTX.Kernel.ToFlow
