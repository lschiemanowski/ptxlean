import PoissonPTX.ScalarExecution

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- Recover each nonbranching instruction from the actual fetched execution. -/
theorem peel_segment (code pre post : List Instr) (plain : ∀ i∈code, segment i=true)
    (run : Runs ctx (pre++code++post) s t) (pc : s.core.pc=pre.length)
    (running : s.halted=false) (done : t.halted=true) :
    ∃ middle, Sequence ctx code s middle ∧ middle.core.pc=pre.length+code.length ∧
      middle.halted=false ∧ Runs ctx (pre++code++post) middle t := by
  induction code generalizing pre s with
  | nil => exact ⟨s,.nil,by simpa using pc,running,run⟩
  | cons i code ih =>
    cases run with
    | nil => simp [running] at done
    | @cons s middle t step rest =>
      obtain ⟨alive,op,fetch,actual⟩ := step
      have same : op=i := by simpa [pc] using fetch.symm
      subst op
      have nextPC : middle.core.pc=(pre++[i]).length := by
        rw [segment_pc actual (plain i (by simp)),pc]; simp
      have nextRunning : middle.halted=false := (segment_running actual (plain i (by simp))).trans running
      obtain ⟨final,trace,finalPC,finalRunning,tail⟩ := ih (pre++[i])
        (fun j member => plain j (by simp [member])) (by simpa [List.append_assoc] using rest) nextPC nextRunning
      refine ⟨final,.cons alive actual trace,?_,finalRunning,?_⟩
      · simp only [List.length_append,List.length_cons,List.length_nil] at finalPC ⊢; omega
      · simpa [List.append_assoc] using tail

theorem halted_result (run : Runs ctx program s t) (done : s.halted=true) : t=s := by
  cases run with
  | nil => rfl
  | cons step rest => simp [Step,done] at step

theorem completed_body (plain : ∀ i∈body, segment i=true)
    (run : Runs ctx (body++[.base .ret]) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true) :
    ∃ middle, Sequence ctx body s middle ∧ t=Flow.halt middle := by
  obtain ⟨middle,trace,position,alive,tail⟩ := peel_segment body [] [.base .ret] plain run pc running done
  cases tail with
  | nil => simp [alive] at done
  | @cons middle next t step rest =>
    obtain ⟨_,op,fetch,actual⟩ := step
    have same : op=.base .ret := by simpa [position] using fetch.symm
    subst op
    cases actual with
    | simple ordinary => simp [Scalar.ordinary] at ordinary
    | base returned =>
      have eq : next=Flow.halt middle := by
        cases returned with
        | simple ordinary => rfl
      subst next
      exact ⟨middle,trace,halted_result rest rfl⟩

theorem sequence_run (trace : Sequence ctx code s t) (plain : ∀ i∈code, segment i=true)
    (pre post : List Instr) (pc : s.core.pc=pre.length) : Runs ctx (pre++code++post) s t := by
  induction trace generalizing pre with
  | nil => exact .nil
  | @cons i s middle code t running step rest ih =>
    apply Runs.cons (s:=s) (t:=middle) ⟨running,i,by simp [pc],step⟩
    have nextPC : middle.core.pc=(pre++[i]).length := by
      rw [segment_pc step (plain i (by simp)),pc]; simp
    simpa [List.append_assoc] using ih (fun j member => plain j (by simp [member])) (pre++[i]) nextPC

theorem append (one : Runs ctx program s t) (two : Runs ctx program t u) : Runs ctx program s u := by
  induction one with
  | nil => exact two
  | cons step rest ih => exact .cons step (ih two)

theorem executes_body (trace : Sequence ctx body s t) (plain : ∀ i∈body, segment i=true)
    (pc : s.core.pc=0) (running : s.halted=false) : Runs ctx (body++[.base .ret]) s (Flow.halt t) := by
  have bodyRun := sequence_run trace plain [] [.base .ret] pc
  have tPC : t.core.pc=body.length := by simpa [pc] using sequence_pc trace plain
  have tRunning := (sequence_running trace plain).trans running
  exact append bodyRun (.cons ⟨tRunning,.base .ret,by simp [tPC],.base (.simple (by intro op h; cases h))⟩ .nil)

end PtxTorchLean.Poisson.PTX.Scalar
