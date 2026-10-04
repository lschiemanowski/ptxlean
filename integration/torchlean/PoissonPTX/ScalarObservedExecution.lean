import PoissonPTX.ScalarRecorded
import PoissonPTX.ScalarEntry

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

theorem peel_segment (code pre post : List Instr) (plain : ∀ i∈code, segment i=true)
    (run : Runs ctx (pre++code++post) s events t) (pc : s.core.pc=pre.length)
    (running : s.halted=false) (done : t.halted=true) :
    ∃ middle first rest, Sequence ctx code s first middle ∧ middle.core.pc=pre.length+code.length ∧
      middle.halted=false ∧ Runs ctx (pre++code++post) middle rest t ∧ events=first++rest := by
  induction code generalizing pre s events with
  | nil => exact ⟨s,[],events,.nil,by simpa using pc,running,run,rfl⟩
  | cons i code ih =>
    cases run with
    | nil => simp [running] at done
    | @cons s next first rest t step tail =>
      obtain ⟨alive,op,fetch,actual⟩ := step
      have same : op=i := by simpa [pc] using fetch.symm
      subst op
      have nextPC : next.core.pc=(pre++[i]).length := by
        rw [eval_position actual (plain i (by simp)),pc]; simp
      have nextRunning : next.halted=false := (eval_running actual (plain i (by simp))).trans running
      obtain ⟨middle,body,remaining,trace,position,awake,final,whole⟩ := ih (pre++[i])
        (fun j member => plain j (by simp [member])) (by simpa [List.append_assoc] using tail) nextPC nextRunning
      refine ⟨middle,first++body,remaining,.cons alive actual trace,?_,awake,?_,?_⟩
      · simp only [List.length_append,List.length_cons,List.length_nil] at position ⊢; omega
      · simpa [List.append_assoc] using final
      · simp only [whole,List.append_assoc]

theorem halted_result (run : Runs ctx code s events t) (done : s.halted=true) : t=s ∧ events=[] := by
  cases run with
  | nil => exact ⟨rfl,rfl⟩
  | cons step rest => simp [Step,done] at step

theorem completed_body (plain : ∀ i∈body, segment i=true)
    (run : Runs ctx (body++[.base .ret]) s events t) (pc : s.core.pc=0)
    (running : s.halted=false) (done : t.halted=true) :
    ∃ middle, Sequence ctx body s events middle ∧ t=Flow.halt middle := by
  obtain ⟨middle,first,rest,trace,position,awake,tail,whole⟩ := peel_segment body [] [.base .ret] plain run pc running done
  cases tail with
  | nil => simp [awake] at done
  | @cons middle next head rest t step tail =>
    obtain ⟨_,op,fetch,actual⟩ := step
    have same : op=.base .ret := by simpa [position] using fetch.symm
    subst op
    cases actual with
    | extra plain => simp [extra] at plain
    | base returned =>
      cases returned with
      | simple ordinary =>
        obtain ⟨same,empty⟩ := halted_result tail rfl
        have emptyRest : events=first := by simpa [empty,records] using whole
        rw [emptyRest]
        exact ⟨middle,trace,same⟩

theorem entry_result (run : Runs ctx (program body) s events final) (pc : s.core.pc=0)
    (running : s.halted=false) (done : final.halted=true) (plain : ∀ i∈body, segment i=true) :
    ∃ middle, Sequence ctx body (setup ctx s) events middle ∧ final=Flow.halt middle := by
  have allPlain : ∀ i∈prologue++body, segment i=true := by
    intro i mem; rcases List.mem_append.mp mem with h|h; exact prologue_segment i h; exact plain i h
  obtain ⟨middle,trace,last⟩ := completed_body allPlain run pc running done
  obtain ⟨header,first,rest,pre,bodyRun,whole⟩ := sequence_split prologue body trace
  obtain ⟨empty,ordinary⟩ := no_memory_sequence pre (by simp [prologue,noMemory])
  have same := Scalar.sequence_unique ordinary (setup_trace running) prologue_plain
  rw [same] at bodyRun
  have eventEq : events=rest := by simpa [empty] using whole
  rw [eventEq]
  exact ⟨middle,bodyRun,last⟩

theorem sequence_run (trace : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true)
    (pre post : List Instr) (pc : s.core.pc=pre.length) : Runs ctx (pre++code++post) s events t := by
  induction trace generalizing pre with
  | nil => exact .nil
  | @cons i s middle first code rest t running step tail ih =>
    apply Runs.cons (s:=s) (middle:=middle) ⟨running,i,by simp [pc],step⟩
    have nextPC : middle.core.pc=(pre++[i]).length := by
      rw [eval_position step (plain i (by simp)),pc]; simp
    simpa [List.append_assoc] using ih (fun i member => plain i (by simp [member])) (pre++[i]) nextPC

theorem append (one : Runs ctx code s first middle) (two : Runs ctx code middle rest t) :
    Runs ctx code s (first++rest) t := by
  induction one with
  | nil => exact two
  | cons step tail ih => simpa only [List.append_assoc] using Runs.cons step (ih two)

theorem entry_executes (trace : Sequence ctx body (setup ctx s) events middle)
    (plain : ∀ i∈body, segment i=true) (pc : s.core.pc=0) (running : s.halted=false) :
    Runs ctx (program body) s events (Flow.halt middle) := by
  obtain ⟨header,headerRun⟩ := sequence_witness (setup_trace (ctx:=ctx) running)
  have empty := (no_memory_sequence headerRun (by simp [prologue,noMemory])).1
  rw [empty] at headerRun
  have all : Sequence ctx (prologue++body) s events middle := by simpa using sequence_append headerRun trace
  have allPlain : ∀ i∈prologue++body, segment i=true := by
    intro i mem; rcases List.mem_append.mp mem with h|h; exact prologue_segment i h; exact plain i h
  have bodyRun := sequence_run all allPlain [] [.base .ret] pc
  have finalPC : middle.core.pc=(prologue++body).length := by simpa [pc] using sequence_position all allPlain
  have finalRunning := (sequence_running all allPlain).trans running
  have returned : Runs ctx (program body) middle [] (Flow.halt middle) :=
    .cons ⟨finalRunning,.base .ret,by simp [program,finalPC],.base (.simple (by intro op h; cases h))⟩ .nil
  simpa [program,List.append_assoc] using append bodyRun returned

end PtxTorchLean.Poisson.PTX.Scalar.Observed
