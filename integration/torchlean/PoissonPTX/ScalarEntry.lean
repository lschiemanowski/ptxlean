import PoissonPTX.ScalarSegments
import PoissonPTX.ScalarDeterministic

namespace PtxTorchLean.Poisson.PTX.Scalar

def prologue : List Instr := [.base (.context 0 .arena),.base (.context 14 .lane),.base (.context 15 .group)]
def setup (ctx : Kernel.Context) (s : Flow.State) : Flow.State :=
  {s with core:=assign (assign (assign s.core 0 ctx.arena) 14 (ctx.lane.setWidth 64)) 15 (ctx.group.setWidth 64)}

def program (body : List Instr) : List Instr := prologue++body++[.base .ret]

theorem setup_trace (running : s.halted=false) : Sequence ctx prologue s (setup ctx s) := by
  exact .cons running (.base (.simple (by intro op h; cases h)))
    (.cons running (.base (.simple (by intro op h; cases h)))
      (.cons running (.base (.simple (by intro op h; cases h))) .nil))

theorem prologue_plain : ∀ i∈prologue, noFP i=true := by simp [prologue,noFP,Flow.noFP]

theorem prologue_segment : ∀ i∈prologue, segment i=true := by simp [prologue,segment,Flow.segment]

theorem setup_frame : (setup ctx s).core.global=s.core.global ∧
    (setup ctx s).core.globalStart=s.core.globalStart ∧ (setup ctx s).core.globalBytes=s.core.globalBytes ∧
    (setup ctx s).core.regs 0=ctx.arena ∧ (setup ctx s).halted=s.halted := by
  simp [setup,assign,advance]

theorem entry_result (run : Runs ctx (program body) s final) (pc : s.core.pc=0)
    (running : s.halted=false) (done : final.halted=true) (plain : ∀ i∈body, segment i=true) :
    ∃ middle, Sequence ctx body (setup ctx s) middle ∧ final=Flow.halt middle := by
  obtain ⟨middle,trace,eq⟩ := completed_body (body:=prologue++body)
    (by intro i member; rcases List.mem_append.mp member with h|h; exact prologue_segment i h; exact plain i h)
    run pc running done
  obtain ⟨first,header,rest⟩ := sequence_split prologue body trace
  have same := sequence_unique header (setup_trace running) prologue_plain
  subst first
  exact ⟨middle,rest,eq⟩

theorem entry_executes (trace : Sequence ctx body (setup ctx s) middle)
    (plain : ∀ i∈body, segment i=true) (pc : s.core.pc=0) (running : s.halted=false) :
    Runs ctx (program body) s (Flow.halt middle) := by
  exact executes_body (sequence_append (setup_trace running) trace)
    (by intro i member; rcases List.mem_append.mp member with h|h; exact prologue_segment i h; exact plain i h) pc running

end PtxTorchLean.Poisson.PTX.Scalar
