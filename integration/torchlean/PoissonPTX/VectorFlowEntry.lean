import PoissonPTX.AssemblyPrologue
import PoissonPTX.ControlFlowLoop
import PoissonPTX.ControlFlowSegments

namespace PtxTorchLean.Poisson.PTX.VectorFlowEntry

def program (count : BitVec 32) (body : List Flow.Instr) : List Flow.Instr :=
  Assembly.prologue count ++ body ++ [.ret]

theorem setup_run (pc : s.core.pc=0) (running : s.halted=false) :
    Flow.Runs ctx (program count body) s (Assembly.setup ctx count s) := by
  simpa [program] using Flow.sequence_run
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.linear]) [] (body++[.ret]) pc

theorem inactive (run : Flow.Runs ctx (program count body) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) : t=Assembly.setup ctx count s := by
  obtain ⟨k,counted⟩ := Flow.counted run
  obtain ⟨remaining,_,rest⟩ := Flow.consume_sequence
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.noFP,Indexed.noFP]) (by simp [Assembly.prologue,Flow.linear])
    (pre:=[]) (post:=body++[.ret])
    (by simpa [program] using counted) pc done
  exact Flow.Loop.halted_eq rest (Assembly.setup_inactive inactive)

/-- Recover a mixed arithmetic/predicate body from the actual active entry.
The prologue establishes the live path; no intermediate registers are assumed. -/
theorem completed_body (run : Flow.Runs ctx (program count body) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count) (plain : ∀ i∈body, Flow.segment i=true) :
    ∃ middle, Flow.Sequence ctx body (Assembly.setup ctx count s) middle ∧ t=Flow.halt middle := by
  obtain ⟨k,counted⟩ := Flow.counted run
  obtain ⟨remaining,_,rest⟩ := Flow.consume_sequence
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.noFP,Indexed.noFP]) (by simp [Assembly.prologue,Flow.linear])
    (pre:=[]) (post:=body++[.ret])
    (by simpa [program] using counted) pc done
  have setupPC : (Assembly.setup ctx count s).core.pc=(Assembly.prologue count).length := by
    simp [Assembly.setup,Assembly.prologue,pc]
  obtain ⟨steps,middle,_,sequence,bodyPC,alive,last⟩ := Flow.peel_segment body (Assembly.prologue count) [.ret]
    plain (by simpa only [List.nil_append,List.append_assoc] using rest) setupPC (Assembly.setup_active (s:=s) live) done
  have retFetch : (program count body)[middle.core.pc]?=some .ret := by rw [bodyPC]; simp [program]
  obtain ⟨left,_,tailRun⟩ := Flow.peel_simple last alive done retFetch (by intro op same; cases same)
  exact ⟨middle,sequence,Flow.Loop.halted_eq tailRun rfl⟩

theorem executes (pc : s.core.pc=0) (running : s.halted=false) (live : Kernel.Residual.live ctx count)
    (plain : ∀ i∈body, Flow.segment i=true)
    (bodyRun : Flow.Sequence ctx body (Assembly.setup ctx count s) middle) :
    Flow.Runs ctx (program count body) s (Flow.halt middle) := by
  have first := setup_run (body:=body) (ctx:=ctx) (count:=count) pc running
  have setupPC : (Assembly.setup ctx count s).core.pc=(Assembly.prologue count).length := by simp [Assembly.setup,Assembly.prologue,pc]
  have second := Flow.sequence_run bodyRun (fun i member => Flow.segment_linear (plain i member))
    (Assembly.prologue count) [.ret] setupPC
  have alive : middle.halted=false := (Flow.sequence_running bodyRun plain).trans (Assembly.setup_active (s:=s) live)
  have retFetch : (program count body)[middle.core.pc]?=some .ret := by
    rw [Flow.sequence_pc bodyRun (fun i member => Flow.segment_linear (plain i member)),setupPC]
    simp [program]
  exact Flow.append first (Flow.append second (.cons ⟨alive,.ret,retFetch,.simple (by intro op same; cases same)⟩ .nil))

end PtxTorchLean.Poisson.PTX.VectorFlowEntry
