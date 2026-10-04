import PoissonPTX.AssemblyPrologue
import PoissonPTX.ControlFlowLoop
import PoissonPTX.IndexedScalar

namespace PtxTorchLean.Poisson.PTX.VectorEntry

def program (count : BitVec 32) (body : List Op) : List Flow.Instr :=
  Assembly.prologue count ++ (body.map Indexed.Instr.data).map Flow.Instr.data ++ [.ret]

theorem setup_run (pc : s.core.pc=0) (running : s.halted=false) :
    Flow.Runs ctx (program count body) s (Assembly.setup ctx count s) := by
  simpa [program] using Flow.sequence_run
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.linear]) [] ((body.map Indexed.Instr.data).map Flow.Instr.data++[.ret]) pc

theorem inactive (run : Flow.Runs ctx (program count body) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) : t=Assembly.setup ctx count s := by
  obtain ⟨k,counted⟩ := Flow.counted run
  obtain ⟨remaining,_,rest⟩ := Flow.consume_sequence
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.noFP,Indexed.noFP]) (by simp [Assembly.prologue,Flow.linear])
    (pre:=[]) (post:=(body.map Indexed.Instr.data).map Flow.Instr.data++[.ret])
    (by simpa [program] using counted) pc done
  exact Flow.Loop.halted_eq rest (Assembly.setup_inactive inactive)

/-- The actual fetched prologue and return surround an extracted data block.
No initial register setup or arithmetic output is assumed. -/
theorem completed_body (run : Flow.Runs ctx (program count body) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count) :
    ∃ core, PTX.Block body (Assembly.setup ctx count s).core core ∧
      t=Flow.halt {Assembly.setup ctx count s with core:=core} := by
  obtain ⟨k,counted⟩ := Flow.counted run
  obtain ⟨remaining,_,rest⟩ := Flow.consume_sequence
    (Flow.sequence_sound (Assembly.prologue_execution (ctx:=ctx) (count:=count) running))
    (by simp [Assembly.prologue,Flow.noFP,Indexed.noFP]) (by simp [Assembly.prologue,Flow.linear])
    (pre:=[]) (post:=(body.map Indexed.Instr.data).map Flow.Instr.data++[.ret])
    (by simpa [program] using counted) pc done
  have setupPC : (Assembly.setup ctx count s).core.pc=(Assembly.prologue count).length := by
    simp [Assembly.setup,Assembly.prologue,pc]
  obtain ⟨steps,core,_,block,last⟩ := Flow.peel_block (body.map Indexed.Instr.data) (Assembly.prologue count) [.ret]
    (by simpa only [List.nil_append,List.append_assoc] using rest) setupPC (Assembly.setup_active (s:=s) live) done
  have bodyPC := Indexed.block_pc block
  have retFetch : (program count body)[core.pc]?=some .ret := by
    rw [bodyPC,setupPC]
    simp [program]
  obtain ⟨left,_,tailRun⟩ := Flow.peel_simple last (Assembly.setup_active (s:=s) live) done retFetch (by intro op same; cases same)
  refine ⟨core,Indexed.underlying_block block,?_⟩
  exact Flow.Loop.halted_eq tailRun rfl

/-- Canonical body witnesses lift to complete fetched executions of active
lanes; padding lanes already have the prologue-only return path. -/
theorem executes (pc : s.core.pc=0) (running : s.halted=false) (live : Kernel.Residual.live ctx count)
    (bodyRun : PTX.Block body (Assembly.setup ctx count s).core core) :
    Flow.Runs ctx (program count body) s (Flow.halt {Assembly.setup ctx count s with core:=core}) := by
  have first := setup_run (body:=body) (ctx:=ctx) (count:=count) pc running
  have setupPC : (Assembly.setup ctx count s).core.pc=(Assembly.prologue count).length := by simp [Assembly.setup,Assembly.prologue,pc]
  have second := Flow.block_run (ctx:=ctx) (Indexed.scalar_block bodyRun) (Assembly.setup_active (s:=s) live)
    (Assembly.prologue count) [.ret] setupPC
  have retFetch : (program count body)[core.pc]?=some .ret := by
    rw [PTX.block_pc bodyRun,setupPC]
    simp [program]
  have last : Flow.Runs ctx (program count body) {Assembly.setup ctx count s with core:=core}
      (Flow.halt {Assembly.setup ctx count s with core:=core}) :=
    .cons ⟨Assembly.setup_active (s:=s) live,.ret,retFetch,.simple (by intro op same; cases same)⟩ .nil
  exact Flow.append first (Flow.append second last)

end PtxTorchLean.Poisson.PTX.VectorEntry
