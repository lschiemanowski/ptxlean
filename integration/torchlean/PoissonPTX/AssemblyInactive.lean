import PoissonPTX.AssemblyEntry

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- A padded thread returns at the entry guard. It does not read the offsets
or access the output, and does not require those addresses to be allocated. -/
theorem inactive_result
    (run : Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) :
    t=setup ctx count s ∧ t.core.global=s.core.global := by
  obtain ⟨k,run⟩ := Flow.counted run
  have trace := Flow.sequence_sound (prologue_execution (s:=s) (ctx:=ctx) (count:=count) running)
  let post := (prepareCode offsets).map Flow.Instr.data++
    Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element)++
    (body entries element).map Flow.Instr.data++[.jump (entryPrefix count offsets).length]++tailCode mask boundary output
  obtain ⟨remaining,_,rest⟩ := Flow.consume_sequence trace
    (by simp [prologue,Flow.noFP,Indexed.noFP]) (by simp [prologue,Flow.linear])
    (pre:=[]) (post:=post) (by simpa [entryCode,Flow.Window.program,entryPrefix,post,List.append_assoc] using run) pc done
  have same := Flow.Loop.halted_eq rest (setup_inactive (s:=s) inactive)
  exact ⟨same,by rw [same]; rfl⟩

/-- Padded launch lanes always have a finite return path, independently of the
memory layout. -/
theorem inactive_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (inactive : ¬Kernel.Residual.live ctx count) :
    Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s (setup ctx count s) ∧
      (setup ctx count s).halted=true := by
  have trace := Flow.sequence_sound (prologue_execution (s:=s) (ctx:=ctx) (count:=count) running)
  have run := Flow.sequence_run trace (by simp [prologue,Flow.linear]) []
    ((prepareCode offsets).map Flow.Instr.data++
      Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element)++
      (body entries element).map Flow.Instr.data++[.jump (entryPrefix count offsets).length]++tailCode mask boundary output) pc
  exact ⟨by simpa [entryCode,Flow.Window.program,entryPrefix,List.append_assoc] using run,setup_inactive (s:=s) inactive⟩

end PtxTorchLean.Poisson.PTX.Assembly
