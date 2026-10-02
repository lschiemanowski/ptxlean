import PoissonPTX.AssemblyEntryResult
import PoissonPTX.AssemblyWindowExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- The complete active entry has a returning execution for every safe ordered
contribution range. It includes the actual setup, loop, optional mask and store. -/
theorem entry_exists (s : Flow.State)
    (pc : s.core.pc=0) (running : s.halted=false) (live : Kernel.Residual.live ctx count)
    (prepareValid : PrepareValid (setup ctx count s).core offsets)
    (layout : Layout (ready ctx count offsets s).core entries element)
    (ordered : cursor (ready ctx count offsets s).core≤limit (ready ctx count offsets s).core)
    (maskValid : mask=true → Valid32 (ready ctx count offsets s).core.globalStart
      (ready ctx count offsets s).core.globalBytes (maskAddress (ready ctx count offsets s).core boundary).toNat)
    (outputValid : Valid64 (ready ctx count offsets s).core.globalStart (ready ctx count offsets s).core.globalBytes
      (address (ready ctx count offsets s).core 12 output).toNat) :
    ∃ t, Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s t ∧ t.halted=true := by
  let start := ready ctx count offsets s
  obtain ⟨core,traverse⟩ := window_exists (origin:=(entryPrefix count offsets).length)
    start.core (stable_refl _) ordered (valid_of_layout layout)
  obtain ⟨middle,loopRun,same,alive⟩ := Flow.Window.traversal_runs
    (post:=tailCode mask boundary output) (ctx:=ctx) traverse start rfl
    (by simp [start,ready_pc,pc,entryPrefix,prologue,prepareCode]) (ready_running (s:=s) live)
  have trace : Flow.Window.Traversal (entryPrefix count offsets).length 19 20 (body entries element) start.core middle.core := by
    rw [same]; exact traverse
  have frame := (window_correct trace (stable_refl _) ordered (valid_of_layout layout)).2
  have node := window_node trace
  have outputAddress : address middle.core 12 output=address start.core 12 output := by
    simp only [address,wide,frame.2.2.2.2.2.2.1,node]
  have boundaryAddress : maskAddress middle.core boundary=maskAddress start.core boundary := by
    simp only [maskAddress,frame.2.2.2.2.2.2.1,node]
  have tail := tail_trace (ctx:=ctx) (s:=middle) (mask:=mask) (boundary:=boundary) (output:=output) alive
    (fun enabled => by simpa only [frame.2.2.1,frame.2.2.2.1,boundaryAddress] using maskValid enabled)
    (by simpa only [frame.2.2.1,frame.2.2.2.1,outputAddress] using outputValid)
  have tailRun : Flow.Runs ctx (entryCode count offsets entries element mask boundary output)
      middle (tailFinish ctx mask middle boundary output) := by
    simpa [entryCode,Flow.Window.program,beforeOutput,List.append_assoc] using
      Flow.sequence_run tail tail_linear (beforeOutput count offsets entries element) []
        (by have := Flow.Window.exit_pc trace; simpa [beforeOutput,Flow.Window.header,Nat.add_assoc] using this)
  have first : Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s start := by
    have run := Flow.sequence_run (prefix_trace running live prepareValid) prefix_linear []
        (Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element)++
          (body entries element).map Flow.Instr.data++[.jump (entryPrefix count offsets).length]++tailCode mask boundary output) pc
    simpa [entryCode,Flow.Window.program,List.append_assoc,start] using run
  exact ⟨_,Flow.append first (Flow.append loopRun tailRun),tail_returned⟩

end PtxTorchLean.Poisson.PTX.Assembly
