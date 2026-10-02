import PoissonPTX.AssemblySetup
import PoissonPTX.AssemblyWindow
import PoissonPTX.AssemblyOutput

namespace PtxTorchLean.Poisson.PTX.Assembly

def entryCode (count : BitVec 32) (offsets entries element : Word) (mask : Bool) (boundary output : Word) : List Flow.Instr :=
  Flow.Window.program (entryPrefix count offsets) 19 20 (body entries element) (tailCode mask boundary output)

def beforeOutput (count : BitVec 32) (offsets entries element : Word) : List Flow.Instr :=
  entryPrefix count offsets++Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element)++
    (body entries element).map Flow.Instr.data++[.jump (entryPrefix count offsets).length]

theorem window_node (run : Flow.Window.Traversal origin 19 20 (body entries element) s t) : t.regs 12=s.regs 12 := by
  induction run with
  | done => rfl
  | more _ step rest ih =>
    have keep := Indexed.block_keeps (r:=12) step (by simp [body,lookupCode,Indexed.keeps,SharedStore.keeps])
    exact ih.trans keep

/-- Recover the actual loop boundary and its continuation from the whole entry.
No ready state, cursor range, trace or intermediate sum is supplied. -/
theorem entry_loop
    (run : Flow.Counted ctx (entryCode count offsets entries element mask boundary output) k s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count) (valid : PrepareValid (setup ctx count s).core offsets) :
    ∃ remaining loopEnd,
      Flow.Window.Traversal (entryPrefix count offsets).length 19 20 (body entries element)
        (ready ctx count offsets s).core loopEnd.core ∧
      loopEnd.core.pc=(beforeOutput count offsets entries element).length ∧ loopEnd.halted=false ∧
      Flow.Counted ctx (entryCode count offsets entries element mask boundary output) remaining loopEnd t := by
  let post := Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element)++
    (body entries element).map Flow.Instr.data++[.jump (entryPrefix count offsets).length]++tailCode mask boundary output
  obtain ⟨afterSetup,number,continued⟩ := Flow.consume_sequence (prefix_trace running live valid)
    prefix_plain prefix_linear (pre:=[]) (post:=post)
    (by simpa [entryCode,Flow.Window.program,post,List.append_assoc] using run) pc done
  have continued' : Flow.Counted ctx (entryCode count offsets entries element mask boundary output)
      afterSetup (ready ctx count offsets s) t := by
    simpa [entryCode,Flow.Window.program,post,List.append_assoc] using continued
  obtain ⟨remaining,loopEnd,_,trace,exit,alive,rest⟩ := Flow.Window.cut continued'
    (by simp [ready_pc,pc,entryPrefix,prologue,prepareCode]) (ready_running (s:=s) live) done
  exact ⟨remaining,loopEnd,trace,by simpa [beforeOutput,Flow.Window.header,Nat.add_assoc] using exit,alive,rest⟩

/-- The original output path is consumed instruction by instruction at its
native location, and a real ret establishes the final state. -/
theorem entry_tail
    (run : Flow.Counted ctx (entryCode count offsets entries element mask boundary output) k s t)
    (pc : s.core.pc=(beforeOutput count offsets entries element).length)
    (running : s.halted=false) (done : t.halted=true)
    (maskValid : mask=true → Valid32 s.core.globalStart s.core.globalBytes (maskAddress s.core boundary).toNat)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 output).toNat) :
    t=tailFinish ctx mask s boundary output := by
  obtain ⟨remaining,number,rest⟩ := Flow.consume_sequence (tail_trace running maskValid valid)
    tail_plain tail_linear (pre:=beforeOutput count offsets entries element) (post:=[])
    (by simpa [entryCode,Flow.Window.program,beforeOutput,List.append_assoc] using run) pc done
  exact Flow.Loop.halted_eq rest tail_returned

end PtxTorchLean.Poisson.PTX.Assembly
