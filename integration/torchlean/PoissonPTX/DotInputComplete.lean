import PoissonPTX.DotInputSetup

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- The lane's actual rounded partial sum, starting with positive zero.
The input view uses the supplied arena bytes and launch base. -/
def partialSum (ctx : Kernel.Context) (scratch : Word) (s : Flow.State)
    (count : Nat) (left right : Word) : Float :=
  (indices count ctx.lane.toNat).foldl
    (fun acc index => acc+contribution (setup ctx scratch s).core left right index) 0

theorem input_correct
    (run : Flow.Runs ctx (inputProgram count left right scratch) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.core.pc=20)
    (bounded : count<2^30) (arrays : Arrays (setup ctx scratch s).core count left right) :
    decode (t.core.regs 8)=partialSum ctx scratch s count left right ∧
      Stable (setup ctx scratch s).core t.core := by
  obtain ⟨steps,counted⟩ := Flow.counted run
  obtain ⟨remaining,afterSetup⟩ := consume_setup counted pc running done
  have setupPC : (setup ctx scratch s).core.pc=(setupCode scratch).length := by
    simp [setup,setupCode,assign,advance,pc]
  obtain ⟨_,ready,_,traverse,exit,_,rest⟩ := Flow.OperandWindow.cut afterSetup setupPC running
    (by simp [done,setupCode,body,loadCode,addressCode])
  have readyPC : ready.core.pc=20 := by simpa [setupCode,body,loadCode,addressCode] using exit
  have finalEq := no_continuation rest (by
    change (inputProgram count left right scratch)[ready.core.pc]?=none
    rw [readyPC,← input_length (count:=count) (left:=left) (right:=right) (scratch:=scratch)]; simp)
  rw [finalEq]
  have result := traversal_correct traverse bounded (stable_refl _)
    (fun i hi => arrays_valid arrays bounded hi)
  simpa only [partialSum,setup_cursor,setup_zero] using result

theorem input_exists (ctx : Kernel.Context) (scratch : Word) (s : Flow.State)
    (pc : s.core.pc=0) (running : s.halted=false) (bounded : count<2^30)
    (arrays : Arrays (setup ctx scratch s).core count left right) :
    ∃ t, Flow.Runs ctx (inputProgram count left right scratch) s t ∧
      t.core.pc=20 ∧ t.halted=false ∧
      decode (t.core.regs 8)=partialSum ctx scratch s count left right ∧
      Stable (setup ctx scratch s).core t.core := by
  have first : Flow.Runs ctx (inputProgram count left right scratch) s (setup ctx scratch s) := by
    have witness := Flow.sequence_run (setup_sequence (ctx:=ctx) (scratch:=scratch) running)
      (by simp [setupCode,Flow.linear]) []
      (Flow.OperandWindow.header (setupCode scratch).length 12 (.imm (BitVec.ofNat 64 count))
        ((body left right).map Indexed.Instr.data) ++
        ((body left right).map Indexed.Instr.data).map Flow.Instr.data ++
        [.jump (setupCode scratch).length]) pc
    simpa [inputProgram,Flow.OperandWindow.program,List.append_assoc] using witness
  obtain ⟨core,traverse⟩ := traversal_exists (origin:=(setupCode scratch).length)
    (setup ctx scratch s).core bounded (stable_refl _) (fun i hi => arrays_valid arrays bounded hi)
  have setupPC : (setup ctx scratch s).core.pc=(setupCode scratch).length := by
    simp [setup,setupCode,assign,advance,pc]
  obtain ⟨t,second,same,live⟩ := Flow.OperandWindow.traversal_runs (pre:=setupCode scratch) (post:=[])
    (ctx:=ctx) traverse (setup ctx scratch s) rfl setupPC running
  have actual := Flow.append first second
  have done : t.core.pc=20 := by
    rw [same,Flow.OperandWindow.exit_pc traverse]
    simp [setupCode,body,loadCode,addressCode]
  exact ⟨t,actual,done,live,input_correct actual pc running done bounded arrays⟩

end PtxTorchLean.Poisson.PTX.DotInput
