import PoissonPTX.ScalarBetaCorrect

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena} {s : Flow.State}

theorem body_exists (s : Flow.State) (running : s.halted=false) (ready : a.Ready s) :
    ∃ final, Sequence ctx (body a.offset) s final := by
  have one := prefix_trace (ctx:=ctx) running ready
  obtain ⟨value,allowed⟩ := ConditionalDivide.exists_allowed (beforeDivide ctx a s) 4 5
  have two := ConditionalDivide.trace (ctx:=ctx) (s:=beforeDivide ctx a s) (before_running.trans running) allowed (by decide) (by decide)
  have dividedReady := ConditionalDivide.ready (before_ready (ctx:=ctx) ready) (value:=value)
  have alive : (ConditionalDivide.finish (beforeDivide ctx a s) value).halted=false :=
    ConditionalDivide.frame.2.2.2.2.1.trans (before_running.trans running)
  have three := middle_trace (ctx:=ctx) alive dividedReady
  let square := encode (decode ((readySquare ctx a s value).core.regs 5)*decode ((readySquare ctx a s value).core.regs 5))
  have four : Sequence ctx [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 5))))]
      (readySquare ctx a s value) (squared (readySquare ctx a s value) square) := by
    exact .cons alive (.base (.data (.data (.fp (by simp [FP.Result,FP.apply,Operand.eval,square]))))) .nil
  have five := tail_trace (ctx:=ctx) (s:=squared (readySquare ctx a s value) square) alive (squared_ready (middle_ready dividedReady))
  exact ⟨_,sequence_append (sequence_append (sequence_append (sequence_append one two) three) four) five⟩

theorem entry_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final, Runs a.context (entry a.offset) (a.start memory regs) final ∧ final.halted=true := by
  obtain ⟨middle,trace⟩ := body_exists (ctx:=a.context) (setup a.context (a.start memory regs)) rfl (a.setup_ready memory regs)
  exact ⟨_,entry_executes trace (body_segment (a:=a)) rfl rfl,rfl⟩

end PtxTorchLean.Poisson.PTX.Scalar.Beta
