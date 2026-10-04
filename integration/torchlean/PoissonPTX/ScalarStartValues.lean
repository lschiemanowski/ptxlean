import PoissonPTX.ScalarStart

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena} {s : Flow.State} {norm product tolerance value : Word}

theorem middle_values (ready : a.Ready s) :
    (middle a s).core.regs 4=s.core.regs 4 ∧
    (middle a s).core.regs 5=read64 s.core.global (a.slot .rtol) ∧
    (middle a s).core.regs 6=read64 s.core.global (a.slot .atol) ∧
    (middle a s).core.global=write64 (write64 s.core.global (a.slot .rhsNorm) (s.core.regs 4))
      (a.slot .residual) (s.core.regs 4) := by
  simp [middle,relativeLoaded,residualStored,normStored,loaded64,stored64,
    ScalarLoad.loaded,ScalarLoad.addressed,put,assign,advance,Operand.eval,ready.1,a.address,
    read64_write64_disjoint _ _ _ _ (a.word_separate .residual .rtol (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .rhsNorm .rtol (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .residual .atol (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .rhsNorm .atol (by decide) rfl rfl)]

theorem tail_ready (ready : a.Ready s) : a.Ready (finished a s) := by
  simpa [Arena.Ready,finished,activeStored,toleranceStored,stored32,put32,stored64,
    ScalarLoad.addressed,put,assign,advance] using ready

theorem tail_halted : (finished a s).halted=s.halted := rfl

theorem tail_trace (running : s.halted=false) (ready : a.Ready s) : Sequence ctx (tailCode a.offset) s (finished a s) := by
  have one := store64_trace (ctx:=ctx) (value:=.reg 5) running (a.state_valid64 ready .tolerance rfl)
  have beforeFlag : a.Ready (toleranceStored a s) := a.ready_store64 ready
  have two := store32_trace (ctx:=ctx) (s:=toleranceStored a s) (value:=.imm 1)
    running (a.state_valid32 beforeFlag .active rfl)
  have beforeBroken : a.Ready (activeStored a s) := by
    simpa [Arena.Ready,activeStored,stored32,put32,ScalarLoad.addressed,assign,advance] using beforeFlag
  have three := store32_trace (ctx:=ctx) (s:=activeStored a s) (value:=.imm 0)
    running (a.state_valid32 beforeBroken .broken rfl)
  exact sequence_append (sequence_append one two) three

theorem tail_global (ready : a.Ready s) : (finished a s).core.global=
    write32 (write32 (write64 s.core.global (a.slot .tolerance) (s.core.regs 5))
      (a.slot .active) 1) (a.slot .broken) 0 := by
  simp [finished,activeStored,toleranceStored,stored32,put32,stored64,ScalarLoad.addressed,
    put,assign,advance,Operand.eval,Kernel.u32,ready.1,a.address]

end PtxTorchLean.Poisson.PTX.Scalar.Start
