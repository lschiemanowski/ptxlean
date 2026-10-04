import PoissonPTX.ScalarArena

namespace PtxTorchLean.Poisson.PTX.Scalar
variable {a : Arena} {s : Flow.State} {offset : Word} {value : Operand} {dst : Nat}

theorem loaded32_frame (dst0 : dst≠0) : (loaded32 s dst offset).core.global=s.core.global ∧
    (loaded32 s dst offset).core.globalStart=s.core.globalStart ∧ (loaded32 s dst offset).core.globalBytes=s.core.globalBytes ∧
    (loaded32 s dst offset).core.regs 0=s.core.regs 0 ∧ (loaded32 s dst offset).halted=s.halted := by
  simp [loaded32,ScalarLoad.addressed,assign,advance,Ne.symm dst0]

theorem stored32_frame : (stored32 s offset value).core.globalStart=s.core.globalStart ∧
    (stored32 s offset value).core.globalBytes=s.core.globalBytes ∧
    (stored32 s offset value).core.regs 0=s.core.regs 0 ∧ (stored32 s offset value).halted=s.halted := by
  simp [stored32,put32,ScalarLoad.addressed,assign,advance]

theorem Arena.ready_load32 (ready : a.Ready s) (dst0 : dst≠0) : a.Ready (loaded32 s dst offset) := by
  simpa only [Arena.Ready,(loaded32_frame dst0).2.1,(loaded32_frame dst0).2.2.1,
    (loaded32_frame dst0).2.2.2.1] using ready

theorem Arena.ready_store32 (ready : a.Ready s) : a.Ready (stored32 s offset value) := by
  simpa only [Arena.Ready,stored32_frame.1,stored32_frame.2.1,stored32_frame.2.2.1] using ready

theorem Arena.ready_assign (ready : a.Ready s) (dst0 : dst≠0) :
    a.Ready {s with core:=assign s.core dst word} := by
  simpa [Arena.Ready,assign,advance,Ne.symm dst0] using ready

end PtxTorchLean.Poisson.PTX.Scalar
