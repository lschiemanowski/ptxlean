import PoissonPTX.ScalarObservedBase
import PoissonPTX.ScalarMemory

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

def address8Code (offset : Word) : List Instr := ops [
  .wide8 1 (.imm 0),.add64 2 (.reg 0) (.reg 1),.add64 2 (.reg 2) (.imm offset)]

def addressed (s : Flow.State) (offset : Word) : Flow.State := {s with core:=ScalarLoad.addressed s.core offset}

theorem address8_trace (running : s.halted=false) : Scalar.Sequence ctx (address8Code offset) s (addressed s offset) := by
  apply ops_trace _ running
  apply run_sound
  simp [run,PTX.eval,Operand.eval,ScalarLoad.addressed,assign,advance]

theorem address4_trace (running : s.halted=false) : Scalar.Sequence ctx (address4Code offset) s (addressed s offset) := by
  apply Scalar.sequence_sound
  simp [address4Code,Scalar.sequence,Scalar.eval,Scalar.simple,Flow.eval,Indexed.eval,PTX.eval,
    Operand.eval,Kernel.u32,addressed,ScalarLoad.addressed,assign,advance,running]

theorem address8_state (actual : Sequence ctx (address8Code offset) s events t) (running : s.halted=false) :
    events=[] ∧ t=addressed s offset := by
  have empty := no_memory_sequence actual (by simp [address8Code,ops,noMemory])
  exact ⟨empty.1,Scalar.sequence_unique empty.2 (address8_trace running)
    (by simp [address8Code,ops,noFP,Flow.noFP,Indexed.noFP,PTX.noFP])⟩

theorem address4_state (actual : Sequence ctx (address4Code offset) s events t) (running : s.halted=false) :
    events=[] ∧ t=addressed s offset := by
  have empty := no_memory_sequence actual (by simp [address4Code,noMemory])
  exact ⟨empty.1,Scalar.sequence_unique empty.2 (address4_trace running)
    (by simp [address4Code,noFP,Flow.noFP,Indexed.noFP,PTX.noFP])⟩

theorem addressed_address {a : Arena} (ready : a.Ready s) :
    (addressed s (a.offset field)).core.pc=s.core.pc+3 ∧
    ((addressed s (a.offset field)).core.regs 2).toNat=a.slot field := by
  simp [addressed,ScalarLoad.addressed,assign,advance,ready.1,a.address,Nat.add_assoc]

end PtxTorchLean.Poisson.PTX.Scalar.Observed
