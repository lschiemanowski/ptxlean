import PoissonPTX.ScalarCoefficientGuards

namespace PtxTorchLean.Poisson.PTX.Scalar.Coefficient

def betaBrokenCode : List Instr := finiteCode 4 0++[
  .notPred 0 0,.base (.compare 1 .ne (.reg 21) (.imm 0)),.andPred 0 0 1,.move32 0 true 22 (.imm 1)]

def betaBroken (s : Flow.State) : BitVec 32 :=
  if !finiteGuard (s.core.regs 4) && active s then 1 else Kernel.u32 (s.core.regs 22)

def betaGuarded (ctx : Kernel.Context) (s : Flow.State) : Flow.State := Control.fold ctx betaBrokenCode s

def betaFinalCode : List Instr := [
  .compare 1 .gt (.reg 4) (.reg 5),.equal32 2 (.reg 22) (.imm 0),
  .andPred 0 0 1,.andPred 0 0 2,.select32 21 (.imm 1) (.imm 0) 0]

def betaActive (s : Flow.State) : Bool :=
  s.predicates 0 && Comparison.apply .gt (s.core.regs 4) (s.core.regs 5) && (Kernel.u32 (s.core.regs 22)==0)

def betaFinal (ctx : Kernel.Context) (s : Flow.State) : Flow.State := Control.fold ctx betaFinalCode s

theorem beta_broken_supported : ∀ i∈betaBrokenCode, Control.supported i=true := by
  simp [betaBrokenCode,finiteCode,Control.supported,Scalar.ordinary]

theorem beta_final_supported : ∀ i∈betaFinalCode, Control.supported i=true := by
  simp [betaFinalCode,Control.supported,Scalar.ordinary]

theorem beta_broken_trace (running : s.halted=false) : Sequence ctx betaBrokenCode s (betaGuarded ctx s) :=
  Control.trace beta_broken_supported running

theorem beta_final_trace (running : s.halted=false) : Sequence ctx betaFinalCode s (betaFinal ctx s) :=
  Control.trace beta_final_supported running

theorem beta_broken_values :
    Kernel.u32 ((betaGuarded ctx s).core.regs 22)=betaBroken s ∧
    (betaGuarded ctx s).core.regs 4=s.core.regs 4 ∧ (betaGuarded ctx s).core.regs 5=s.core.regs 5 ∧
    (betaGuarded ctx s).core.global=s.core.global ∧
    (betaGuarded ctx s).core.globalStart=s.core.globalStart ∧ (betaGuarded ctx s).core.globalBytes=s.core.globalBytes ∧
    (betaGuarded ctx s).core.regs 0=s.core.regs 0 ∧ (betaGuarded ctx s).halted=s.halted := by
  simp [betaGuarded,betaBrokenCode,finiteCode,Control.fold,Control.apply,Scalar.simple,Flow.simple,Flow.next,
    Flow.Compare.apply,Operand.eval,assign,advance,betaBroken,active,finiteGuard]
  split <;> simp_all [Kernel.u32]
  all_goals by_cases isActive : BitVec.setWidth 32 (s.core.regs 21)=0 <;> simp_all

theorem beta_final_values :
    Kernel.u32 ((betaFinal ctx s).core.regs 21)=(if betaActive s then 1 else 0) ∧
    (betaFinal ctx s).core.global=s.core.global ∧
    (betaFinal ctx s).core.globalStart=s.core.globalStart ∧ (betaFinal ctx s).core.globalBytes=s.core.globalBytes ∧
    (betaFinal ctx s).core.regs 0=s.core.regs 0 ∧ (betaFinal ctx s).halted=s.halted := by
  simp [betaFinal,betaFinalCode,Control.fold,Control.apply,Scalar.simple,Flow.next,
    Operand.eval,assign,advance,betaActive,Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]
  split_ifs <;> rfl

end PtxTorchLean.Poisson.PTX.Scalar.Coefficient
