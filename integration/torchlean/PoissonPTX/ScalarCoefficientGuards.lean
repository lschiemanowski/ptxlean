import PoissonPTX.ScalarControl

namespace PtxTorchLean.Poisson.PTX.Scalar.Coefficient

def largestFinite : Word := 0x7fefffffffffffff

/-- The emitted finite-range guard: absolute value followed by an ordered
comparison with the greatest finite binary64 value. -/
def finiteGuard (word : Word) : Bool := Comparison.apply .le (absolute word) largestFinite

def finiteCode (src predicate : Nat) : List Instr :=
  [.abs 11 (.reg src),.compare predicate .le (.reg 11) (.imm largestFinite)]

def alphaCode : List Instr := finiteCode 4 0++finiteCode 5 1++[
  .compare 2 .gt (.reg 4) (.imm 0),.compare 3 .gt (.reg 5) (.imm 0),
  .andPred 0 0 1,.andPred 0 0 2,.andPred 0 0 3,
  .base (.compare 1 .ne (.reg 21) (.imm 0)),.notPred 2 0,.andPred 2 2 1,
  .move32 2 true 22 (.imm 1),.andPred 0 0 1,.select32 21 (.imm 1) (.imm 0) 0]

def alphaGood (s : Flow.State) : Bool :=
  finiteGuard (s.core.regs 4) && finiteGuard (s.core.regs 5) &&
    Comparison.apply .gt (s.core.regs 4) 0 && Comparison.apply .gt (s.core.regs 5) 0

def active (s : Flow.State) : Bool := Kernel.u32 (s.core.regs 21)!=0

def alphaUse (s : Flow.State) : Bool := alphaGood s && active s

def alphaBroken (s : Flow.State) : BitVec 32 :=
  if !alphaGood s && active s then 1 else Kernel.u32 (s.core.regs 22)

def alpha (ctx : Kernel.Context) (s : Flow.State) : Flow.State := Control.fold ctx alphaCode s

theorem alpha_supported : ∀ i∈alphaCode, Control.supported i=true := by
  simp [alphaCode,finiteCode,Control.supported,Scalar.ordinary]

theorem alpha_trace (running : s.halted=false) : Sequence ctx alphaCode s (alpha ctx s) :=
  Control.trace alpha_supported running

theorem alpha_state (actual : Sequence ctx alphaCode s t) (running : s.halted=false) : t=alpha ctx s :=
  Control.unique actual alpha_supported running

/-- The old broken flag is preserved unless this active step fails its guard;
that old flag does not itself disable alpha in the emitted program. -/
theorem alpha_values :
    (alpha ctx s).predicates 0=alphaUse s ∧
    Kernel.u32 ((alpha ctx s).core.regs 21)=(if alphaUse s then 1 else 0) ∧
    Kernel.u32 ((alpha ctx s).core.regs 22)=alphaBroken s ∧
    (alpha ctx s).core.regs 4=s.core.regs 4 ∧ (alpha ctx s).core.regs 5=s.core.regs 5 := by
  simp [alpha,alphaCode,finiteCode,Control.fold,Control.apply,Scalar.simple,Flow.simple,Flow.next,
    Flow.Compare.apply,Operand.eval,assign,advance,alphaUse,alphaGood,alphaBroken,active,finiteGuard]
  split <;> simp_all [Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]
  all_goals split_ifs <;> simp_all
  all_goals split_ifs <;> simp_all

  all_goals by_cases isActive : BitVec.setWidth 32 (s.core.regs 21)=0 <;> simp_all

theorem alpha_frame :
    (alpha ctx s).core.global=s.core.global ∧
    (alpha ctx s).core.globalStart=s.core.globalStart ∧
    (alpha ctx s).core.globalBytes=s.core.globalBytes ∧
    (alpha ctx s).core.regs 0=s.core.regs 0 ∧ (alpha ctx s).halted=s.halted := by
  simp [alpha,alphaCode,finiteCode,Control.fold,Control.apply,Scalar.simple,Flow.simple,Flow.next,
    Flow.Compare.apply,Operand.eval,assign,advance]
  split <;> simp_all

end PtxTorchLean.Poisson.PTX.Scalar.Coefficient
