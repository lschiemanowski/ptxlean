import PoissonPTX.ScalarAlpha

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha
variable {a : Arena} {s : Flow.State}

def good (a : Arena) (memory : Memory) : Bool :=
  Coefficient.finiteGuard (read64 memory (a.slot .denominator)) && Coefficient.finiteGuard (read64 memory (a.slot .rho)) &&
    Comparison.apply .gt (read64 memory (a.slot .denominator)) 0 && Comparison.apply .gt (read64 memory (a.slot .rho)) 0

def useStep (a : Arena) (memory : Memory) : Bool := good a memory && (read32 memory (a.slot .active)!=0)
def broken (a : Arena) (memory : Memory) : BitVec 32 :=
  if !good a memory && (read32 memory (a.slot .active)!=0) then 1 else read32 memory (a.slot .broken)

def flags (a : Arena) (memory : Memory) : Memory :=
  write32 (write32 memory (a.slot .broken) (broken a memory)) (a.slot .useStep) (if useStep a memory then 1 else 0)

def Allowed (a : Arena) (memory : Memory) (value : Word) : Prop :=
  (useStep a memory=true ∧ decode value=decode (read64 memory (a.slot .rho))/decode (read64 memory (a.slot .denominator))) ∨
  (useStep a memory=false ∧ value=0)

theorem flags_values (ready : a.Ready s) :
    (flagsStored a s).predicates=s.predicates ∧
    (flagsStored a s).core.regs 4=s.core.regs 4 ∧ (flagsStored a s).core.regs 5=s.core.regs 5 ∧
    (flagsStored a s).core.global=write32 (write32 s.core.global (a.slot .broken) (Kernel.u32 (s.core.regs 22)))
      (a.slot .useStep) (Kernel.u32 (s.core.regs 21)) := by
  simp [flagsStored,stored32,put32,ScalarLoad.addressed,Operand.eval,assign,advance,ready.1,a.address]

theorem before_values (ready : a.Ready s) :
    (beforeDivide ctx a s).predicates 0=useStep a s.core.global ∧
    (beforeDivide ctx a s).core.regs 4=read64 s.core.global (a.slot .denominator) ∧
    (beforeDivide ctx a s).core.regs 5=read64 s.core.global (a.slot .rho) ∧
    (beforeDivide ctx a s).core.global=flags a s.core.global := by
  have values := Coefficient.inputs_values (first:=Field.denominator) ready
  simp only [beforeDivide]
  rw [(flags_values (guarded_ready ready)).1,(flags_values (guarded_ready ready)).2.1,
    (flags_values (guarded_ready ready)).2.2.1,(flags_values (guarded_ready ready)).2.2.2]
  simp only [guarded,
    Coefficient.alpha_values.1,Coefficient.alpha_values.2.1,Coefficient.alpha_values.2.2.1,
    Coefficient.alpha_values.2.2.2.1,Coefficient.alpha_values.2.2.2.2,Coefficient.alpha_frame.1,Coefficient.inputs_frame.1]
  simp only [Coefficient.alphaUse,Coefficient.alphaGood,Coefficient.alphaBroken,Coefficient.active,
    values.1,values.2.1,values.2.2.1,values.2.2.2,good,useStep,broken,flags]
  exact ⟨trivial,trivial,trivial,rfl⟩

theorem allowed_iff (ready : a.Ready s) :
    ConditionalDivide.Allowed (beforeDivide ctx a s) 5 4 value ↔ Allowed a s.core.global value := by
  simp only [ConditionalDivide.Allowed,(before_values ready).1,(before_values ready).2.1,
    (before_values ready).2.2.1,FP.Result,FP.apply,Allowed]

def publish (a : Arena) (memory : Memory) (value : Word) : Memory := write64 (flags a memory) (a.slot .alpha) value

theorem finished_global (ready : a.Ready s) :
    (finished a (beforeDivide ctx a s) value).core.global=publish a s.core.global value := by
  rw [finished,stored64_global]
  simp only [Operand.eval,addressed_reg (by decide : 6≠1) (by decide : 6≠2),ConditionalDivide.frame.2.2.2.2.2,
    ConditionalDivide.frame.1,ConditionalDivide.frame.2.2.2.1,(before_ready ready).1,a.address,(before_values ready).2.2.2,publish]

end PtxTorchLean.Poisson.PTX.Scalar.Alpha
