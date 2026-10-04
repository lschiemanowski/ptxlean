import PoissonPTX.ScalarBetaSegments

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena} {s : Flow.State}

def broken (a : Arena) (memory : Memory) : BitVec 32 :=
  if !Coefficient.finiteGuard (read64 memory (a.slot .rhoNext)) && (read32 memory (a.slot .active)!=0)
    then 1 else read32 memory (a.slot .broken)

def useStep (a : Arena) (memory : Memory) : Bool := read32 memory (a.slot .useStep)!=0

def flagged (a : Arena) (memory : Memory) : Memory := write32 memory (a.slot .broken) (broken a memory)

def Allowed (a : Arena) (memory : Memory) (value : Word) : Prop :=
  (useStep a memory=true ∧ decode value=decode (read64 memory (a.slot .rhoNext))/decode (read64 memory (a.slot .rho))) ∨
  (useStep a memory=false ∧ value=0)

theorem select_values (ready : a.Ready s) :
    (selected ctx (loaded32 (stored32 s (a.offset .broken) (.reg 22)) 21 (a.offset .useStep))).predicates 0=
      (read32 s.core.global (a.slot .useStep)!=0) ∧
    (selected ctx (loaded32 (stored32 s (a.offset .broken) (.reg 22)) 21 (a.offset .useStep))).core.regs 4=s.core.regs 4 ∧
    (selected ctx (loaded32 (stored32 s (a.offset .broken) (.reg 22)) 21 (a.offset .useStep))).core.regs 5=s.core.regs 5 ∧
    (selected ctx (loaded32 (stored32 s (a.offset .broken) (.reg 22)) 21 (a.offset .useStep))).core.regs 22=s.core.regs 22 ∧
    (selected ctx (loaded32 (stored32 s (a.offset .broken) (.reg 22)) 21 (a.offset .useStep))).core.global=
      write32 s.core.global (a.slot .broken) (Kernel.u32 (s.core.regs 22)) := by
  simp only [selected_frame.2.2.2.2.2,selected_frame.2.2.2.1,selected_frame.1]
  simp [loaded32,stored32,ScalarLoad.addressed,put32,assign,advance,Operand.eval,ready.1,a.address,
    Kernel.u32,BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),
    read32_write32_disjoint _ _ _ _ (a.separate .broken .useStep (by decide))]

theorem before_values (ready : a.Ready s) :
    (beforeDivide ctx a s).predicates 0=useStep a s.core.global ∧
    (beforeDivide ctx a s).core.regs 4=read64 s.core.global (a.slot .rhoNext) ∧
    (beforeDivide ctx a s).core.regs 5=read64 s.core.global (a.slot .rho) ∧
    Kernel.u32 ((beforeDivide ctx a s).core.regs 22)=broken a s.core.global ∧
    (beforeDivide ctx a s).core.global=flagged a s.core.global := by
  have values := Coefficient.inputs_values (first:=Field.rhoNext) ready
  simp only [beforeDivide,brokenStored]
  rw [(select_values (guarded_ready ready)).1,(select_values (guarded_ready ready)).2.1,
    (select_values (guarded_ready ready)).2.2.1,(select_values (guarded_ready ready)).2.2.2.1,
    (select_values (guarded_ready ready)).2.2.2.2]
  simp only [guarded,Coefficient.beta_broken_values.1,Coefficient.beta_broken_values.2.1,Coefficient.beta_broken_values.2.2.1,
    Coefficient.beta_broken_values.2.2.2.1,Coefficient.inputs_frame.1]
  simp only [Coefficient.betaBroken,Coefficient.active,values.1,values.2.1,values.2.2.1,values.2.2.2,
    broken,useStep,flagged]
  exact ⟨trivial,trivial,trivial,trivial,trivial⟩

theorem allowed_iff (ready : a.Ready s) :
    ConditionalDivide.Allowed (beforeDivide ctx a s) 4 5 value ↔ Allowed a s.core.global value := by
  simp only [ConditionalDivide.Allowed,(before_values ready).1,(before_values ready).2.1,
    (before_values ready).2.2.1,FP.Result,FP.apply,Allowed]

def readySquare (ctx : Kernel.Context) (a : Arena) (s : Flow.State) (value : Word) : Flow.State :=
  middle a (ConditionalDivide.finish (beforeDivide ctx a s) value)

def dividedMemory (a : Arena) (memory : Memory) (value : Word) : Memory :=
  write64 (write64 (flagged a memory) (a.slot .beta) value) (a.slot .rho) (read64 memory (a.slot .rhoNext))

theorem ready_square_values (ready : a.Ready s) :
    (readySquare ctx a s value).core.regs 4=read64 s.core.global (a.slot .rr) ∧
    (readySquare ctx a s value).core.regs 5=read64 s.core.global (a.slot .tolerance) ∧
    Kernel.u32 ((readySquare ctx a s value).core.regs 22)=broken a s.core.global ∧
    (readySquare ctx a s value).predicates 0=useStep a s.core.global ∧
    (readySquare ctx a s value).core.global=dividedMemory a s.core.global value := by
  have ready' := ConditionalDivide.ready (before_ready (ctx:=ctx) ready) (value:=value)
  simp only [readySquare]
  rw [(middle_values ready').1,(middle_values ready').2.1,(middle_values ready').2.2.1,
    (middle_values ready').2.2.2.1,(middle_values ready').2.2.2.2]
  simp only [ConditionalDivide.frame.1,ConditionalDivide.frame.2.2.2.2.2]
  have reg4 : (ConditionalDivide.finish (beforeDivide ctx a s) value).core.regs 4=(beforeDivide ctx a s).core.regs 4 := by
    simp [ConditionalDivide.finish,ConditionalDivide.zeroed,assign,advance]
  have reg22 : (ConditionalDivide.finish (beforeDivide ctx a s) value).core.regs 22=(beforeDivide ctx a s).core.regs 22 := by
    simp [ConditionalDivide.finish,ConditionalDivide.zeroed,assign,advance]
  have pred : (ConditionalDivide.finish (beforeDivide ctx a s) value).predicates=(beforeDivide ctx a s).predicates := rfl
  rw [reg4,reg22,pred,(before_values ready).1,(before_values ready).2.1,
    (before_values ready).2.2.2.1,(before_values ready).2.2.2.2]
  simp only [flagged,dividedMemory,
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .broken .rr (by decide) rfl rfl),
    read64_write32_disjoint _ _ _ _ (a.flag_word_separate .broken .tolerance (by decide) rfl rfl),and_self]

end PtxTorchLean.Poisson.PTX.Scalar.Beta
