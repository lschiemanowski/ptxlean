import PoissonPTX.ScalarCoefficientInputs
import PoissonPTX.ScalarBetaGuards
import PoissonPTX.ScalarConditionalDivide

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena} {s : Flow.State}

def selectCode : List Instr := [.base (.compare 0 .ne (.reg 21) (.imm 0))]
def selected (ctx : Kernel.Context) (s : Flow.State) : Flow.State := Control.fold ctx selectCode s

def prefixCode (offset : Field → Word) : List Instr :=
  Coefficient.inputCode offset .rhoNext++Coefficient.betaBrokenCode++store32Code (offset .broken) (.reg 22)++
    load32Code 21 (offset .useStep)++selectCode

def middleCode (offset : Field → Word) : List Instr :=
  store64Code (offset .beta) (.reg 6)++store64Code (offset .rho) (.reg 4)++
    load64Code 4 (offset .rr)++load64Code 5 (offset .tolerance)

def tailCode (offset : Field → Word) : List Instr := Coefficient.betaFinalCode++store32Code (offset .active) (.reg 21)

def body (offset : Field → Word) : List Instr := prefixCode offset++ConditionalDivide.code 4 5++middleCode offset++
  [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 5))))]++tailCode offset

def entry (offset : Field → Word) : List Instr := program (body offset)

def guarded (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State :=
  Coefficient.betaGuarded ctx (Coefficient.inputs a .rhoNext s)
def brokenStored (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State :=
  stored32 (guarded ctx a s) (a.offset .broken) (.reg 22)
def beforeDivide (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State :=
  selected ctx (loaded32 (brokenStored ctx a s) 21 (a.offset .useStep))

def betaStored (a : Arena) (s : Flow.State) : Flow.State := stored64 s (a.offset .beta) (.reg 6)
def rhoStored (a : Arena) (s : Flow.State) : Flow.State := stored64 (betaStored a s) (a.offset .rho) (.reg 4)
def rrLoaded (a : Arena) (s : Flow.State) : Flow.State := loaded64 (rhoStored a s) 4 (a.offset .rr)
def middle (a : Arena) (s : Flow.State) : Flow.State := loaded64 (rrLoaded a s) 5 (a.offset .tolerance)
def squared (s : Flow.State) (value : Word) : Flow.State := {s with core:=assign s.core 5 value}
def finished (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State :=
  stored32 (Coefficient.betaFinal ctx s) (a.offset .active) (.reg 21)

theorem selected_supported : ∀ i∈selectCode, Control.supported i=true := by simp [selectCode,Control.supported]

theorem guarded_ready (ready : a.Ready s) : a.Ready (guarded ctx a s) := by
  simpa only [Arena.Ready,guarded,Coefficient.beta_broken_values.2.2.2.2.1,Coefficient.beta_broken_values.2.2.2.2.2.1,
    Coefficient.beta_broken_values.2.2.2.2.2.2.1] using Coefficient.inputs_ready (first:=Field.rhoNext) ready

theorem selected_frame : (selected ctx s).core.global=s.core.global ∧
    (selected ctx s).core.globalStart=s.core.globalStart ∧ (selected ctx s).core.globalBytes=s.core.globalBytes ∧
    (selected ctx s).core.regs=s.core.regs ∧ (selected ctx s).halted=s.halted ∧
    (selected ctx s).predicates 0=(Kernel.u32 (s.core.regs 21)!=0) := by
  simp [selected,selectCode,Control.fold,Control.apply,Flow.simple,Flow.next,Flow.Compare.apply,Operand.eval,advance,Kernel.u32]

theorem before_ready (ready : a.Ready s) : a.Ready (beforeDivide ctx a s) := by
  have h : a.Ready (brokenStored ctx a s) := a.ready_store32 (guarded_ready ready)
  have h' : a.Ready (loaded32 (brokenStored ctx a s) 21 (a.offset .useStep)) := a.ready_load32 h (by decide)
  simpa only [beforeDivide,Arena.Ready,selected_frame.2.1,selected_frame.2.2.1,selected_frame.2.2.2.1] using h'

theorem before_running : (beforeDivide ctx a s).halted=s.halted := by
  simp only [beforeDivide,selected_frame.2.2.2.2.1,(loaded32_frame (by decide : 21≠0)).2.2.2.2,
    brokenStored,stored32_frame.2.2.2,guarded,Coefficient.beta_broken_values.2.2.2.2.2.2.2,Coefficient.inputs_frame.2]

theorem prefix_trace (running : s.halted=false) (ready : a.Ready s) : Sequence ctx (prefixCode a.offset) s (beforeDivide ctx a s) := by
  have one := Coefficient.inputs_trace (ctx:=ctx) running ready (first:=Field.rhoNext) rfl
  have two := Coefficient.beta_broken_trace (ctx:=ctx) (s:=Coefficient.inputs a .rhoNext s) (Coefficient.inputs_frame.2.trans running)
  have alive : (guarded ctx a s).halted=false := Coefficient.beta_broken_values.2.2.2.2.2.2.2.trans (Coefficient.inputs_frame.2.trans running)
  have three := store32_trace (ctx:=ctx) (s:=guarded ctx a s) (value:=.reg 22) alive (a.state_valid32 (guarded_ready ready) .broken rfl)
  have four := load32_trace (ctx:=ctx) (s:=brokenStored ctx a s) (dst:=21) alive
    (a.state_valid32 (a.ready_store32 (guarded_ready ready)) .useStep rfl)
  have five := Control.trace (ctx:=ctx) (s:=loaded32 (brokenStored ctx a s) 21 (a.offset .useStep)) selected_supported alive
  exact sequence_append (sequence_append (sequence_append (sequence_append one two) three) four) five

theorem prefix_plain : ∀ i∈prefixCode a.offset, noFP i=true := by
  intro i member
  simp only [prefixCode,List.mem_append] at member
  rcases member with (((input | guard) | broken) | useStep) | selected
  · exact Coefficient.inputs_plain i input
  · exact Control.plain (Coefficient.beta_broken_supported i guard)
  · exact store32_plain i broken
  · exact load32_plain i useStep
  · exact Control.plain (selected_supported i selected)

end PtxTorchLean.Poisson.PTX.Scalar.Beta
