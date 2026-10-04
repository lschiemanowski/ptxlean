import PoissonPTX.ScalarCoefficientInputs
import PoissonPTX.ScalarCoefficientGuards
import PoissonPTX.ScalarConditionalDivide

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha
variable {a : Arena} {s : Flow.State}

def flagCode (offset : Field → Word) : List Instr :=
  store32Code (offset .broken) (.reg 22)++store32Code (offset .useStep) (.reg 21)

def prefixCode (offset : Field → Word) : List Instr :=
  Coefficient.inputCode offset .denominator++Coefficient.alphaCode++flagCode offset

def body (offset : Field → Word) : List Instr :=
  prefixCode offset++ConditionalDivide.code 5 4++store64Code (offset .alpha) (.reg 6)

def entry (offset : Field → Word) : List Instr := program (body offset)

def guarded (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State :=
  Coefficient.alpha ctx (Coefficient.inputs a .denominator s)

def flagsStored (a : Arena) (s : Flow.State) : Flow.State :=
  stored32 (stored32 s (a.offset .broken) (.reg 22)) (a.offset .useStep) (.reg 21)

def beforeDivide (ctx : Kernel.Context) (a : Arena) (s : Flow.State) : Flow.State := flagsStored a (guarded ctx a s)

def finished (a : Arena) (s : Flow.State) (value : Word) : Flow.State :=
  stored64 (ConditionalDivide.finish s value) (a.offset .alpha) (.reg 6)

theorem guarded_ready (ready : a.Ready s) : a.Ready (guarded ctx a s) := by
  simpa only [Arena.Ready,guarded,Coefficient.alpha_frame.2.1,Coefficient.alpha_frame.2.2.1,
    Coefficient.alpha_frame.2.2.2.1] using Coefficient.inputs_ready (first:=Field.denominator) ready

theorem flags_ready (ready : a.Ready s) : a.Ready (flagsStored a s) := a.ready_store32 (a.ready_store32 ready)

theorem before_ready (ready : a.Ready s) : a.Ready (beforeDivide ctx a s) := flags_ready (guarded_ready ready)

theorem before_running : (beforeDivide ctx a s).halted=s.halted := by
  simp only [beforeDivide,flagsStored,stored32_frame.2.2.2,guarded,Coefficient.alpha_frame.2.2.2.2,Coefficient.inputs_frame.2]

theorem flags_trace (running : s.halted=false) (ready : a.Ready s) : Sequence ctx (flagCode a.offset) s (flagsStored a s) :=
  sequence_append (store32_trace running (a.state_valid32 ready .broken rfl))
    (store32_trace running (a.state_valid32 (a.ready_store32 ready) .useStep rfl))

theorem prefix_trace (running : s.halted=false) (ready : a.Ready s) : Sequence ctx (prefixCode a.offset) s (beforeDivide ctx a s) := by
  have one := Coefficient.inputs_trace (ctx:=ctx) running ready (first:=Field.denominator) rfl
  have two := Coefficient.alpha_trace (ctx:=ctx) (s:=Coefficient.inputs a .denominator s)
    (Coefficient.inputs_frame.2.trans running)
  have three := flags_trace (ctx:=ctx) (s:=guarded ctx a s)
    (Coefficient.alpha_frame.2.2.2.2.trans (Coefficient.inputs_frame.2.trans running)) (guarded_ready ready)
  exact sequence_append (sequence_append one two) three

theorem prefix_plain : ∀ i∈prefixCode a.offset, noFP i=true := by
  intro i member
  simp only [prefixCode,flagCode,List.mem_append] at member
  rcases member with (input | guard) | (broken | useStep)
  · exact Coefficient.inputs_plain i input
  · exact Control.plain (Coefficient.alpha_supported i guard)
  · exact store32_plain i broken
  · exact store32_plain i useStep

theorem prefix_state (actual : Sequence ctx (prefixCode a.offset) s t) (running : s.halted=false) (ready : a.Ready s) :
    t=beforeDivide ctx a s := sequence_unique actual (prefix_trace running ready) prefix_plain

theorem body_segment : ∀ i∈body a.offset, segment i=true := by
  simp [body,prefixCode,flagCode,Coefficient.inputCode,Coefficient.alphaCode,Coefficient.finiteCode,
    ConditionalDivide.code,load64Code,load32Code,store64Code,store64Ops,store32Code,address4Code,
    ScalarLoad.code,ops,segment,Flow.segment]

theorem entry_length : (entry a.offset).length=49 := by
  simp [entry,program,prologue,body,prefixCode,flagCode,Coefficient.inputCode,Coefficient.alphaCode,Coefficient.finiteCode,
    ConditionalDivide.code,load64Code,load32Code,store64Code,store64Ops,store32Code,address4Code,ScalarLoad.code,ops]

end PtxTorchLean.Poisson.PTX.Scalar.Alpha
