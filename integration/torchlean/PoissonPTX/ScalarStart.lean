import PoissonPTX.ScalarArena
import PoissonPTX.ScalarNorm

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena} {s : Flow.State} {norm product tolerance value : Word}

def middleCode (offset : Field → Word) : List Instr :=
  store64Code (offset .rhsNorm) (.reg 4)++store64Code (offset .residual) (.reg 4)++
    load64Code 5 (offset .rtol)++load64Code 6 (offset .atol)

def tailCode (offset : Field → Word) : List Instr :=
  store64Code (offset .tolerance) (.reg 5)++store32Code (offset .active) (.imm 1)++store32Code (offset .broken) (.imm 0)

def body (offset : Field → Word) : List Instr :=
  load64Code 4 (offset .rhsSquare)++[.sqrt 4 (.reg 4)]++middleCode offset++
  [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 4)))),.max 5 (.reg 5) (.reg 6)]++tailCode offset

def entry (offset : Field → Word) : List Instr := program (body offset)

def rooted (a : Arena) (s : Flow.State) (norm : Word) : Flow.State := Norm.rooted s (a.offset .rhsSquare) norm

def normStored (a : Arena) (s : Flow.State) : Flow.State := stored64 s (a.offset .rhsNorm) (.reg 4)
def residualStored (a : Arena) (s : Flow.State) : Flow.State := stored64 (normStored a s) (a.offset .residual) (.reg 4)
def relativeLoaded (a : Arena) (s : Flow.State) : Flow.State := loaded64 (residualStored a s) 5 (a.offset .rtol)
def middle (a : Arena) (s : Flow.State) : Flow.State := loaded64 (relativeLoaded a s) 6 (a.offset .atol)

def scaled (s : Flow.State) (value : Word) : Flow.State := {s with core:=assign s.core 5 value}
def maximumStored (s : Flow.State) (value : Word) : Flow.State := {s with core:=assign s.core 5 value}
def toleranceStored (a : Arena) (s : Flow.State) : Flow.State := stored64 s (a.offset .tolerance) (.reg 5)
def activeStored (a : Arena) (s : Flow.State) : Flow.State := stored32 (toleranceStored a s) (a.offset .active) (.imm 1)
def finished (a : Arena) (s : Flow.State) : Flow.State := stored32 (activeStored a s) (a.offset .broken) (.imm 0)

theorem middle_plain : ∀ i∈middleCode a.offset, noFP i=true := by
  simp [middleCode,store64Code,store64Ops,load64Code,ScalarLoad.code,ops,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem tail_plain : ∀ i∈tailCode a.offset, noFP i=true := by
  simp [tailCode,store64Code,store64Ops,store32Code,address4Code,ops,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem body_segment : ∀ i∈body a.offset, segment i=true := by
  simp [body,middleCode,tailCode,load64Code,ScalarLoad.code,store64Code,store64Ops,
    store32Code,address4Code,ops,segment,Flow.segment]

theorem entry_length : (entry a.offset).length=39 := by
  simp [entry,program,prologue,body,middleCode,tailCode,load64Code,ScalarLoad.code,
    store64Code,store64Ops,store32Code,address4Code,ops]

theorem rooted_ready (ready : a.Ready s) : a.Ready (rooted a s norm) := by
  simpa only [Arena.Ready,rooted,Norm.rooted_frame.2.1,Norm.rooted_frame.2.2.1,Norm.rooted_frame.2.2.2.1] using ready

theorem middle_ready (ready : a.Ready s) : a.Ready (middle a s) :=
  a.ready_load64 (a.ready_load64 (a.ready_store64 (a.ready_store64 ready)) (by decide)) (by decide)

theorem middle_trace (running : s.halted=false) (ready : a.Ready s) :
    Sequence ctx (middleCode a.offset) s (middle a s) := by
  have one := store64_trace (ctx:=ctx) (value:=.reg 4) running (a.state_valid64 ready .rhsNorm rfl)
  have two := store64_trace (ctx:=ctx) (s:=normStored a s) (value:=.reg 4)
    (stored64_frame.2.2.2.trans running) (a.state_valid64 (a.ready_store64 ready) .residual rfl)
  have three := load64_trace (ctx:=ctx) (s:=residualStored a s) (dst:=5)
    (by simpa only [residualStored,normStored,stored64_frame.2.2.2] using running)
    (a.state_valid64 (a.ready_store64 (a.ready_store64 ready)) .rtol rfl)
  have four := load64_trace (ctx:=ctx) (s:=relativeLoaded a s) (dst:=6)
    (by simpa only [relativeLoaded,residualStored,normStored,(loaded64_frame (by decide : 5≠0)).2.2.2.2,stored64_frame.2.2.2] using running)
    (a.state_valid64 (a.ready_load64 (a.ready_store64 (a.ready_store64 ready)) (by decide : 5≠0)) .atol rfl)
  exact sequence_append (sequence_append (sequence_append one two) three) four

end PtxTorchLean.Poisson.PTX.Scalar.Start
