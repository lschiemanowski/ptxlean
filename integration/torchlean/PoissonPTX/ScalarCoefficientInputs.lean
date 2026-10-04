import PoissonPTX.ScalarFlagFrames

namespace PtxTorchLean.Poisson.PTX.Scalar.Coefficient
variable {a : Arena} {s : Flow.State} {first : Field}

def inputCode (offset : Field → Word) (first : Field) : List Instr :=
  load64Code 4 (offset first)++load64Code 5 (offset .rho)++
    load32Code 21 (offset .active)++load32Code 22 (offset .broken)

def firstLoaded (a : Arena) (first : Field) (s : Flow.State) : Flow.State := loaded64 s 4 (a.offset first)
def rhoLoaded (a : Arena) (first : Field) (s : Flow.State) : Flow.State := loaded64 (firstLoaded a first s) 5 (a.offset .rho)
def activeLoaded (a : Arena) (first : Field) (s : Flow.State) : Flow.State := loaded32 (rhoLoaded a first s) 21 (a.offset .active)
def inputs (a : Arena) (first : Field) (s : Flow.State) : Flow.State := loaded32 (activeLoaded a first s) 22 (a.offset .broken)

theorem inputs_ready (ready : a.Ready s) : a.Ready (inputs a first s) :=
  a.ready_load32 (a.ready_load32 (a.ready_load64 (a.ready_load64 ready (by decide)) (by decide)) (by decide)) (by decide)

theorem inputs_frame : (inputs a first s).core.global=s.core.global ∧ (inputs a first s).halted=s.halted := by
  simp [inputs,activeLoaded,rhoLoaded,firstLoaded,loaded32,loaded64,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance]

theorem inputs_values (ready : a.Ready s) :
    (inputs a first s).core.regs 4=read64 s.core.global (a.slot first) ∧
    (inputs a first s).core.regs 5=read64 s.core.global (a.slot .rho) ∧
    Kernel.u32 ((inputs a first s).core.regs 21)=read32 s.core.global (a.slot .active) ∧
    Kernel.u32 ((inputs a first s).core.regs 22)=read32 s.core.global (a.slot .broken) := by
  simp [inputs,activeLoaded,rhoLoaded,firstLoaded,loaded32,loaded64,ScalarLoad.loaded,
    ScalarLoad.addressed,assign,advance,ready.1,a.address,Kernel.u32,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64)]

theorem inputs_trace (running : s.halted=false) (ready : a.Ready s) (wide : first.width=8) :
    Sequence ctx (inputCode a.offset first) s (inputs a first s) := by
  have one := load64_trace (ctx:=ctx) (dst:=4) running (a.state_valid64 ready first wide)
  have two := load64_trace (ctx:=ctx) (s:=firstLoaded a first s) (dst:=5) running
    (a.state_valid64 (a.ready_load64 ready (by decide)) .rho rfl)
  have three := load32_trace (ctx:=ctx) (s:=rhoLoaded a first s) (dst:=21) running
    (a.state_valid32 (a.ready_load64 (a.ready_load64 ready (by decide)) (by decide)) .active rfl)
  have four := load32_trace (ctx:=ctx) (s:=activeLoaded a first s) (dst:=22) running
    (a.state_valid32 (a.ready_load32 (a.ready_load64 (a.ready_load64 ready (by decide)) (by decide)) (by decide)) .broken rfl)
  exact sequence_append (sequence_append (sequence_append one two) three) four

theorem inputs_plain : ∀ i∈inputCode a.offset first, noFP i=true := by
  simp [inputCode,load64Code,ops,ScalarLoad.code,load32Code,address4Code,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem inputs_state (actual : Sequence ctx (inputCode a.offset first) s t)
    (running : s.halted=false) (ready : a.Ready s) (wide : first.width=8) : t=inputs a first s :=
  sequence_unique actual (inputs_trace running ready wide) inputs_plain

end PtxTorchLean.Poisson.PTX.Scalar.Coefficient
