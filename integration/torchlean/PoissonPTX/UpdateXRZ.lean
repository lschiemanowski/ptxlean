import PoissonPTX.RegisterUpdateFrame
import PoissonPTX.PreconditionUpdateCorrect
import PoissonPTX.ControlFlowScalarSegments
import PoissonPTX.VectorFlowEntry

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- The emitted vector update loads alpha once, updates x, updates r, then
computes z from the newly computed r register and the boundary-adjusted diagonal. -/
def body (alpha p x ap r diagonal boundary z : Word) : List Flow.Instr :=
  (ScalarLoad.code 4 alpha).map (Flow.Instr.data ∘ Indexed.Instr.data) ++
    (RegisterUpdate.code .add p x x).map (Flow.Instr.data ∘ Indexed.Instr.data) ++
    (RegisterUpdate.code .sub ap r r).map (Flow.Instr.data ∘ Indexed.Instr.data) ++
    PreconditionUpdate.code diagonal boundary z

def entry (count : BitVec 32) (alpha p x ap r diagonal boundary z : Word) : List Flow.Instr :=
  VectorFlowEntry.program count (body alpha p x ap r diagonal boundary z)

def coefficient (s : Flow.State) (alpha : Word) : Flow.State := {s with core:=ScalarLoad.loaded s.core 4 alpha}

def solution (s : Flow.State) (alpha p x mulWord value : Word) : Flow.State :=
  {coefficient s alpha with core:=RegisterUpdate.finish (coefficient s alpha).core p x x mulWord value}

def residual (s : Flow.State) (alpha p x ap r xm xv rm rv : Word) : Flow.State :=
  {solution s alpha p x xm xv with core:=RegisterUpdate.finish (solution s alpha p x xm xv).core ap r r rm rv}

def finish (ctx : Kernel.Context) (s : Flow.State) (alpha p x ap r diagonal boundary z xm xv rm rv zv : Word) : Flow.State :=
  PreconditionUpdate.finish ctx (residual s alpha p x ap r xm xv rm rv) diagonal boundary z zv

theorem body_segment : ∀ i∈body alpha p x ap r diagonal boundary z, Flow.segment i=true := by
  simp [body,ScalarLoad.code,RegisterUpdate.code,loadCode,storeCode,PTX.addressCode,
    PreconditionUpdate.code,PreconditionUpdate.setupCode,Assembly.maskLoad,Flow.segment]

theorem entry_length : (entry count alpha p x ap r diagonal boundary z).length=54 := by
  simp [entry,VectorFlowEntry.program,body,Assembly.prologue,ScalarLoad.code,RegisterUpdate.code,
    loadCode,storeCode,PTX.addressCode,PreconditionUpdate.code,PreconditionUpdate.setupCode,Assembly.maskLoad]

end PtxTorchLean.Poisson.PTX.UpdateXRZ
