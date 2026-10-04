import PoissonPTX.StorePair
import PoissonPTX.StoreZero
import PoissonPTX.DividePair
import PoissonPTX.PreconditionUpdate
import PoissonPTX.ControlFlowScalarSegments
import PoissonPTX.VectorFlowEntry

namespace PtxTorchLean.Poisson.PTX.Initialize

def prefixCode (boundary input rhs r diagonal : Word) : List Flow.Instr :=
  (Assembly.maskLoad boundary).map Flow.Instr.data++
  (loadCode 4 12 input).map (Flow.Instr.data ∘ Indexed.Instr.data)++
  [.compare 0 .ne (.reg 21) (.imm 0),.select 0 true 4 (.imm 0)]++
  (StorePair.code 4 rhs r).map (Flow.Instr.data ∘ Indexed.Instr.data)++
  (loadCode 5 12 diagonal).map (Flow.Instr.data ∘ Indexed.Instr.data)++
  [.select 0 true 5 (.imm PreconditionUpdate.one)]

def body (boundary input rhs r diagonal z p x : Word) : List Flow.Instr :=
  prefixCode boundary input rhs r diagonal++
  (DividePair.code z p).map (Flow.Instr.data ∘ Indexed.Instr.data)++
  (StoreZero.code x).map (Flow.Instr.data ∘ Indexed.Instr.data)

def entry (count : BitVec 32) (boundary input rhs r diagonal z p x : Word) : List Flow.Instr :=
  VectorFlowEntry.program count (body boundary input rhs r diagonal z p x)

def maskLoaded (s : Flow.State) (boundary : Word) : Flow.State := {s with core:=Assembly.maskLoaded s.core boundary}

def loadLoaded (s : Flow.State) (boundary input : Word) : Flow.State :=
  {maskLoaded s boundary with core:=assign (addressed (maskLoaded s boundary).core 12 input) 4 (read64 (maskLoaded s boundary).core.global (address (maskLoaded s boundary).core 12 input).toNat)}

def masked (ctx : Kernel.Context) (s : Flow.State) (boundary input : Word) : Flow.State :=
  Flow.simple ctx (.select 0 true 4 (.imm 0)) (Flow.simple ctx (.compare 0 .ne (.reg 21) (.imm 0))
    (loadLoaded s boundary input))

def copied (ctx : Kernel.Context) (s : Flow.State) (boundary input rhs r : Word) : Flow.State :=
  {masked ctx s boundary input with core:=StorePair.finish (masked ctx s boundary input).core 4 rhs r}

def diagonalLoaded (ctx : Kernel.Context) (s : Flow.State) (boundary input rhs r diagonal : Word) : Flow.State :=
  {copied ctx s boundary input rhs r with core:=assign (addressed (copied ctx s boundary input rhs r).core 12 diagonal) 5 (read64 (copied ctx s boundary input rhs r).core.global (address (copied ctx s boundary input rhs r).core 12 diagonal).toNat)}

def ready (ctx : Kernel.Context) (s : Flow.State) (boundary input rhs r diagonal : Word) : Flow.State :=
  Flow.simple ctx (.select 0 true 5 (.imm PreconditionUpdate.one)) (diagonalLoaded ctx s boundary input rhs r diagonal)

def divided (ctx : Kernel.Context) (s : Flow.State) (boundary input rhs r diagonal z p value : Word) : Flow.State :=
  {ready ctx s boundary input rhs r diagonal with core:=DividePair.finish (ready ctx s boundary input rhs r diagonal).core z p value}

def finish (ctx : Kernel.Context) (s : Flow.State) (boundary input rhs r diagonal z p x value : Word) : Flow.State :=
  {divided ctx s boundary input rhs r diagonal z p value with core:=StoreZero.finish (divided ctx s boundary input rhs r diagonal z p value).core x}

def Valid (s : State) (boundary input rhs r diagonal z p x : Word) : Prop :=
  (∀ field∈[input,rhs,r,diagonal,z,p,x],Valid64 s.globalStart s.globalBytes (address s 12 field).toNat) ∧
  Valid32 s.globalStart s.globalBytes (Assembly.maskAddress s boundary).toNat

theorem prefix_plain : ∀ i∈prefixCode boundary input rhs r diagonal, Flow.noFP i=true := by
  simp [prefixCode,StorePair.code,loadCode,storeCode,PTX.addressCode,Assembly.maskLoad,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem body_segment : ∀ i∈body boundary input rhs r diagonal z p x, Flow.segment i=true := by
  simp [body,prefixCode,StorePair.code,StoreZero.code,DividePair.code,loadCode,storeCode,PTX.addressCode,Assembly.maskLoad,Flow.segment]

theorem entry_length : (entry count boundary input rhs r diagonal z p x).length=43 := by
  simp [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,StorePair.code,StoreZero.code,DividePair.code,
    loadCode,storeCode,PTX.addressCode,Assembly.maskLoad]

end PtxTorchLean.Poisson.PTX.Initialize
