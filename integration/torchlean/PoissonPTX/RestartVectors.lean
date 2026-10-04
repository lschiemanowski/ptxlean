import PoissonPTX.VectorCopy
import PoissonPTX.DividePair
import PoissonPTX.PreconditionUpdate
import PoissonPTX.ControlFlowScalarSegments
import PoissonPTX.VectorFlowEntry

namespace PtxTorchLean.Poisson.PTX.RestartVectors

def prefixCode (source r diagonal boundary : Word) : List Flow.Instr :=
  (VectorCopy.code source r).map (Flow.Instr.data ∘ Indexed.Instr.data)++PreconditionUpdate.setupCode diagonal boundary

def body (source r diagonal boundary z p : Word) : List Flow.Instr :=
  prefixCode source r diagonal boundary++(DividePair.code z p).map (Flow.Instr.data ∘ Indexed.Instr.data)

def entry (count : BitVec 32) (source r diagonal boundary z p : Word) : List Flow.Instr :=
  VectorFlowEntry.program count (body source r diagonal boundary z p)

def copied (s : Flow.State) (source r : Word) : Flow.State := {s with core:=VectorCopy.finish s.core source r}

def ready (ctx : Kernel.Context) (s : Flow.State) (source r diagonal boundary : Word) : Flow.State :=
  PreconditionUpdate.ready ctx (copied s source r) diagonal boundary

def finish (ctx : Kernel.Context) (s : Flow.State) (source r diagonal boundary z p value : Word) : Flow.State :=
  {ready ctx s source r diagonal boundary with core:=DividePair.finish (ready ctx s source r diagonal boundary).core z p value}

def Valid (s : State) (source r diagonal boundary z p : Word) : Prop :=
  (∀ field∈[source,r,diagonal,z,p], Valid64 s.globalStart s.globalBytes (address s 12 field).toNat) ∧
  Valid32 s.globalStart s.globalBytes (Assembly.maskAddress s boundary).toNat

theorem copied_mask : Assembly.maskAddress (copied s source r).core boundary=Assembly.maskAddress s.core boundary := by
  simp [copied,Assembly.maskAddress,VectorCopy.finish_frame.2.2.2.1,VectorCopy.finish_frame.2.2.2.2.1]

theorem prefix_trace (running : s.halted=false) (valid : Valid s.core source r diagonal boundary z p) :
    Flow.Sequence ctx (prefixCode source r diagonal boundary) s (ready ctx s source r diagonal boundary) := by
  have first := Flow.scalar_sequence (ctx:=ctx) (s:=s) (run_sound (VectorCopy.executes s.core source r
    (valid.1 source (by simp)) (valid.1 r (by simp)))) running
  have diagonalValid : Valid64 (copied s source r).core.globalStart (copied s source r).core.globalBytes
      (address (copied s source r).core 12 diagonal).toNat := by
    simpa only [copied,VectorCopy.finish_frame.1,VectorCopy.finish_frame.2.1,VectorCopy.finish_address] using valid.1 diagonal (by simp)
  have maskValid : Valid32 (copied s source r).core.globalStart (copied s source r).core.globalBytes
      (Assembly.maskAddress (copied s source r).core boundary).toNat := by
    rw [copied_mask]
    exact valid.2
  exact Flow.sequence_append first (PreconditionUpdate.setup_trace running diagonalValid maskValid)

theorem prefix_plain : ∀ i∈prefixCode source r diagonal boundary, Flow.noFP i=true := by
  simp [prefixCode,VectorCopy.code,loadCode,storeCode,PTX.addressCode,
    PreconditionUpdate.setupCode,Assembly.maskLoad,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem body_segment : ∀ i∈body source r diagonal boundary z p, Flow.segment i=true := by
  simp [body,prefixCode,VectorCopy.code,DividePair.code,loadCode,storeCode,PTX.addressCode,
    PreconditionUpdate.setupCode,Assembly.maskLoad,Flow.segment]

theorem ready_frame :
    (ready ctx s source r diagonal boundary).core.globalStart=s.core.globalStart ∧
    (ready ctx s source r diagonal boundary).core.globalBytes=s.core.globalBytes ∧
    (ready ctx s source r diagonal boundary).core.regs 0=s.core.regs 0 ∧
    (ready ctx s source r diagonal boundary).core.regs 12=s.core.regs 12 ∧
    (ready ctx s source r diagonal boundary).halted=s.halted := by
  simp only [ready,PreconditionUpdate.ready_frame.2.2.1,PreconditionUpdate.ready_frame.2.2.2.1,
    PreconditionUpdate.ready_frame.2.2.2.2.1,PreconditionUpdate.ready_frame.2.2.2.2.2.1,
    PreconditionUpdate.ready_frame.2.2.2.2.2.2,copied,VectorCopy.finish_frame.1,
    VectorCopy.finish_frame.2.1,VectorCopy.finish_frame.2.2.2.1,VectorCopy.finish_frame.2.2.2.2.1]
  simp

theorem entry_length : (entry count source r diagonal boundary z p).length=34 := by
  simp [entry,VectorFlowEntry.program,body,prefixCode,Assembly.prologue,VectorCopy.code,DividePair.code,
    loadCode,storeCode,PTX.addressCode,PreconditionUpdate.setupCode,Assembly.maskLoad]

end PtxTorchLean.Poisson.PTX.RestartVectors
