import PoissonPTX.AssemblyMask
import PoissonPTX.IndexedFrames

namespace PtxTorchLean.Poisson.PTX.Assembly

def outputCode (output : Word) : List Flow.Instr :=
  ((storeCode 8 12 output).map Indexed.Instr.data).map Flow.Instr.data++[.ret]

def outputFinish (s : Flow.State) (output : Word) : Flow.State :=
  Flow.halt {s with core:=put (addressed s.core 12 output) .global (address s.core 12 output).toNat (s.core.regs 8)}

theorem output_trace (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 output).toNat) :
    Flow.Sequence ctx (outputCode output) s (outputFinish s output) := by
  apply Flow.sequence_append (Flow.sequence_data
    (Indexed.scalar_block (PTX.run_sound (store_run s.core 8 12 output (by decide) (by decide) valid))) running)
  exact .cons running (.simple (by intro op eq; cases eq)) .nil

def tailCode (mask : Bool) (boundary output : Word) : List Flow.Instr :=
  (if mask then maskCode boundary else [])++outputCode output

def tailStart (ctx : Kernel.Context) (mask : Bool) (s : Flow.State) (boundary : Word) : Flow.State :=
  if mask then masked ctx s boundary else s

def tailFinish (ctx : Kernel.Context) (mask : Bool) (s : Flow.State) (boundary output : Word) : Flow.State :=
  outputFinish (tailStart ctx mask s boundary) output

theorem mask_address : address (masked ctx s boundary).core 12 output=address s.core 12 output := by
  simp only [address,wide,(masked_frame (ctx:=ctx) (s:=s) (boundary:=boundary)).2.2.2.2.1,
    (masked_frame (ctx:=ctx) (s:=s) (boundary:=boundary)).2.2.2.2.2.1]

theorem tail_trace (running : s.halted=false)
    (maskValid : mask=true → Valid32 s.core.globalStart s.core.globalBytes (maskAddress s.core boundary).toNat)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 output).toNat) :
    Flow.Sequence ctx (tailCode mask boundary output) s (tailFinish ctx mask s boundary output) := by
  cases mask with
  | false => exact output_trace running valid
  | true =>
    apply Flow.sequence_append (mask_trace running (maskValid rfl))
    have frame := masked_frame (ctx:=ctx) (s:=s) (boundary:=boundary)
    exact output_trace (frame.2.2.2.2.2.2.1.trans running)
      (by simpa only [frame.2.2.1,frame.2.2.2.1,mask_address] using valid)

def finalWord (mask : Bool) (s : State) (boundary : Word) : Word :=
  if mask then maskedWord s boundary else s.regs 8

theorem tail_memory : (tailFinish ctx mask s boundary output).core.global=
    write64 s.core.global (address s.core 12 output).toNat (finalWord mask s.core boundary) := by
  cases mask with
  | false => rfl
  | true =>
    change write64 (masked ctx s boundary).core.global (address (masked ctx s boundary).core 12 output).toNat
      ((masked ctx s boundary).core.regs 8)=_
    rw [masked_frame.1,mask_address,masked_value]
    rfl

theorem tail_returned : (tailFinish ctx mask s boundary output).halted=true := rfl

theorem tail_plain : ∀ i∈tailCode mask boundary output, Flow.noFP i=true := by
  cases mask <;> simp [tailCode,maskCode,maskLoad,outputCode,storeCode,addressCode,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem tail_linear : ∀ i∈tailCode mask boundary output, Flow.linear i=true := by
  cases mask <;> simp [tailCode,maskCode,maskLoad,outputCode,storeCode,addressCode,Flow.linear]

end PtxTorchLean.Poisson.PTX.Assembly
