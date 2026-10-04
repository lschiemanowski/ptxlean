import PoissonPTX.ControlFlowSegments
import PoissonPTX.AssemblyMask
import PoissonPTX.IndexedScalar

namespace PtxTorchLean.Poisson.PTX.PreconditionUpdate

def one : Word := 0x3ff0000000000000

theorem decode_one : decode one=1 := by decide +kernel

def setupCode (diagonal boundary : Word) : List Flow.Instr :=
  (loadCode 5 12 diagonal).map (Flow.Instr.data ∘ Indexed.Instr.data) ++
    (Assembly.maskLoad boundary).map Flow.Instr.data ++
    [.compare 0 .ne (.reg 21) (.imm 0),.select 0 true 5 (.imm one)]

def code (diagonal boundary output : Word) : List Flow.Instr :=
  setupCode diagonal boundary ++
    ([Op.fp .div 6 (.reg 6) (.reg 5)]++storeCode 6 12 output).map (Flow.Instr.data ∘ Indexed.Instr.data)

def diagonalLoaded (s : State) (diagonal : Word) : State :=
  assign (addressed s 12 diagonal) 5 (read64 s.global (address s 12 diagonal).toNat)

def prepared (s : State) (diagonal boundary : Word) : State :=
  Assembly.maskLoaded (diagonalLoaded s diagonal) boundary

def ready (ctx : Kernel.Context) (s : Flow.State) (diagonal boundary : Word) : Flow.State :=
  Flow.simple ctx (.select 0 true 5 (.imm one)) (Flow.simple ctx (.compare 0 .ne (.reg 21) (.imm 0))
    {s with core:=prepared s.core diagonal boundary})

def divisor (s : State) (diagonal boundary : Word) : Word :=
  if Assembly.maskFlag s boundary=0 then read64 s.global (address s 12 diagonal).toNat else one

def result (s : State) (diagonal boundary : Word) : Float := decode (s.regs 6)/decode (divisor s diagonal boundary)

def finish (ctx : Kernel.Context) (s : Flow.State) (diagonal boundary output value : Word) : Flow.State :=
  {ready ctx s diagonal boundary with core := put (addressed (assign (ready ctx s diagonal boundary).core 6 value) 12 output) .global (address s.core 12 output).toNat value}

theorem setup_trace (running : s.halted=false)
    (hd : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 diagonal).toNat)
    (hb : Valid32 s.core.globalStart s.core.globalBytes (Assembly.maskAddress s.core boundary).toNat) :
    Flow.Sequence ctx (setupCode diagonal boundary) s (ready ctx s diagonal boundary) := by
  have loaded := run_sound (load_run s.core 5 12 diagonal hd)
  have first := Flow.sequence_data (ctx:=ctx) (s:=s) (Indexed.scalar_block loaded) running
  have maskValid : Valid32 (diagonalLoaded s.core diagonal).globalStart (diagonalLoaded s.core diagonal).globalBytes
      (Assembly.maskAddress (diagonalLoaded s.core diagonal) boundary).toNat := by
    simpa [diagonalLoaded,Assembly.maskAddress,assign,advance,addressed] using hb
  have second := Flow.sequence_data (ctx:=ctx) (s:={s with core:=diagonalLoaded s.core diagonal})
    (Indexed.run_sound (Assembly.mask_load_execution maskValid)) running
  have last : Flow.Sequence ctx [.compare 0 .ne (.reg 21) (.imm 0),.select 0 true 5 (.imm one)]
      {s with core:=prepared s.core diagonal boundary} (ready ctx s diagonal boundary) :=
    .cons running (.simple (by intro op h; cases h)) (.cons running (.simple (by intro op h; cases h)) .nil)
  simpa [setupCode,List.map_map,Function.comp_def,List.append_assoc] using
    Flow.sequence_append first (Flow.sequence_append second last)

theorem ready_values :
    (ready ctx s diagonal boundary).core.regs 5=divisor s.core diagonal boundary ∧
    (ready ctx s diagonal boundary).core.regs 6=s.core.regs 6 := by
  simp [ready,prepared,divisor,diagonalLoaded,Assembly.maskLoaded,Assembly.maskFlag,Assembly.maskAddress,
    Flow.simple,Flow.next,Flow.Compare.apply,Kernel.u32,assign,advance,addressed,address,wide,Operand.eval]
  split <;> simp_all

theorem ready_frame :
    (ready ctx s diagonal boundary).core.global=s.core.global ∧
    (ready ctx s diagonal boundary).core.shared=s.core.shared ∧
    (ready ctx s diagonal boundary).core.globalStart=s.core.globalStart ∧
    (ready ctx s diagonal boundary).core.globalBytes=s.core.globalBytes ∧
    (ready ctx s diagonal boundary).core.regs 0=s.core.regs 0 ∧
    (ready ctx s diagonal boundary).core.regs 12=s.core.regs 12 ∧
    (ready ctx s diagonal boundary).halted=s.halted := by
  simp [ready,prepared,diagonalLoaded,Assembly.maskLoaded,Flow.simple,Flow.next,assign,advance,addressed]
  split <;> simp

theorem setup_plain : ∀ i∈setupCode diagonal boundary, Flow.noFP i=true := by
  simp [setupCode,loadCode,PTX.addressCode,Assembly.maskLoad,Flow.noFP,Indexed.noFP,noFP]

theorem code_segment : ∀ i∈code diagonal boundary output, Flow.segment i=true := by
  simp [code,setupCode,loadCode,storeCode,PTX.addressCode,Assembly.maskLoad,Flow.segment]

end PtxTorchLean.Poisson.PTX.PreconditionUpdate
