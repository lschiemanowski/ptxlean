import PoissonPTX.ScalarDeterministic
import PoissonPTX.ControlFlowScalarSegments
import PoissonPTX.ScalarLoad

namespace PtxTorchLean.Poisson.PTX.Scalar

def ops (code : List Op) : List Instr := code.map (Instr.base ∘ Flow.Instr.data ∘ Indexed.Instr.data)

theorem ops_trace (actual : Block code s.core t) (running : s.halted=false) :
    Sequence ctx (ops code) s {s with core:=t} := by
  simpa only [ops,List.map_map,Function.comp_def] using sequence_base (Flow.scalar_sequence actual running)

theorem ops_block (actual : Sequence ctx (ops code) s t) : Block code s.core t.core ∧ t={s with core:=t.core} := by
  have first := sequence_base_block (code:=code.map (Flow.Instr.data ∘ Indexed.Instr.data))
    (by simpa only [ops,List.map_map,Function.comp_def] using actual)
  exact Flow.scalar_segment first

def load64Code (dst : Nat) (offset : Word) : List Instr := ops (ScalarLoad.code dst offset)
def loaded64 (s : Flow.State) (dst : Nat) (offset : Word) : Flow.State := {s with core:=ScalarLoad.loaded s.core dst offset}

theorem load64_trace (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat) :
    Sequence ctx (load64Code dst offset) s (loaded64 s dst offset) :=
  ops_trace (run_sound (ScalarLoad.executes _ _ _ valid)) running

theorem load64_state (actual : Sequence ctx (load64Code dst offset) s t) : t=loaded64 s dst offset := by
  obtain ⟨block,state⟩ := ops_block actual
  rw [state,ScalarLoad.block_eq block]
  rfl

def store64Ops (offset : Word) (value : Operand) : List Op :=
  [.wide8 1 (.imm 0),.add64 2 (.reg 0) (.reg 1),.add64 2 (.reg 2) (.imm offset),.store64 .global (.reg 2) value]

def store64Code (offset : Word) (value : Operand) : List Instr := ops (store64Ops offset value)
def stored64 (s : Flow.State) (offset : Word) (value : Operand) : Flow.State :=
  {s with core:=put (ScalarLoad.addressed s.core offset) .global (s.core.regs 0+offset).toNat (value.eval (ScalarLoad.addressed s.core offset))}

theorem store64_trace (running : s.halted=false)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat) :
    Sequence ctx (store64Code offset value) s (stored64 s offset value) := by
  apply ops_trace _ running
  apply run_sound
  simp [store64Ops,run,PTX.eval,Operand.eval,ScalarLoad.addressed,assign,advance,State.start,State.bytes]
  simpa only [BitVec.toNat_add] using valid

theorem store64_plain : ∀ i∈store64Code offset value, noFP i=true := by
  simp [store64Code,ops,store64Ops,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem store64_state (actual : Sequence ctx (store64Code offset value) s t)
    (valid : Valid64 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat)
    (running : s.halted=false) : t=stored64 s offset value :=
  sequence_unique actual (store64_trace running valid) store64_plain

def address4Code (offset : Word) : List Instr :=
  [.wide4 1 (.imm 0),.base (.data (.data (.add64 2 (.reg 0) (.reg 1)))),
    .base (.data (.data (.add64 2 (.reg 2) (.imm offset))))]

def load32Code (dst : Nat) (offset : Word) : List Instr :=
  address4Code offset++[.base (.data (.load32 dst 2))]
def loaded32 (s : Flow.State) (dst : Nat) (offset : Word) : Flow.State :=
  {s with core:=assign (ScalarLoad.addressed s.core offset) dst ((read32 s.core.global (s.core.regs 0+offset).toNat).setWidth 64)}

def store32Code (offset : Word) (value : Operand) : List Instr :=
  address4Code offset++[.store32 (.reg 2) value]
def stored32 (s : Flow.State) (offset : Word) (value : Operand) : Flow.State :=
  put32 {s with core:=ScalarLoad.addressed s.core offset} (s.core.regs 0+offset).toNat (Kernel.u32 (value.eval (ScalarLoad.addressed s.core offset)))

theorem load32_trace (running : s.halted=false)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat) :
    Sequence ctx (load32Code dst offset) s (loaded32 s dst offset) := by
  apply sequence_sound
  simp [load32Code,address4Code,sequence,eval,simple,Flow.eval,Indexed.eval,PTX.eval,
    Operand.eval,Kernel.u32,assign,advance,loaded32,ScalarLoad.addressed,running]
  simpa only [BitVec.toNat_add] using valid

theorem store32_trace (running : s.halted=false)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat) :
    Sequence ctx (store32Code offset value) s (stored32 s offset value) := by
  apply sequence_sound
  simp [store32Code,address4Code,sequence,eval,simple,Flow.eval,Indexed.eval,PTX.eval,
    Operand.eval,Kernel.u32,assign,advance,stored32,ScalarLoad.addressed,running]
  simpa only [BitVec.toNat_add] using valid

theorem load32_plain : ∀ i∈load32Code dst offset, noFP i=true := by
  simp [load32Code,address4Code,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem store32_plain : ∀ i∈store32Code offset value, noFP i=true := by
  simp [store32Code,address4Code,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem load32_state (actual : Sequence ctx (load32Code dst offset) s t)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat)
    (running : s.halted=false) : t=loaded32 s dst offset :=
  sequence_unique actual (load32_trace running valid) load32_plain

theorem store32_state (actual : Sequence ctx (store32Code offset value) s t)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (s.core.regs 0+offset).toNat)
    (running : s.halted=false) : t=stored32 s offset value :=
  sequence_unique actual (store32_trace running valid) store32_plain

end PtxTorchLean.Poisson.PTX.Scalar
