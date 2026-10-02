import PoissonPTX.AssemblyPrologue
import PoissonPTX.AssemblyLayout

namespace PtxTorchLean.Poisson.PTX.Assembly

def prepareCode (offsets : Word) : List Indexed.Instr := [
  .wide4 1 12,.data (.add64 2 (.reg 0) (.reg 1)),.data (.add64 2 (.reg 2) (.imm offsets)),.load32 19 2,
  .data (.add32 13 (.reg 12) (.imm 1)),
  .wide4 1 13,.data (.add64 2 (.reg 0) (.reg 1)),.data (.add64 2 (.reg 2) (.imm offsets)),.load32 20 2,
  .data (.mov 8 (.imm 0))]

def offsetAddress (s : State) (offsets : Word) (next : Bool) : Word :=
  address32 (s.regs 0) (Kernel.u32 (if next then add32 (s.regs 12) 1 else s.regs 12)) offsets

def offsetValue (s : State) (offsets : Word) (next : Bool) : BitVec 32 :=
  read32 s.global (offsetAddress s offsets next).toNat

def PrepareValid (s : State) (offsets : Word) : Prop :=
  Valid32 s.globalStart s.globalBytes (offsetAddress s offsets false).toNat ∧
  Valid32 s.globalStart s.globalBytes (offsetAddress s offsets true).toNat

def prepared (s : State) (offsets : Word) : State :=
  let r := Function.update s.regs 19 ((offsetValue s offsets false).setWidth 64)
  let r := Function.update r 13 (add32 (s.regs 12) 1)
  let r := Function.update r 1 (BitVec.ofNat 64 ((Kernel.u32 (add32 (s.regs 12) 1)).toNat*4))
  let r := Function.update r 2 (offsetAddress s offsets true)
  let r := Function.update r 20 ((offsetValue s offsets true).setWidth 64)
  let r := Function.update r 8 0
  {s with pc:=s.pc+10,regs:=r}

theorem prepare_execution (valid : PrepareValid s offsets) :
    Indexed.run (prepareCode offsets) s=some (prepared s offsets) := by
  obtain ⟨first,last⟩ := valid
  have wide4 (x : Nat) : (x%4294967296*4)%18446744073709551616=x%4294967296*4 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  simp [offsetAddress,address32,Kernel.u32,add32,wide4,Nat.add_assoc] at first last
  simp [prepareCode,Indexed.run,Indexed.eval,Indexed.wide,PTX.eval,prepared,offsetValue,offsetAddress,
    address32,Kernel.u32,add32,assign,advance,Operand.eval,State.start,State.bytes,State.memory,
    wide4,Nat.add_assoc,first,last]
  funext r
  by_cases one : r=1 <;> by_cases two : r=2 <;> simp [Function.update,one,two]

theorem prepare_correct (run : Indexed.Block (prepareCode offsets) s t)
    (valid : PrepareValid s offsets) : t=prepared s offsets := by
  have executed := Indexed.run_complete run (by simp [prepareCode,Indexed.noFP,PTX.noFP])
  rw [prepare_execution valid] at executed
  exact (Option.some.inj executed).symm

def entryPrefix (count : BitVec 32) (offsets : Word) : List Flow.Instr :=
  prologue count++(prepareCode offsets).map Flow.Instr.data

def ready (ctx : Kernel.Context) (count : BitVec 32) (offsets : Word) (s : Flow.State) : Flow.State :=
  let start := setup ctx count s
  {start with core:=prepared start.core offsets}

theorem prefix_trace (running : s.halted=false) (live : Kernel.Residual.live ctx count)
    (valid : PrepareValid (setup ctx count s).core offsets) :
    Flow.Sequence ctx (entryPrefix count offsets) s (ready ctx count offsets s) :=
  Flow.sequence_append (Flow.sequence_sound (prologue_execution running))
    (Flow.sequence_data (Indexed.run_sound (prepare_execution valid)) (setup_active live))

theorem prefix_plain : ∀ i∈entryPrefix count offsets, Flow.noFP i=true := by
  simp [entryPrefix,prologue,prepareCode,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem prefix_linear : ∀ i∈entryPrefix count offsets, Flow.linear i=true := by
  simp [entryPrefix,prologue,prepareCode,Flow.linear]

theorem ready_pc : (ready ctx count offsets s).core.pc=s.core.pc+16 := by
  simp [ready,prepared,setup,Nat.add_assoc]

theorem ready_running (live : Kernel.Residual.live ctx count) : (ready ctx count offsets s).halted=false :=
  setup_active (s:=s) live

end PtxTorchLean.Poisson.PTX.Assembly
