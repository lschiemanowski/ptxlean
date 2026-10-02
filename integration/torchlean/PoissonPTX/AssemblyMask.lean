import PoissonPTX.ControlFlowSequence
import PoissonPTX.AssemblyLayout

namespace PtxTorchLean.Poisson.PTX.Assembly

def maskLoad (boundary : Word) : List Indexed.Instr := [
  .wide4 1 12,.data (.add64 2 (.reg 0) (.reg 1)),.data (.add64 2 (.reg 2) (.imm boundary)),.load32 21 2]

def maskAddress (s : State) (boundary : Word) : Word := address32 (s.regs 0) (Kernel.u32 (s.regs 12)) boundary
def maskFlag (s : State) (boundary : Word) : BitVec 32 := read32 s.global (maskAddress s boundary).toNat

def maskLoaded (s : State) (boundary : Word) : State :=
  assign (assign (assign (assign s 1 (BitVec.ofNat 64 ((Kernel.u32 (s.regs 12)).toNat*4)))
    2 (s.regs 0+BitVec.ofNat 64 ((Kernel.u32 (s.regs 12)).toNat*4))) 2 (maskAddress s boundary))
    21 ((maskFlag s boundary).setWidth 64)

theorem mask_load_execution (valid : Valid32 s.globalStart s.globalBytes (maskAddress s boundary).toNat) :
    Indexed.run (maskLoad boundary) s=some (maskLoaded s boundary) := by
  have wide4 (x : Nat) : (x%4294967296*4)%18446744073709551616=x%4294967296*4 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  simp [maskAddress,address32,Kernel.u32,wide4,Nat.add_assoc] at valid
  simp [maskLoad,maskLoaded,maskAddress,maskFlag,Indexed.run,Indexed.eval,Indexed.wide,PTX.eval,
    address32,Kernel.u32,assign,advance,Operand.eval,wide4,Nat.add_assoc,valid]

def maskCode (boundary : Word) : List Flow.Instr := (maskLoad boundary).map Flow.Instr.data++[
  .compare 0 .ne (.reg 21) (.imm 0),.select 0 true 8 (.imm 0)]

def masked (ctx : Kernel.Context) (s : Flow.State) (boundary : Word) : Flow.State :=
  Flow.simple ctx (.select 0 true 8 (.imm 0)) (Flow.simple ctx (.compare 0 .ne (.reg 21) (.imm 0))
    {s with core:=maskLoaded s.core boundary})

theorem mask_trace (running : s.halted=false)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (maskAddress s.core boundary).toNat) :
    Flow.Sequence ctx (maskCode boundary) s (masked ctx s boundary) := by
  apply Flow.sequence_append (Flow.sequence_data (Indexed.run_sound (mask_load_execution valid)) running)
  exact .cons running (.simple (by intro op h; cases h))
    (.cons running (.simple (by intro op h; cases h)) .nil)

def maskedWord (s : State) (boundary : Word) : Word := if maskFlag s boundary=0 then s.regs 8 else 0

theorem masked_value : (masked ctx s boundary).core.regs 8=maskedWord s.core boundary := by
  simp [masked,maskedWord,maskLoaded,Flow.simple,Flow.next,Flow.Compare.apply,Kernel.u32,assign,advance,Operand.eval]
  split <;> simp_all

theorem masked_frame :
    (masked ctx s boundary).core.global=s.core.global ∧
    (masked ctx s boundary).core.shared=s.core.shared ∧
    (masked ctx s boundary).core.globalStart=s.core.globalStart ∧
    (masked ctx s boundary).core.globalBytes=s.core.globalBytes ∧
    (masked ctx s boundary).core.regs 0=s.core.regs 0 ∧
    (masked ctx s boundary).core.regs 12=s.core.regs 12 ∧
    (masked ctx s boundary).halted=s.halted ∧
    (masked ctx s boundary).core.pc=s.core.pc+6 := by
  simp [masked,maskLoaded,Flow.simple,Flow.next,Flow.Compare.apply,Kernel.u32,assign,advance,Operand.eval,Nat.add_assoc]
  split <;> simp

end PtxTorchLean.Poisson.PTX.Assembly
