import PoissonPTX.ControlFlowSequence
import PoissonPTX.ResidualKernel

namespace PtxTorchLean.Poisson.PTX.Assembly

def prologue (count : BitVec 32) : List Flow.Instr :=
  [.context 0 .arena,.context 14 .lane,.context 15 .group,.data (.mad32 12 15 256 14),
    .compare 0 .ge (.reg 12) (.imm (count.setWidth 64)),.predRet 0 true]

def setup (ctx : Kernel.Context) (count : BitVec 32) (s : Flow.State) : Flow.State :=
  let idx := Kernel.Residual.index ctx
  let inactive := decide (count.toNat ≤ idx.toNat)
  let r := Function.update s.core.regs 0 ctx.arena
  let r := Function.update r 14 (ctx.lane.setWidth 64)
  let r := Function.update r 15 (ctx.group.setWidth 64)
  let r := Function.update r 12 (idx.setWidth 64)
  ⟨{s.core with pc:=s.core.pc+6,regs:=r},Function.update s.predicates 0 inactive,inactive⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem prologue_execution (running : s.halted=false) :
    Flow.sequence ctx (prologue count) s=some (setup ctx count s) := by
  have wide (v : BitVec 32) : v.toNat%18446744073709551616=v.toNat := Nat.mod_eq_of_lt (by have := v.isLt; omega)
  simp [prologue,Flow.sequence,Flow.eval,Flow.simple,Flow.source,Flow.next,Flow.halt,
    Flow.Compare.apply,Indexed.eval,Indexed.mad,Kernel.u32,Kernel.Residual.index,
    Operand.eval,assign,advance,setup,running,Nat.add_assoc,wide]
  split <;> simp_all

theorem setup_active (live : Kernel.Residual.live ctx count) : (setup ctx count s).halted=false := by
  simp [setup,Kernel.Residual.live] at *
  omega

theorem setup_inactive (dead : ¬Kernel.Residual.live ctx count) : (setup ctx count s).halted=true := by
  simp [setup,Kernel.Residual.live] at *
  omega

end PtxTorchLean.Poisson.PTX.Assembly
