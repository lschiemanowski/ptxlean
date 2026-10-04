import PoissonPTX.ScalarEntry
import PoissonPTX.ScalarFrames

namespace PtxTorchLean.Poisson.PTX.Scalar.RestartFlag

def body (active : Word) : List Instr := store32Code active (.imm 1)
def entry (active : Word) : List Instr := program (body active)

theorem body_segment : ∀ i∈body active, segment i=true := by
  simp [body,store32Code,address4Code,segment,Flow.segment]

theorem entry_correct (run : Runs ctx (entry active) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (ctx.arena+active).toNat) :
    read32 final.core.global (ctx.arena+active).toNat=1 ∧
    (∀ byte, byte<(ctx.arena+active).toNat ∨ (ctx.arena+active).toNat+4≤byte → final.core.global byte=s.core.global byte) := by
  obtain ⟨middle,trace,eq⟩ := entry_result run pc running done body_segment
  have same := store32_state trace
    (by simpa only [setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1] using valid) running
  subst final middle
  simp only [Flow.halt,Flow.next,advance,stored32_global,setup_frame.1,setup_frame.2.2.2.1,
    Operand.eval,Kernel.u32,read32_write32]
  refine ⟨rfl,?_⟩
  intro byte outside
  exact write32_outside _ _ _ _ outside

theorem entry_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (valid : Valid32 s.core.globalStart s.core.globalBytes (ctx.arena+active).toNat) :
    ∃ final, Runs ctx (entry active) s final ∧ final.halted=true := by
  have trace := store32_trace (ctx:=ctx) (s:=setup ctx s) (value:=.imm 1) running
    (by simpa only [setup_frame.2.1,setup_frame.2.2.1,setup_frame.2.2.2.1] using valid)
  exact ⟨_,entry_executes trace body_segment pc running,rfl⟩

theorem entry_length : (entry active).length=8 := by
  simp [entry,program,prologue,body,store32Code,address4Code]

end PtxTorchLean.Poisson.PTX.Scalar.RestartFlag
