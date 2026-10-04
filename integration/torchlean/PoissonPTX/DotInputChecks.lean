import PoissonPTX.DotInputComplete

namespace PtxTorchLean.Poisson.PTX.DotInput.Checks

theorem uneven_tail : indices 257 0=[0,256] ∧ indices 257 1=[1] ∧ indices 257 255=[255] := by decide +kernel

theorem empty_lane : indices 1 1=[] ∧ indices 0 0=[] := by decide +kernel

/-- Without the supported size bound, unsigned addition can wrap backwards.
The nonwrapping-progress premise therefore has real semantic content. -/
theorem wraparound : (Kernel.u32 (add32 (BitVec.ofNat 64 (2^32-1)) 256)).toNat=255 := by decide +kernel

/-- Literal comparison limits are also 32-bit. Dropping CountsFit from native
guard translation would let a very large bound silently become zero. -/
theorem truncated_guard : Flow.Compare.ge.apply 0 (BitVec.ofNat 64 (2^32))=true ∧
    ¬(2^32:Nat)≤0 := by decide +kernel

def initial (memory : Memory) : Flow.State :=
  ⟨⟨0,(fun _ => 0),memory,(fun _ => 0),0,8192,0,2048⟩,(fun _ => true),false⟩

def context : Kernel.Context := ⟨0,0,0⟩

/-- A lane really executes two iterations at size 257, for arbitrary memory
words and initially true predicate bits. No fixed numeric example is assumed. -/
theorem arbitrary_input (memory : Memory) :
    ∃ final, Flow.Runs context (inputProgram 257 0 4096 0) (initial memory) final ∧
      final.core.pc=20 ∧ final.halted=false ∧
      decode (final.core.regs 8)=partialSum context 0 (initial memory) 257 0 4096 := by
  obtain ⟨final,run,done,live,result,_⟩ := input_exists context 0 (initial memory) rfl rfl
    (count:=257) (left:=0) (right:=4096) (by decide +kernel) (by
      simp [Arrays,setup,initial,context,assign,advance])
  exact ⟨final,run,done,live,result⟩

end PtxTorchLean.Poisson.PTX.DotInput.Checks
