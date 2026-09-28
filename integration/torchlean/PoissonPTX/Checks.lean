import PoissonPTX.Tensor

/-! Closed instruction executions are reduced by Lean's kernel, not by a native
oracle. The universal correspondence theorem is independent of these examples. -/
namespace PtxTorchLean.Poisson.PTX.Kernel.Checks

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def initial : State := {
  core := {
    pc := 0, regs := fun _ => 0,
    global := write64 (write64 (fun _ => 0) 0 0x4008000000000000) 8 0x3ff0000000000000,
    shared := fun _ => 0,
    globalStart := 0, globalBytes := 24, sharedStart := 0, sharedBytes := 0 },
  predicate := false, halted := false }

def context : Context := ⟨0,0,0⟩
def code : List Instr := Residual.program 1 0 8 16

theorem subtract_stored_words :
    ((execute context code 20 initial).map fun s => read64 s.core.global 16) =
      some 0x4000000000000000 := by decide +kernel

theorem no_return_no_success : execute context code 19 initial = none := by decide +kernel

theorem misaligned_load_rejected :
    execute context (Residual.program 1 1 8 16) 20 initial = none := by decide +kernel

theorem short_allocation_rejected :
    execute context code 20 {initial with core.globalBytes := 23} = none := by decide +kernel

theorem below_allocation_rejected :
    execute context code 20 {initial with core.globalStart := 8} = none := by decide +kernel

theorem padded_lane_needs_no_memory :
    ((execute ⟨0,1,0⟩ code 6 {initial with core.globalBytes := 0}).map fun s =>
      (s.halted, s.core.pc, read64 s.core.global 0)) =
      some (true,6,0x4008000000000000) := by decide +kernel

end PtxTorchLean.Poisson.PTX.Kernel.Checks
