import PoissonPTX.CellFinalSnapshot
import PoissonPTX.CellFinalLayout
import PoissonPTX.ContractionChecks

namespace PtxTorchLean.Poisson.PTX.CellFinal.Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Asymmetric matrices distinguish row/column, coefficient and accumulator
mistakes. Cell one and lane two distinguish local from global output indexing. -/
def initial : PTX.State := {
  pc:=0, regs:=fun r => if r=14 then 2 else if r=15 ∨ r=16 then 1 else 0,
  global:=fun a => if a<32 then Contraction.Checks.memory4
    0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0x4010000000000000 a
    else if 64≤a ∧ a<96 then Contraction.Checks.memory4
    0x4000000000000000 0 0x3ff0000000000000 0x4008000000000000 (a-64) else 0,
  shared:=fun a => if 160≤a ∧ a<192 then Contraction.Checks.memory4
    0x3ff0000000000000 0x4000000000000000 0x4008000000000000 0x4010000000000000 (a-160)
    else if 192≤a ∧ a<224 then Contraction.Checks.memory4
    0x4014000000000000 0x4018000000000000 0x401c000000000000 0x4020000000000000 (a-192) else 0,
  globalStart:=0,globalBytes:=256,sharedStart:=0,sharedBytes:=224 }
def start : Kernel.State := ⟨initial,false,false⟩
def ctx : Kernel.Context := ⟨0,2,1⟩
def code : List Kernel.Instr := program 2 0 64 160

theorem input_bounds : Inputs initial 2 0 64 := by
  intro k hk
  interval_cases k <;> unfold Contraction.Valid <;> decide +kernel
theorem store_bounds : Valid64 initial.globalStart initial.globalBytes (location initial 2 160).toNat := by decide +kernel

theorem completed_value :
    (Kernel.execute ctx code 1000 start).map (fun s => (read64 s.core.global 208,s.halted))=
      some (0x4044800000000000,true) := by decide +kernel

theorem exists_fetched : ∃ final, Kernel.Run ctx code start final := by
  simpa [code] using fetched_exists (ctx:=ctx) start rfl input_bounds store_bounds [] rfl

/-- A subtraction at the final join is observably different from addition. -/
theorem wrong_sum_changes_result :
    (Kernel.execute ctx (code.set ((arithmetic 2 0 64).length-1)
      (.data (.fp .sub 11 (.reg 8) (.reg 9)))) 1000 start).map (fun s => read64 s.core.global 208)≠
      some 0x4044800000000000 := by decide +kernel

theorem short_output_rejected :
    Kernel.execute ctx code 1000 {start with core:={initial with globalBytes:=208}}=none := by decide +kernel

theorem unaligned_output_rejected :
    Kernel.execute ctx (program 2 0 64 161) 1000 start=none := by decide +kernel

theorem modular_index : index {initial with regs:=fun r => if r=15 then 0x40000000 else if r=14 then 2 else 0} 2=2 := by decide +kernel

theorem wrapped_extent_rejected : ¬(0x40000000*4+2<2^32) := by decide +kernel

end PtxTorchLean.Poisson.PTX.CellFinal.Checks
