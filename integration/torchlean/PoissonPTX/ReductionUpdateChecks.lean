import PoissonPTX.ReductionUpdate
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.Reduction.Update.Checks
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The last active lane of the widest stage reads the last allocated word. -/
def state : State where
  pc := 0
  regs := fun r => if r=14 then 127 else 0
  global := fun _ => 23
  shared := write64 (write64 (fun _ => 0) 1016 0x3ff0000000000000)
    2040 0x4000000000000000
  globalStart := 0
  globalBytes := 0
  sharedStart := 0
  sharedBytes := 2048

theorem boundary_sum :
    (run (code 1024) state).map (fun s => read64 s.shared 1016) =
      some 0x4008000000000000 := by decide +kernel

theorem neighbor_unchanged :
    (run (code 1024) state).map (fun s => read64 s.shared 2040) =
      some 0x4000000000000000 := by decide +kernel

theorem past_end_rejected : run (code 1032) state = none := by decide +kernel

theorem misaligned_rejected : run (code 1025) state = none := by decide +kernel

/-- One ulp at 2^53 is two. Adding one rounds to the even lower neighbor;
the local arithmetic contract does not silently replace binary64 by reals. -/
def rounding : State :=
  {state with shared := write64 (write64 (fun _ => 0) 1016 0x4340000000000000) 2040 0x3ff0000000000000}

theorem rounded_addition :
    (run (code 1024) rounding).map (fun s => read64 s.shared 1016) =
      some 0x4340000000000000 := by decide +kernel

/-- Render the proved instruction list, including its real register mapping. -/
theorem instruction_text : (code 1024).map Text.data =
    ["mul.wide.u32 %off, %lane, 8;", "add.u64 %addr, %shared, %off;",
     "ld.shared.f64 %a, [%addr];", "ld.shared.f64 %b, [%addr+1024];",
     "add.rn.f64 %acc, %a, %b;", "st.shared.f64 [%addr], %acc;"] := by decide +kernel

end PtxTorchLean.Poisson.PTX.Reduction.Update.Checks
