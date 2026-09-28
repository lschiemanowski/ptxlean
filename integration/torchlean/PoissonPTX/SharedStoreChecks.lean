import PoissonPTX.SharedPlane

namespace PtxTorchLean.Poisson.PTX.SharedStore.Checks

def state : State := {
  pc := 0, regs := fun r => if r=3 then 64 else if r=14 then 3 else if r=8 then 0x7ff8000000000123 else 0
  global := fun _ => 19, shared := fun _ => 7,
  globalStart := 0, globalBytes := 0, sharedStart := 64, sharedBytes := 224 }

/-- Store raw bits, including NaN payload, into the last slot of plane six. -/
theorem last_plane : (run (code 192 8) state).map
    (fun t => (read64 t.shared 280,t.shared 279,t.shared 288,t.global 280,t.pc)) =
      some (0x7ff8000000000123,7,7,19,3) := by decide +kernel

theorem outside_rejected : run (code 224 8) state = none := by decide +kernel

theorem misaligned_rejected : run (code 193 8) state = none := by decide +kernel

/-- Aliasing the source with scratch really changes the stored word. The source
exclusions in run_store are necessary, not cosmetic conditions. -/
theorem scratch_source : (run (code 192 1) state).map
    (fun t => read64 t.shared 280) = some 24 := by decide +kernel

theorem bad_lane_rejected : run (code 192 8)
    {state with regs := Function.update state.regs 14 4} = none := by decide +kernel

def finals (i : Fin 4) : State :=
  {state with shared := write64 state.shared (SharedPlane.address 64 2 6 i.val) (BitVec.ofNat 64 (100+i.val))}

theorem reversed_publication :
    read64 (SharedPlane.publish state.shared 64 2 6 finals [3,2,1,0]) 280 = 103 ∧
    read64 (SharedPlane.publish state.shared 64 2 6 finals [0,1,2,3]) 256 = 100 := by decide +kernel

end PtxTorchLean.Poisson.PTX.SharedStore.Checks
