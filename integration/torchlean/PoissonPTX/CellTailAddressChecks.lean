import PoissonPTX.CellTailOwners
import PoissonPTX.CellTailWitnessSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks
open Ptx CellMiddle
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
attribute [local irreducible] Checks.result

theorem launch_bounds : OutputBounds 2 160 Checks.start := by decide +kernel

/-- The completed concurrent witness now uses launch bounds, with no supplied
geometry for any of its event records. -/
theorem stored (i j : Fin 2) :
    decode (read64 (Checks.result.state.core.lanes
      ⟨i.val*2+j.val,by have := i.isLt; have := j.isLt; omega⟩).global
      (CellFinal.location (Checks.start.core.lanes
        ⟨i.val*2+j.val,by have := i.isLt; have := j.isLt; omega⟩) 2 160).toNat)=
      Spec.get2 (localAction
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 0)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 64)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 128)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .shared 0)) i j := by
  apply stored_from_launch Checks.launch (by decide) (by decide) Checks.actual_run launch_bounds
    (by decide) Checks.compatible Checks.performed _ i j rfl
  rw [(Checks.returned _).2]; omega

theorem index_wrap_rejected : ¬OutputBounds 2 160
    {Checks.start with core:={Checks.start.core with
      lanes:=fun t => {Checks.start.core.lanes t with
        regs:=Function.update (Checks.start.core.lanes t).regs 15 (BitVec.ofNat 64 (2^30))}}} := by
  decide +kernel

theorem address_wrap_rejected :
    ¬OutputBounds 2 (BitVec.ofNat 64 (2^64-8)) Checks.start := by decide +kernel

/-- Nonzero base, cell ID, lane ID and stored word exercise all address terms. -/
def sample : WithTail.State 1 := ⟨⟨fun _ => {
  pc:=0, regs:=fun r => if r=0 then 64 else if r=15 then 3 else if r=14 then 2 else
    if r=11 then 0x3ff0000000000000 else 0,
  global:=fun _ => 0,shared:=fun _ => 0,
  globalStart:=64,globalBytes:=320,sharedStart:=0,sharedBytes:=0 },
  Barrier.reset 0,none⟩,fun _ => false,fun _ => false⟩
def cfg : Config 1 := ⟨0,by decide⟩
def ctx (_ : Fin 1) : Kernel.Context := ⟨64,2,3⟩
def sampleRun : Option (WithTail.Outcome 1) :=
  WithTail.execute cfg ctx [] (CellFinal.tail 2 160) (fun _ _ => 0) (List.replicate 6 0) sample
def sampleResult : WithTail.Outcome 1 := sampleRun.getD ⟨sample,[]⟩

theorem sample_executed : sampleRun=some sampleResult := by
  have h : sampleRun.isSome=true := by decide +kernel
  cases he : sampleRun with
  | none => simp [he] at h
  | some out => simp [sampleResult,he]

theorem sample_actual : WithTail.Runs cfg ctx [] (CellFinal.tail 2 160)
    sample sampleResult.events sampleResult.state := WithTail.execute_sound sample_executed

theorem nonzero_store :
    sampleResult.events=[.data 0 ⟨.global,⟨4,true,336,0x3ff0000000000000⟩⟩] ∧
    read64 (sampleResult.state.core.lanes 0).global 336=0x3ff0000000000000 ∧
    sampleResult.state.halted 0=true := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks
