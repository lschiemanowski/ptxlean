import PoissonPTX.CellOutputTensor
import PoissonPTX.CellTailAddressChecks

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks
open Ptx CellMiddle Publication
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
attribute [local irreducible] Checks.result

theorem cells : ∀ t, (Checks.start.core.lanes t).regs 15=0 := by decide +kernel

/-- The existing completed concurrent execution publishes the whole local
TorchLean tensor, even into an arbitrary pre-existing byte memory. -/
theorem tensor_output (memory : Memory) (order : List (Event 32))
    (permutation : order.Perm Checks.result.events) :
    tensor 2 0 0 160 (GlobalPublication.publish memory order)=localAction
      (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 0)
      (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 64)
      (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 128)
      (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .shared 0) := by
  apply published_tensor Checks.launch (by decide) (by decide) Checks.actual_run
    AddressChecks.launch_bounds (by decide) cells Checks.compatible Checks.performed permutation
  intro t _
  rw [(Checks.returned t).2]; omega

theorem reversed_output (memory : Memory) :
    tensor 2 0 0 160 (GlobalPublication.publish memory Checks.result.events.reverse)=
    tensor 2 0 0 160 (GlobalPublication.publish memory Checks.result.events) := by
  rw [tensor_output memory _ (List.reverse_perm _),tensor_output memory _ (List.Perm.refl _)]

/-- A separate actually executed tail publishes nonzero bits at the address
computed from a nonzero base, cell and lane. This is a storage regression,
not an extra full-cell numerical witness. -/
theorem nonzero_publication (memory : Memory) :
    read64 (GlobalPublication.publish memory AddressChecks.sampleResult.events) 336=
      0x3ff0000000000000 := by
  rw [AddressChecks.nonzero_store.1]
  simp [GlobalPublication.publish,GlobalPublication.applyEvent]

theorem missing_store_rejected : ¬GlobalPublication.Present ([] : List (Event 32)) 160 0 := by
  simp [GlobalPublication.Present]

/-- The generic merger refuses to justify a word when another recorded store
partially overlaps it. Disjointness cannot be replaced by distinct addresses. -/
theorem overlapping_store_rejected : ¬GlobalPublication.Safe
    ([.data 0 ⟨.global,⟨0,true,161,1⟩⟩] : List (Event 32)) 160 0 := by
  intro safe
  have h := safe 0 ⟨.global,⟨0,true,161,1⟩⟩ (by simp) rfl rfl
  norm_num at h

theorem coefficient_bytes_preserved (memory : Memory) (p : Nat) (before : p<160) :
    GlobalPublication.publish memory Checks.result.events p=memory p := by
  apply published_outside Checks.launch (by decide) (by decide) Checks.actual_run (List.Perm.refl _)
  intro t
  left
  have address := CellFinal.location_exact (Checks.start.core.lanes t) (by decide : 2≤5)
    (AddressChecks.launch_bounds t).1 (AddressChecks.launch_bounds t).2
  rw [address]
  have base := Checks.launch.global t
  have offset : (160 : Word).toNat=160 := by decide
  have zero : (0 : Word).toNat=0 := by decide
  rw [base,offset,zero]
  omega

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks
