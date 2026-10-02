import PoissonPTX.CellEntryJointCorrespondence
import PoissonPTX.CellEntryRebaseChecks

namespace PtxTorchLean.Poisson.PTX.CellEntry.JointChecks
open Checks RebaseChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The nonzero connectivity and source arrays precede the output array. -/
def inputs (owner : Fin 32) (active : owner.val<2*2) :
    Control.InputLayout memory (CellPrologue.threadContext bases 1 owner) 2 0 64 256 := by
  refine ⟨4,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel +revert

attribute [local irreducible] result bodyResult whole

theorem joint_indices : IndexSources.Compatible memory (result.events++bodyResult.events)
    result.indices (fun _ _ => .initial) := by
  intro r owner access observed k
  exact Checks.index_compatible r owner access observed k

/-- Derive the prefix contracts from the nonzero joint trace, rather than
passing the existing prefix certificates to the composition theorem. -/
theorem derived_prefix :
    Concurrent.Visibility.Compatible initial result.events (fun _ _ => .initial) ∧
    IndexSources.Compatible memory result.events result.indices (fun _ _ => .initial) :=
  Control.joint_sources actual_run ProducerChecks.aligned (by intro u; rfl) completed.1
    (by decide) (by decide) (by decide) inputs actual_body
    (by unfold Concurrent.CellConsumer.WithOutput.OutputBounds; decide +kernel)
    joint_indices (by simpa only [whole] using RebaseChecks.compatible)

/-- A layout that places output over the connectivity load cannot satisfy the
separation condition used to justify initialization sources. -/
theorem overlapping_output_rejected :
    ¬Nonempty (Control.InputLayout memory (CellPrologue.threadContext bases 1 (0 : Fin 32)) 2 0 64 16) := by
  rintro ⟨layout⟩
  have bad := layout.cellsEnd
  norm_num [CellPrologue.threadContext] at bad

end PtxTorchLean.Poisson.PTX.CellEntry.JointChecks
