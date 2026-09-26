import PtxDenseForward
import PtxBinary32.GridDenseLaunch

namespace PtxTorchLean.GridDenseForward
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel PtxTorchLean.DenseForward
open TorchLean TorchLean.Tensor

/-- Every admitted completed execution approximates the actual TorchLean graph.
No desired load values, intermediate arithmetic identities, concrete-read
policy or selected schedule appear among the premises. -/
theorem universal_forward (s : Dense.Shape) (bounds : GridDense.Bounds s) (global : List Word)
    (seeds : Fin s.threads → Ptx.Scalar.State)
    (x : Tensor ℝ (DenseVJP.column s.columns))
    (w : Tensor ℝ (DenseVJP.matrix s.rows s.columns))
    (b : Tensor ℝ (DenseVJP.column s.rows)) (encoding : Encoding s global x w b)
    {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (GridDense.config s bounds) (Dense.program s) (GridDense.initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co)
    (valid : GridDense.Admitted s global seeds events source co) :
    (∀ row : Fin s.rows, ∃ value, final.global[s.outputBase+row.val]?=some value ∧
      finiteReal value=some (max (encoding.row row).affine 0) ∧
      |max (encoding.row row).affine 0-
        Spec.get2 ((DenseVJP.graph s.rows s.columns).forward (DenseVJP.inputs x w b)) row 0| ≤ (encoding.row row).error) ∧
    (∀ i, i<s.outputBase → final.global[i]?=global[i]?) ∧
    final.global.length=global.length ∧ (∀ g, (final.blocks g).shared.length=s.sharedWords) ∧
    (∀ event ∈ events, Grid.AccessSafe (GridDense.initial s global seeds) event) := by
  obtain ⟨values,inputs,gl,sl,safe⟩ := GridDense.completed_forward s bounds global seeds run halted source co valid
  refine ⟨?_,inputs,gl,sl,safe⟩
  intro row
  obtain ⟨value,stored,correct⟩ := values row
  exact ⟨value,stored,output_accuracy encoding row value correct⟩

/-- Nonvacuity under storage/resource bounds. Numerical conditions only interpret
outputs; they are not needed by the instruction-execution construction. -/
theorem forward_exists (s : Dense.Shape) (bounds : 0<s.rows → GridDense.Bounds s) (global : List Word)
    (x : Tensor ℝ (DenseVJP.column s.columns)) (w : Tensor ℝ (DenseVJP.matrix s.rows s.columns))
    (b : Tensor ℝ (DenseVJP.column s.rows)) (encoding : Encoding s global x w b)
    (size : s.globalWords≤global.length) :
    ∃ after, GridDense.Launch s global after ∧
      ∀ row : Fin s.rows, ∃ value, after[s.outputBase+row.val]?=some value ∧
        finiteReal value=some (max (encoding.row row).affine 0) ∧
        |max (encoding.row row).affine 0-
          Spec.get2 ((DenseVJP.graph s.rows s.columns).forward (DenseVJP.inputs x w b)) row 0|≤(encoding.row row).error := by
  obtain ⟨after,run⟩ := GridDense.launch_exists s global bounds size
  refine ⟨after,run,?_⟩
  intro row
  obtain ⟨value,saved,correct⟩ := (GridDense.launch_correct run).1 row
  exact ⟨value,saved,output_accuracy encoding row value correct⟩

end PtxTorchLean.GridDenseForward
