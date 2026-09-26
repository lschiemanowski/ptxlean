import PtxBinary32.GridDenseExists
import PtxBinary32.GridDenseUniversal

/-! Array interface for completed admitted grid reductions and explicit empty
launches. Both universal outputs and a separate execution witness are available. -/
namespace Ptx.Scalar.Parallel.GridDense
inductive Launch (s : Dense.Shape) (before : List Word) : List Word → Prop
  | empty (zero : s.rows=0) : Launch s before before
  | kernel (bounds : Bounds s) (seeds : Fin s.threads → Scalar.State)
      {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
      (run : Grid.Runs (config s bounds) (Dense.program s) (initial s before seeds) events final)
      (halted : ∀ g t, ((final.blocks g).lanes t).halted=true)
      (admitted : Grid.Memory.Admitted (Dense.program s) (initial s before seeds) events) :
      Launch s before final.global

theorem launch_exists (s : Dense.Shape) (before : List Word) (bounds : 0<s.rows → Bounds s)
    (size : s.globalWords≤before.length) : ∃ after, Launch s before after := by
  by_cases zero : s.rows=0
  · exact ⟨before,.empty zero⟩
  · let b := bounds (by omega)
    let seeds : Fin s.threads → Scalar.State := fun _ => ⟨0,fun _ => 0,fun _ => 0,fun _ => false,[]⟩
    obtain ⟨events,final,run,halted,admitted⟩ := completed_admitted_exists s b before seeds size
    exact ⟨final.global,.kernel b seeds run.toRuns halted admitted⟩

theorem launch_correct (run : Launch s before after) :
    (∀ row : Fin s.rows, ∃ value, after[s.outputBase+row.val]?=some value ∧ Dense.Output s before row.val value) ∧
    (∀ i, i<s.outputBase → after[i]?=before[i]?) ∧ after.length=before.length := by
  cases run with
  | empty zero => exact ⟨by intro t; have := t.isLt; omega,fun _ _ => rfl,rfl⟩
  | kernel bounds seeds run halted admitted =>
    obtain ⟨source,co,valid⟩ := admitted
    have result := completed_forward _ _ _ _ run halted source co valid
    exact ⟨result.1,result.2.1,result.2.2.1⟩
end Ptx.Scalar.Parallel.GridDense
