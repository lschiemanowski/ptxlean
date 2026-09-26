import PtxBinary32.DenseUniversal
import PtxBinary32.DenseAdmission

namespace Ptx.Scalar.Parallel.Dense

/-- Array-level completed-launch interface, retaining the actual machine run. -/
inductive Launch (s : Shape) (before : List Word) : List Word → Prop
  | empty (zero : s.rows=0) : Launch s before before
  | kernel (bounds : Bounds s) (seeds : Fin s.threads → Scalar.State)
      {events : List (Event s.threads)} {final : State s.threads}
      (run : Runs (config s bounds) (program s) (initial s before (List.replicate s.sharedWords 0) seeds) events final)
      (halted : ∀ t, (final.lanes t).halted=true)
      (admitted : ∃ source co, Admitted s bounds before (List.replicate s.sharedWords 0) seeds run source co) :
      Launch s before final.global

theorem launch_exists (s : Shape) (before : List Word) (bounds : s.rows>0 → Bounds s)
    (size : s.globalWords≤before.length) : ∃ after, Launch s before after := by
  by_cases zero : s.rows=0
  · exact ⟨before,.empty zero⟩
  · let seeds : Fin s.threads → Scalar.State := fun _ => ⟨0,fun _ => 0,fun _ => 0,fun _ => false,[]⟩
    obtain ⟨events,final,run,source,co,valid,_,halted,_⟩ := selected_forward_admitted s (bounds (by omega)) before
      (List.replicate s.sharedWords 0) seeds size (by simp)
    exact ⟨final.global,.kernel (bounds (by omega)) seeds run.toRuns (fun t => (halted t).1) ⟨source,co,valid⟩⟩

theorem launch_correct (run : Launch s before after) :
    (∀ row : Fin s.rows, ∃ value, after[s.outputBase+row.val]?=some value ∧ Output s before row.val value) ∧
    (∀ i, i<s.outputBase → after[i]?=before[i]?) ∧ after.length=before.length := by
  cases run with
  | empty zero => exact ⟨by intro t; have := t.isLt; omega,fun _ _ => rfl,rfl⟩
  | kernel bounds seeds run halted admitted =>
    obtain ⟨source,co,valid⟩ := admitted
    have result := completed_forward _ _ _ _ _ run halted source co valid
    exact ⟨result.1,result.2.1,result.2.2.1⟩

end Ptx.Scalar.Parallel.Dense
