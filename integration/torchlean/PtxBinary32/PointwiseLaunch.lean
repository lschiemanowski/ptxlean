import PtxBinary32.PointwiseExists

/-! Completed launch composition at an array interface. No-launch handles zero
lanes. The interface exposes actual final global words, not desired outputs. -/
namespace Ptx.Scalar.Parallel.Pointwise

inductive Launch (op : Op) (l : Layout n) (before : List Word) : List Word → Prop
  | empty (zero : n=0) : Launch op l before before
  | kernel (positive : 0<n) (resource : n≤1024) (seeds : Fin n → Scalar.State)
      {events : List (Event n)} {final : State n}
      (run : Runs (config positive) (program op) (initial l before [] seeds) events final)
      (halted : ∀ t, (final.lanes t).halted=true)
      (admitted : ∃ source co, Admitted op l before [] seeds run source co) : Launch op l before final.global

theorem launch_exists (op : Op) (l : Layout n) (before : List Word)
    (resource : n≤1024) (size : l.prefixWords+n≤before.length) : ∃ after, Launch op l before after := by
  by_cases zero : n=0
  · exact ⟨before,.empty zero⟩
  · let seeds : Fin n → Scalar.State := fun _ => ⟨0,fun _ => 0,fun _ => 0,fun _ => false,[]⟩
    obtain ⟨events,final,run,halted,source,co,valid⟩ := admitted_exists op l before [] seeds (by omega) size
    exact ⟨final.global,.kernel (by omega) resource seeds run halted ⟨source,co,valid⟩⟩

theorem launch_correct (run : Launch op l before after) :
    (∀ t, ∃ value, after[l.output t]?=some value ∧ Result op before[l.left t]! before[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → after[i]?=before[i]?) ∧ after.length=before.length := by
  cases run with
  | empty zero => exact ⟨by intro t; have := t.isLt; omega,fun _ _ => rfl,rfl⟩
  | kernel positive resource seeds run halted admitted =>
    obtain ⟨source,co,valid⟩ := admitted
    have result := completed _ _ _ _ _ run halted source co valid
    exact ⟨result.1,result.2.1,result.2.2.1⟩

/-- Safety is a property of every represented launch trace, separately from
its arithmetic conclusion. -/
theorem launch_access_safe (op : Op) (l : Layout n) (before : List Word) (seeds : Fin n → Scalar.State)
    {positive : 0<n} {events : List (Event n)} {final : State n}
    (run : Runs (config positive) (program op) (initial l before [] seeds) events final) :
    ∀ event ∈ events, AccessSafe (initial l before [] seeds) event := runs_access_safe run

end Ptx.Scalar.Parallel.Pointwise
