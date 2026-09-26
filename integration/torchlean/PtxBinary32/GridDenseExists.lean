import PtxBinary32.GridDenseLocalExists
import PtxBinary32.GridAdmission

/-! Completed admitted dense grid execution, including empty output grids.
Groups run successively in this witness, always against the actual current
shared global array. The theorem for arbitrary completed runs is separate. -/
namespace Ptx.Scalar.Parallel.GridDense

theorem completed_concrete_exists (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) (size : s.globalWords≤global.length) :
    ∃ events final, Grid.ConcreteRuns (config s b) (Dense.Compact.program s) (initial s global seeds) events final ∧
      ∀ g t, ((final.blocks g).lanes t).halted=true := by
  have sweep : ∀ count, count≤s.rows → ∃ events state,
      Grid.ConcreteRuns (config s b) (Dense.Compact.program s) (initial s global seeds) events state ∧
      (∀ g : Fin s.rows, g.val<count → ∀ t, ((state.blocks g).lanes t).halted=true) ∧
      (∀ g : Fin s.rows, count≤g.val → state.blocks g=(initial s global seeds).blocks g) := by
    intro count bound
    induction count with
    | zero => exact ⟨[],initial s global seeds,.nil,by intro g hg; omega,fun _ _ => rfl⟩
    | succ count ih =>
      obtain ⟨events,state,run,done,untouched⟩ := ih (by omega)
      let g : Fin s.rows := ⟨count,by omega⟩
      have lengths := Grid.runs_lengths run.toRuns
      have gs : s.globalWords≤state.global.length := by
        simp only [initial] at lengths
        omega
      obtain ⟨next,final,localRun,halted⟩ := Local.completed_exists s b g state.global
        (List.replicate (Dense.Compact.sharedWords s) 0) seeds gs (by simp)
      have viewEq : Grid.view state g=Local.initial s g state.global (List.replicate (Dense.Compact.sharedWords s) 0) seeds := by
        simp [Grid.view,untouched g (by rfl),initial,Local.initial]
      rw [← viewEq] at localRun
      have tail := Grid.embed_concrete g localRun
      refine ⟨events++Grid.tag g next,Grid.install state g final,Grid.concrete_runs_append run tail,?_,?_⟩
      · intro h hh t
        by_cases same : h=g
        · subst h; simpa [Grid.install,Grid.localOf] using halted t
        · rw [Grid.install_local_other _ _ _ _ same]
          have ne : h.val≠count := fun eq => same (Fin.ext eq)
          exact done h (by omega) t
      · intro h hh
        have ne : h≠g := by intro eq; subst h; dsimp [g] at hh; omega
        rw [Grid.install_local_other _ _ _ _ ne]
        exact untouched h (by omega)
  obtain ⟨events,final,run,done,_⟩ := sweep s.rows (by rfl)
  exact ⟨events,final,run,fun g => done g g.isLt⟩

/-- Admission is constructed for the entire emitted grid trace, rather than
assumed for isolated groups. The witness is finite, not a fairness assertion. -/
theorem completed_admitted_exists (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) (size : s.globalWords≤global.length) :
    ∃ events final, Grid.ConcreteRuns (config s b) (Dense.Compact.program s) (initial s global seeds) events final ∧
      (∀ g t, ((final.blocks g).lanes t).halted=true) ∧
      Grid.Memory.Admitted (Dense.Compact.program s) (initial s global seeds) events := by
  obtain ⟨events,final,run,halted⟩ := completed_concrete_exists s b global seeds size
  exact ⟨events,final,run,halted,Grid.Memory.Chronology.concrete_admitted_exists run⟩
end Ptx.Scalar.Parallel.GridDense
