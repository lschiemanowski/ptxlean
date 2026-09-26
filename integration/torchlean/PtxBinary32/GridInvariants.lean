import PtxBinary32.GridHistory
import PtxBinary32.ParallelAddressControl

/-! Lift group-local invariants through actual grid steps. The global-change
obligation is explicit: registers/control may ignore other stores, memory facts
may not. Concrete applications must discharge both preservation obligations. -/
namespace Ptx.Scalar.Parallel.Grid

def Invariant (property : Fin groups → Parallel.State n → Prop) (s : State groups n) : Prop :=
  ∀ g, property g (view s g)

theorem step_invariant {s final : State groups n} {events : List (Event groups n)}
    (step : Step cfg program s events final)
    (property : Fin groups → Parallel.State n → Prop)
    (foreign : ∀ g state memory, property g state → property g {state with global := memory})
    (own : ∀ g candidate t state out, Parallel.Step (cfg.group g) program candidate t state out →
      property g state → property g out.state)
    (before : Invariant property s) : Invariant property final := by
  cases step with
  | issue g t candidate out step =>
    intro h
    by_cases eq : h=g
    · subst h; rw [view_install_same]; exact own g candidate t _ out step (before g)
    · rw [view_install_other _ _ _ _ eq]; exact foreign h _ _ (before h)

theorem runs_invariant {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final)
    (property : Fin groups → Parallel.State n → Prop)
    (foreign : ∀ g state memory, property g state → property g {state with global := memory})
    (own : ∀ g candidate t state out, Parallel.Step (cfg.group g) program candidate t state out →
      property g state → property g out.state)
    (before : Invariant property s) : Invariant property final := by
  induction run with
  | nil => exact before
  | cons step _ ih => exact ih (step_invariant step property foreign own before)

theorem runs_address_control {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (seeds : Fin groups → Fin n → Scalar.State)
    (compatible : AddressControl.ProgramCompatible program)
    (aligned : ∀ g, Parallel.Aligned (view s g))
    (initial : ∀ g, AddressControl.Invariant program (seeds g) (view s g)) :
    ∀ g, AddressControl.Invariant program (seeds g) (view final g) := by
  let property := fun g state => Parallel.Aligned state ∧ AddressControl.Invariant program (seeds g) state
  have lifted : Invariant property final := runs_invariant run property
    (by intro g state memory inv; exact inv)
    (by intro g candidate t state out step inv
        exact ⟨Parallel.step_aligned step inv.1,AddressControl.step_invariant step compatible inv.2 inv.1⟩)
    (fun g => ⟨aligned g,initial g⟩)
  exact fun g => (lifted g).2

end Ptx.Scalar.Parallel.Grid
