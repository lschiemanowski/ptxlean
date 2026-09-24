import Ptx.PureKernel

/-! Composition and termination rules for the existing execution relation. -/
namespace Ptx.Scalar.PureKernel

variable {Kind : Type} {catalog : Catalog Kind} {program : List (Instr catalog)}

theorem Run.prepend (path : Path (Advances target program) s front middle)
    (run : Run target program middle final status suffix) :
    Run target program s final status (front ++ suffix) := by
  induction path with
  | nil => exact run
  | cons step _ ih => exact .next step (ih run)

/-- A halting witness controls every execution prefix only for a proved functional catalog. -/
theorem Run.complete_prefix (functional : Functional catalog)
    (run : Run target program s final .halted trace)
    (path : Path (Advances target program) s front middle) :
    ∃ suffix, Run target program middle final .halted suffix ∧
      trace = front ++ suffix ∧ front.length < trace.length := by
  induction path generalizing trace with
  | nil =>
    refine ⟨trace, run, rfl, ?_⟩
    cases run <;> simp
  | cons step _ ih =>
    cases run with
    | next other rest =>
      have eq := dispatch_deterministic functional step other
      cases eq
      obtain ⟨suffix, hr, ht, hl⟩ := ih rest
      exact ⟨suffix, hr, by simp [ht], by simpa using hl⟩
    | halted other =>
      have eq := dispatch_deterministic functional step other
      cases eq

/-- Infinite here means a next-instruction transition at every natural-number time. -/
theorem Run.no_infinite_advances (functional : Functional catalog)
    (run : Run target program s final .halted trace) :
    ¬ ∃ (states : Nat → State) (events : Nat → Event catalog), states 0 = s ∧
      ∀ n, Advances target program (states n) (events n) (states (n+1)) := by
  rintro ⟨states, events, start, steps⟩
  have paths : ∀ n, ∃ front, Path (Advances target program) s front (states n) ∧
      front.length = n := by
    intro n
    induction n with
    | zero => exact ⟨[], start ▸ .nil, rfl⟩
    | succ n ih =>
      obtain ⟨front, hp, hl⟩ := ih
      exact ⟨front ++ [events n], hp.append (.cons (steps n) .nil), by simp [hl]⟩
  obtain ⟨front, hp, hl⟩ := paths trace.length
  obtain ⟨_, _, _, bound⟩ := run.complete_prefix functional hp
  omega

end Ptx.Scalar.PureKernel
