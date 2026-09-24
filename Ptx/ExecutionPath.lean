import Ptx.ScalarRules

/-! Shared finite-path rules. Existing Mixed names are retained for compatibility. -/
namespace Ptx.Scalar.Mixed

/-- A finite advancing prefix has no implicit exit or fuel interpretation. -/
inductive Path (advance : S → E → S → Prop) : S → List E → S → Prop where
  | nil : Path advance s [] s
  | cons : advance s event next → Path advance next rest final →
      Path advance s (event :: rest) final

theorem Path.append (first : Path advance s xs middle) (second : Path advance middle ys final) :
    Path advance s (xs ++ ys) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

theorem Path.invariant (property : S → Prop)
    (preserved : ∀ s event next, property s → advance s event next → property next)
    (path : Path advance s trace final) (initial : property s) : property final := by
  induction path with
  | nil => exact initial
  | cons step _ ih => exact ih (preserved _ _ _ initial step)

theorem Path.event_origin (path : Path advance s trace final) (member : event ∈ trace) :
    ∃ before after, advance before event after := by
  induction path with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, _, step⟩
    · exact ih member

end Ptx.Scalar.Mixed
