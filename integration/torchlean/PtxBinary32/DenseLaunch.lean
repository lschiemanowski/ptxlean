import PtxBinary32.DenseReadSources

/-! A model-level launch wrapper: an empty output requires no threads and no
instruction execution. This is not a CUDA runtime or ABI implementation. -/
namespace Ptx.Scalar.Parallel.Dense

/-- A missing instruction list means return the empty output without a launch.
A nonempty list still needs the existing resource and storage checks. -/
def launchPlan (s : Shape) : Option (List Instr) :=
  if s.rows=0 then none else some (program s)

@[simp] theorem launchPlan_empty (s : Shape) (empty : s.rows=0) : launchPlan s=none := by
  simp [launchPlan,empty]

theorem launchPlan_kernel (s : Shape) (b : Bounds s) : launchPlan s=some (program s) := by
  simp [launchPlan,Nat.ne_of_gt b.nonempty]

/-- The wrapper has an explicit no-launch case; it never fabricates a zero-thread
configuration. A launched execution retains ordinary completion and admission. -/
inductive ForwardRun (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State) :
    List (Event s.threads) → Parallel.State s.threads → Prop
  | empty (zero : s.rows=0) : ForwardRun s global shared seeds [] (initial s global shared seeds)
  | kernel (b : Bounds s) {events final}
      (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
      (halted : ∀ t, (final.lanes t).halted=true)
      (admitted : ∃ source co, Admitted s b global shared seeds run source co) :
      ForwardRun s global shared seeds events final

/-- No-launch is total for empty outputs and leaves both arenas exactly intact. -/
theorem empty_forward (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    (empty : s.rows=0) :
    ∃ final, ForwardRun s global shared seeds [] final ∧ final.global=global ∧ final.shared=shared ∧
      (∀ t, (final.lanes t).halted=true) := by
  refine ⟨initial s global shared seeds,.empty empty,rfl,rfl,?_⟩
  intro t
  have ht := t.isLt
  simp [Shape.threads,empty] at ht

/-- Every admitted wrapper execution with no output rows is this no-op. -/
theorem empty_forward_unique (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State)
    {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (empty : s.rows=0) (run : ForwardRun s global shared seeds events final) :
    events=[] ∧ final=initial s global shared seeds := by
  cases run with
  | empty => exact ⟨rfl,rfl⟩
  | kernel b _ _ _ => have := b.nonempty; omega

end Ptx.Scalar.Parallel.Dense
