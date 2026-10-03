import PoissonPTX.ConcurrentOwnership

/-! Lane bounds indexed by program position, including shrinking active ranges.
These are syntactic checks on control, not assumptions about recorded accesses. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Limits

/-- At a position with limit k, only lanes numbered below k can arrive. -/
def Invariant (limit : Nat → Nat) (s : State n) : Prop :=
  ∀ thread, thread.val < limit (s.lanes thread).pc

/-- Arithmetic preserves the bound, guards establish it, and a released
full-block barrier resumes at a position permitting every lane. -/
def Boundaries (n : Nat) (program : List Instr) (limit : Nat → Nat) : Prop :=
  (∀ pc op, program[pc]?=some (.data op) → limit pc≤limit (pc+1)) ∧
  (∀ pc count target, program[pc]?=some (.skip count target) →
    count≤limit (pc+1) ∧ n≤limit target) ∧
  (∀ pc resource, program[pc]?=some (.sync resource) → n≤limit (pc+1))

theorem step_invariant {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (inv : Invariant limit s) (bounds : Boundaries n program limit) :
    Invariant limit out.state := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      rw [data_pc hd]
      exact Nat.lt_of_lt_of_le (inv selected) (bounds.1 _ _ fetch)
    · simpa [setLane,Function.update,eq] using inv thread
  | skip =>
    intro thread
    by_cases eq : thread=selected
    · subst thread
      simp only [setLane,Function.update_self]
      split
      · exact Nat.lt_of_lt_of_le ‹_› (bounds.2.1 _ _ _ fetch).1
      · exact Nat.lt_of_lt_of_le selected.isLt (bounds.2.1 _ _ _ fetch).2
    · simpa [setLane,Function.update,eq] using inv thread
  | @sync resource =>
    intro thread
    simp only [synchronize]
    split
    · exact inv thread
    · exact inv thread
    · rename_i released
      have same := release_aligned cfg s selected resource aligned released thread
      simpa [advance,same] using Nat.lt_of_lt_of_le thread.isLt (bounds.2.2 _ _ fetch)

theorem runs_invariant {start : State n} (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant limit start) (bounds : Boundaries n program limit) :
    Invariant limit final := by
  induction run with
  | nil => exact inv
  | cons step tail ih => exact ih (step_aligned step aligned) (step_invariant step aligned inv bounds)

/-- Every recorded access inherits the bound at its actual fetched position. -/
theorem access_active {start : State n} (run : Runs cfg program start events final)
    (aligned : Aligned start) (inv : Invariant limit start) (bounds : Boundaries n program limit)
    (member : Event.data thread access∈events) : thread.val<limit access.data.pc := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have active := runs_invariant hp aligned inv bounds thread
  cases hd <;> simpa using active

end PtxTorchLean.Poisson.PTX.Concurrent.Limits
