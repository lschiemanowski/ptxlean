import PoissonPTX.ControlFlowObserved

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Prove a state invariant and properties of all recorded accesses together.
The step proof may use membership in the fixed whole-history record lists,
which is needed when source choices refer to that same history. -/
theorem walk {allWords : List Concurrent.Access} {allIndices : List IndexSources.Access} {P : State → Prop} {W : Concurrent.Access → Prop} {I : IndexSources.Access → Prop}
    (run : Runs ctx program s words indices t)
    (wordSubset : ∀ a∈words, a∈allWords) (indexSubset : ∀ a∈indices, a∈allIndices)
    (initial : P s)
    (check : ∀ s t access index, Step ctx program s t access index →
      (∀ a, access=some a → a∈allWords) → (∀ a, index=some a → a∈allIndices) → P s →
      P t ∧ (∀ a, access=some a → W a) ∧ (∀ a, index=some a → I a)) :
    P t ∧ (∀ a∈words, W a) ∧ (∀ a∈indices, I a) := by
  induction run with
  | nil => exact ⟨initial,by simp,by simp⟩
  | @cons s middle access index words indices t step rest ih =>
    have first := check s middle access index step
      (fun a eq => wordSubset a (by simp [eq])) (fun a eq => indexSubset a (by simp [eq])) initial
    obtain ⟨final,wordProps,indexProps⟩ := ih (fun a member => wordSubset a (List.mem_append_right _ member))
      (fun a member => indexSubset a (List.mem_append_right _ member)) first.1
    refine ⟨final,?_,?_⟩
    · intro a member
      rcases List.mem_append.mp member with one | later
      · exact first.2.1 a (by simpa using one)
      · exact wordProps a later
    · intro a member
      rcases List.mem_append.mp member with one | later
      · exact first.2.2 a (by simpa using one)
      · exact indexProps a later

end PtxTorchLean.Poisson.PTX.Flow.Observed
