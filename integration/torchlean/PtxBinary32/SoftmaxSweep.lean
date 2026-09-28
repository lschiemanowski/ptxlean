import PtxBinary32.SumProgram

/-! Sequential memory composition. Each invocation is supplied by a concrete
instruction launch; this helper supplies no arithmetic or concurrent semantics. -/
namespace Ptx.Scalar.SoftmaxSweep

inductive Run (step : Nat → List Word → List Word → Prop) :
    Nat → List Word → List Word → Prop
  | nil : Run step 0 memory memory
  | snoc : Run step count before middle → step count middle after →
      Run step (count+1) before after

def WritesOwn (step : Nat → List Word → List Word → Prop) : Prop :=
  ∀ i a b, step i a b → ∃ value, b = a.set i value

variable {step : Nat → List Word → List Word → Prop}

theorem length (writes : WritesOwn step) (run : Run step count before after) :
    after.length=before.length := by
  induction run with
  | nil => rfl
  | snoc run op ih =>
    obtain ⟨value,rfl⟩ := writes _ _ _ op
    simpa using ih

theorem outside (writes : WritesOwn step) (run : Run step count before after)
    (index : Nat) (later : count ≤ index) : after[index]?=before[index]? := by
  induction run with
  | nil => rfl
  | @snoc count before middle after run op ih =>
    obtain ⟨value,rfl⟩ := writes _ _ _ op
    rw [List.getElem?_set_ne (by omega)]
    exact ih (by omega)

/-- Locate each actual invocation. Its input cell and all cells beyond the pass
still contain their original values; later invocations preserve its result. -/
theorem occurrence (writes : WritesOwn step) (run : Run step count before after)
    (i : Nat) (inside : i<count) :
    ∃ a b, step i a b ∧ a.length=before.length ∧
      a[i]?=before[i]? ∧ (∀ j, count≤j → a[j]?=before[j]?) ∧ b[i]?=after[i]? := by
  induction run with
  | nil => omega
  | @snoc count before middle after run op ih =>
    by_cases last : i=count
    · subst i
      exact ⟨middle,after,op,length writes run,outside writes run _ (by omega),
        fun j hj => outside writes run j (by omega),rfl⟩
    · obtain ⟨a,b,hab,len,input,tail,result⟩ := ih (by omega)
      obtain ⟨value,eq⟩ := writes _ _ _ op
      refine ⟨a,b,hab,len,input,fun j hj => tail j (by omega),?_⟩
      rw [eq,List.getElem?_set_ne (by omega)]
      exact result

theorem exists_run (before : List Word) (count : Nat)
    (available : ∀ k, k<count → ∀ middle, Run step k before middle →
      ∃ after, step k middle after) : ∃ after, Run step count before after := by
  have build : ∀ k, k≤count → ∃ after, Run step k before after := by
    intro k hk
    induction k with
    | zero => exact ⟨before,.nil⟩
    | succ k ih =>
      obtain ⟨middle,run⟩ := ih (by omega)
      obtain ⟨after,next⟩ := available k (by omega) middle run
      exact ⟨after,.snoc run next⟩
  exact build count le_rfl

end Ptx.Scalar.SoftmaxSweep
