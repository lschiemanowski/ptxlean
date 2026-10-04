import PoissonPTX.ScalarObservedMemory

namespace PtxTorchLean.Poisson.PTX.Scalar.Observed

theorem eval_position (actual : Eval ctx i s t events) (plain : segment i=true) : t.core.pc=s.core.pc+1 := by
  cases actual with
  | extra _ actual => exact segment_pc actual plain
  | store32 => rfl
  | base actual =>
    cases actual with
    | data actual => exact Indexed.Candidate.data_pc actual
    | simple ordinary => exact Flow.linear_pc (.simple ordinary) (Flow.segment_linear plain)

theorem eval_running (actual : Eval ctx i s t events) (plain : segment i=true) : t.halted=s.halted := by
  cases actual with
  | extra _ actual => exact segment_running actual plain
  | store32 => rfl
  | base actual =>
    cases actual with
    | data => rfl
    | simple ordinary => exact Flow.segment_running (.simple ordinary) plain

/-- One scalar instruction records at most one access, at its actual PC. -/
theorem eval_events (actual : Eval ctx i s t events) : events=[] ∨ ∃ a, events=[a] ∧ a.pc=s.core.pc := by
  cases actual with
  | extra => exact Or.inl rfl
  | store32 => exact Or.inr ⟨_,rfl,rfl⟩
  | base actual =>
    cases actual with
    | simple => exact Or.inl rfl
    | data actual =>
      cases actual with
      | data actual => cases actual with
        | ordinary => exact Or.inl rfl
        | load => exact Or.inr ⟨_,rfl,rfl⟩
        | store => exact Or.inr ⟨_,rfl,rfl⟩
      | mad32 => exact Or.inl rfl
      | wide4 => exact Or.inl rfl
      | load32 => exact Or.inr ⟨_,rfl,rfl⟩

theorem sequence_position (actual : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true) :
    t.core.pc=s.core.pc+code.length := by
  induction actual with
  | nil => simp
  | cons alive step rest ih =>
    rw [ih (fun i mem => plain i (by simp [mem])),eval_position step (plain _ (by simp))]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem sequence_running (actual : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true) :
    t.halted=s.halted := by
  induction actual with
  | nil => rfl
  | cons alive step rest ih =>
    exact (ih (fun i mem => plain i (by simp [mem]))).trans (eval_running step (plain _ (by simp)))

theorem sequence_bounds (actual : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true) :
    ∀ a∈events, s.core.pc≤a.pc ∧ a.pc<t.core.pc := by
  induction actual with
  | nil => simp
  | @cons s i middle first code rest t alive step run ih =>
    intro a member
    have position := eval_position step (plain _ (by simp))
    have finalPosition := sequence_position run (fun i mem => plain i (by simp [mem]))
    rcases List.mem_append.mp member with here | later
    · rcases eval_events step with empty | ⟨one,single,pc⟩
      · simp [empty] at here
      · have same : a=one := by simpa [single] using here
        subst a
        omega
    · have bounds := ih (fun i mem => plain i (by simp [mem])) a later
      omega

theorem sequence_order (actual : Sequence ctx code s events t) (plain : ∀ i∈code, segment i=true) :
    events.Pairwise (fun a b => a.pc<b.pc) := by
  induction actual with
  | nil => exact .nil
  | cons alive step rest ih =>
    have tail := ih (fun i mem => plain i (by simp [mem]))
    rcases eval_events step with empty | ⟨a,single,position⟩
    · simpa [empty] using tail
    · simp only [single,List.singleton_append,List.pairwise_cons]
      refine ⟨?_,tail⟩
      intro b member
      have bounds := sequence_bounds rest (fun i mem => plain i (by simp [mem])) b member
      have next := eval_position step (plain _ (by simp))
      omega

end PtxTorchLean.Poisson.PTX.Scalar.Observed
