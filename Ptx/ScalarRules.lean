import Ptx.Scalar

/-! Reusable concrete scalar verification rules. Segment exhaustion, successful
completion, and partial correctness are distinct contracts. Frame and invariant
rules also apply to candidate reads; they do not admit those candidates under a
concurrent PTX memory model. -/
namespace Ptx.Scalar.Rules

abbrev Assertion := State → Prop

/-- An exact finite prefix reaches an intermediate assertion without terminating. -/
def Segment (program : List Instr) (fuel : Nat) (pre post : Assertion) : Prop :=
  ∀ s, pre s → (run fuel program s).status = .exhausted ∧ post (run fuel program s).state

/-- A fixed-budget total-correctness contract: explicit exit and the postcondition. -/
def Completed (program : List Instr) (fuel : Nat) (pre post : Assertion) : Prop :=
  ∀ s, pre s → (run fuel program s).status = .halted ∧ post (run fuel program s).state

/-- No termination claim: this constrains only runs that explicitly halt. -/
def PartialCorrect (program : List Instr) (pre post : Assertion) : Prop :=
  ∀ s, pre s → ∀ fuel, (run fuel program s).status = .halted → post (run fuel program s).state

/-- Termination with a state-dependent finite budget. -/
def TotalCorrect (program : List Instr) (pre post : Assertion) : Prop :=
  ∀ s, pre s → ∃ fuel, (run fuel program s).status = .halted ∧ post (run fuel program s).state

theorem segment_comp (first : Segment program firstFuel pre middle)
    (second : Segment program secondFuel middle post) :
    Segment program (firstFuel + secondFuel) pre post := by
  intro s hs
  obtain ⟨hf, hm⟩ := first s hs
  obtain ⟨hh, hp⟩ := second _ hm
  rw [run_add]
  simpa only [resume, hf, ↓reduceIte] using And.intro hh hp

theorem segment_then_completed (first : Segment program firstFuel pre middle)
    (second : Completed program secondFuel middle post) :
    Completed program (firstFuel + secondFuel) pre post := by
  intro s hs
  obtain ⟨hf, hm⟩ := first s hs
  obtain ⟨hh, hp⟩ := second _ hm
  rw [run_add]
  simpa only [resume, hf, ↓reduceIte] using And.intro hh hp

theorem segment_then_total (first : Segment program firstFuel pre middle)
    (second : TotalCorrect program middle post) : TotalCorrect program pre post := by
  intro s hs
  obtain ⟨hf, hm⟩ := first s hs
  obtain ⟨secondFuel, hh, hp⟩ := second _ hm
  refine ⟨firstFuel + secondFuel, ?_⟩
  rw [run_add]
  simpa only [resume, hf, ↓reduceIte] using And.intro hh hp

theorem completed_total (h : Completed program fuel pre post) :
    TotalCorrect program pre post := fun s hs => ⟨fuel, h s hs⟩

/-- A trace records a write to a word only when an actual executed store emits it. -/
def StoresTo (event : Occurrence) (index : Nat) : Prop :=
  ∃ effect, event.memory = some effect ∧ effect.kind = .store ∧ effect.address.toNat / 4 = index

def TraceAvoids (trace : List Occurrence) (index : Nat) : Prop :=
  ∀ event ∈ trace, ¬StoresTo event index

theorem eval_frame (hstep : eval override instruction s = .next next event)
    (untouched : ¬StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hguard : guard.eval s <;>
      simp only [eval, hguard, ↓reduceIte] at hstep
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj hstep; rfl)
      | contradiction
      | skip
    all_goals
      split at hstep
      · contradiction
      · obtain ⟨rfl, rfl⟩ := StepResult.next.inj hstep
        first
        | rfl
        | apply List.getElem?_set_ne
          intro equal
          apply untouched
          refine ⟨_,rfl,rfl,?_⟩
          have address := addressIndex_ok_iff.mp (by assumption)
          exact address.2.symm.trans equal

theorem step_frame (hstep : stepWith override program s = .next next event)
    (untouched : ¬StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  unfold stepWith at hstep
  split at hstep
  · contradiction
  · exact eval_frame hstep untouched

/-- Outside actual emitted stores, all words are preserved, including on fault,
unsupported, exhausted, and candidate-read executions. No final-memory premise. -/
theorem runWith_frame (fuel : Nat) (oracle : Nat → Option Word) (program : List Instr)
    (s : State) (index : Nat)
    (untouched : TraceAvoids (runWith fuel oracle program s).trace index) :
    (runWith fuel oracle program s).state.memory[index]? = s.memory[index]? := by
  induction fuel generalizing oracle s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : stepWith (oracle 0) program s with
    | next next emitted =>
      simp only [runWith, hs] at untouched ⊢
      have head := untouched emitted (by simp)
      have tail : TraceAvoids (runWith fuel (fun i => oracle (i + 1)) program next).trace index :=
        fun event member => untouched event (by simp [member])
      exact (ih _ _ tail).trans (step_frame hs head)
    | halted final emitted =>
      simp only [runWith, hs]
      rw [(step_halted hs).1]
    | fault reason => simp [runWith, hs]
    | unsupported spelling => simp [runWith, hs]

theorem run_frame (fuel : Nat) (program : List Instr) (s : State) (index : Nat)
    (untouched : TraceAvoids (run fuel program s).trace index) :
    (run fuel program s).state.memory[index]? = s.memory[index]? :=
  runWith_frame fuel (fun _ => none) program s index untouched

/-- A one-step invariant lifts to every finite prefix. Terminal faults leave the
state unchanged, and explicit exit also leaves its incoming state unchanged. -/
theorem runWith_invariant (invariant : Assertion)
    (preserved : ∀ override s next event, invariant s →
      stepWith override program s = .next next event → invariant next)
    (fuel : Nat) (oracle : Nat → Option Word) (s : State) (initial : invariant s) :
    invariant (runWith fuel oracle program s).state := by
  induction fuel generalizing oracle s with
  | zero => exact initial
  | succ fuel ih =>
    cases hs : stepWith (oracle 0) program s with
    | next next emitted =>
      simp only [runWith, hs]
      exact ih _ _ (preserved _ _ _ _ initial hs)
    | halted final emitted =>
      simp only [runWith, hs]
      rw [(step_halted hs).1]
      exact initial
    | fault reason => simpa [runWith, hs] using initial
    | unsupported spelling => simpa [runWith, hs] using initial

/-- Invariant preservation and the exit case establish partial correctness.
No progress or decreasing-measure premise is required, so divergence remains possible. -/
theorem partial_of_invariant (program : List Instr) (pre invariant post : Assertion)
    (initial : ∀ s, pre s → invariant s)
    (preserved : ∀ s next event, invariant s →
      step program s = .next next event → invariant next)
    (exitPost : ∀ s final event, invariant s →
      step program s = .halted final event → post final) :
    PartialCorrect program pre post := by
  have aux : ∀ fuel s, invariant s → (run fuel program s).status = .halted →
      post (run fuel program s).state := by
    intro fuel
    induction fuel with
    | zero => intro s hs halted; simp [run_zero] at halted
    | succ fuel ih =>
      intro s hs halted
      rw [run_succ] at halted ⊢
      cases stepEq : step program s with
      | next next event =>
        simp only [stepEq] at halted ⊢
        exact ih next (preserved s next event hs stepEq) halted
      | halted final event =>
        exact exitPost s final event hs stepEq
      | fault reason => simp [stepEq] at halted
      | unsupported spelling => simp [stepEq] at halted
  exact fun s hs fuel halted => aux fuel s (initial s hs) halted

/-- A decreasing natural measure and a local progress obligation establish
termination. The progress premise excludes faults/unsupported outcomes without
assuming any completed run; it may be discharged instruction by instruction. -/
theorem terminates_of_decreasing_measure (program : List Instr) (invariant post : Assertion)
    (measure : State → Nat)
    (progress : ∀ s, invariant s →
      (∃ final event, step program s = .halted final event ∧ post final) ∨
      (∃ next event, step program s = .next next event ∧ invariant next ∧
        measure next < measure s)) :
    TotalCorrect program invariant post := by
  have terminate : ∀ rank, ∀ s, measure s = rank → invariant s →
      ∃ fuel, (run fuel program s).status = .halted ∧ post (run fuel program s).state := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro s rankEq initial
      rcases progress s initial with ⟨final,event,hs,hpost⟩ | ⟨next,event,hs,hnext,less⟩
      · exact ⟨1, by simp [run_succ, hs, hpost]⟩
      · obtain ⟨fuel,hh,hp⟩ := ih (measure next) (by omega) next rfl hnext
        exact ⟨fuel + 1, by simpa only [run_succ, hs] using And.intro hh hp⟩
  exact fun s initial => terminate (measure s) s rfl initial

end Ptx.Scalar.Rules
