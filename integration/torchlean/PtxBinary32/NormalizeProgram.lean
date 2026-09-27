import PtxBinary32.Instructions
import PtxBinary32.ReciprocalInstruction

/-! Two fetched instructions implementing division as a rounded reciprocal
followed by a rounded product. This is not a single correctly rounded division:
the separate numerical contract must account for both rounding steps. -/
namespace Ptx.Scalar.Normalize

inductive Instr where
  | reciprocal (instruction : Scalar.Reciprocal.Instr)
  | binary (instruction : Scalar.Binary32.Instr)
  deriving DecidableEq, Repr

inductive Event where
  | reciprocal (event : Scalar.Reciprocal.Occurrence)
  | binary (event : Scalar.Binary32.Occurrence)
  deriving DecidableEq, Repr

inductive Eval : Instr → Scalar.State → Scalar.State → Event → Prop
  | reciprocal {i s t e} (step : Scalar.Reciprocal.Eval i s t e) :
      Eval (.reciprocal i) s t (.reciprocal e)
  | binary {i s t e} (step : Scalar.Binary32.Eval i s t e) :
      Eval (.binary i) s t (.binary e)

/-- Both existing leaves require PTX 9.4 and SM 2.0 or newer. -/
def Step (target : Ptx.Target) (program : List Instr)
    (s t : Scalar.State) (event : Event) : Prop :=
  Scalar.Binary32.SupportedTarget target ∧
    ∃ i, program[s.pc]? = some i ∧ Eval i s t event

/-- Two actual fetched steps, with an existential intermediate state. -/
def Run (target : Ptx.Target) (program : List Instr) (s t : Scalar.State) : Prop :=
  ∃ middle e₀ e₁,
    Step target program s middle e₀ ∧ Step target program middle t e₁

def reciprocal (denominator destination : Nat) : Scalar.Reciprocal.Instr :=
  ⟨.always, destination, .reg denominator⟩

def multiply (numerator destination : Nat) : Scalar.Binary32.Instr :=
  ⟨.always, .mul, destination, .reg numerator, .reg destination⟩

def program (numerator denominator destination : Nat) : List Instr :=
  [.reciprocal (reciprocal denominator destination), .binary (multiply numerator destination)]

/-- Typed PTX statements for the fetched instruction list. -/
def text (numerator denominator destination : Nat) : List Scalar.Text.Statement :=
  [Scalar.Reciprocal.Text.encode (reciprocal denominator destination),
   Scalar.Binary32.Text.encode (multiply numerator destination)]

private theorem reciprocal_of_step {target p s t e i}
    (fetch : p[s.pc]? = some (.reciprocal i)) (step : Step target p s t e) :
    ∃ event, Scalar.Reciprocal.Eval i s t event := by
  rcases step with ⟨_,j,hj,he⟩
  have same : j = .reciprocal i := Option.some.inj (hj.symm.trans fetch)
  subst j
  cases he with | reciprocal h => exact ⟨_,h⟩

private theorem binary_of_step {target p s t e i}
    (fetch : p[s.pc]? = some (.binary i)) (step : Step target p s t e) :
    ∃ event, Scalar.Binary32.Eval i s t event := by
  rcases step with ⟨_,j,hj,he⟩
  have same : j = .binary i := Option.some.inj (hj.symm.trans fetch)
  subst j
  cases he with | binary h => exact ⟨_,h⟩

/-- All executions use the original numerator and denominator. The destination
may overwrite the denominator, but must not overwrite the numerator early. -/
theorem run_results (target : Ptx.Target) (s t : Scalar.State)
    (numerator denominator destination : Nat) (start : s.pc = 0)
    (scratch : destination ≠ numerator)
    (run : Run target (program numerator denominator destination) s t) :
    (∃ inverse,
      Ptx.Binary32.Reciprocal.Results (s.regs denominator) inverse ∧
      Ptx.Binary32.Results .mul (s.regs numerator) inverse (t.regs destination)) ∧
    t.pc = 2 ∧ t.memory = s.memory ∧ t.addrs = s.addrs ∧ t.preds = s.preds ∧
    (∀ other, other ≠ destination → t.regs other = s.regs other) := by
  rcases run with ⟨middle,e₀,e₁,h₀,h₁⟩
  obtain ⟨a₀,b₀⟩ := reciprocal_of_step (i := reciprocal denominator destination)
    (by simp [program,start]) h₀
  have f₀ := Scalar.Reciprocal.eval_frame _ _ _ _ b₀
  have pc₁ : middle.pc = 1 := by omega
  obtain ⟨a₁,b₁⟩ := binary_of_step (i := multiply numerator destination)
    (by simp [program,pc₁]) h₁
  have f₁ := Scalar.Binary32.eval_frame _ _ _ _ b₁
  have r₀ := Scalar.Reciprocal.eval_destination _ _ _ _ b₀ (by rfl)
  have r₁ := Scalar.Binary32.eval_destination _ _ _ _ b₁ (by rfl)
  have saved : middle.regs numerator = s.regs numerator :=
    Scalar.Reciprocal.eval_other _ _ _ _ numerator b₀ (Ne.symm scratch)
  simp only [reciprocal,multiply,Scalar.Operand32.eval] at r₀ r₁
  rw [saved] at r₁
  refine ⟨⟨middle.regs destination,r₀,r₁⟩,by omega,
    f₁.2.1.trans f₀.2.1,f₁.2.2.1.trans f₀.2.2.1,
    f₁.2.2.2.trans f₀.2.2.2,?_⟩
  intro other different
  exact (Scalar.Binary32.eval_other _ _ _ _ other b₁ different).trans
    (Scalar.Reciprocal.eval_other _ _ _ _ other b₀ different)

private def write (s : Scalar.State) (destination : Nat) (value : Word) : Scalar.State :=
  {s with pc := s.pc+1, regs := Scalar.update s.regs destination value}

/-- Bit-level execution exists for every input word, including exceptional
values. Numerical finiteness and accuracy require separate hypotheses. -/
theorem execution_exists (target : Ptx.Target) (s : Scalar.State)
    (numerator denominator destination : Nat)
    (supported : Scalar.Binary32.SupportedTarget target)
    (start : s.pc = 0) (scratch : destination ≠ numerator) :
    ∃ t, Run target (program numerator denominator destination) s t := by
  obtain ⟨inverse,r₀⟩ := Ptx.Binary32.Reciprocal.results_exists (s.regs denominator)
  obtain ⟨value,r₁⟩ := Ptx.Binary32.results_exists .mul (s.regs numerator) inverse
  let middle := write s destination inverse
  let t := write middle destination value
  have b₀ : Scalar.Reciprocal.Eval (reciprocal denominator destination) s middle
      (Scalar.Reciprocal.occurrence s (reciprocal denominator destination) true) :=
    .executed rfl r₀
  have b₁ : Scalar.Binary32.Eval (multiply numerator destination) middle t
      (Scalar.Binary32.occurrence middle (multiply numerator destination) true) := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [middle,write,multiply,Scalar.Operand32.eval,Scalar.update,Ne.symm scratch] using r₁
  refine ⟨t,middle,_,_,⟨supported,_,?_,.reciprocal b₀⟩,
    ⟨supported,_,?_,.binary b₁⟩⟩ <;>
    simp [program,middle,write,start]

end Ptx.Scalar.Normalize
