import PtxBinary32.ShiftedExp
import PtxBinary32.Instructions
import PtxBinary32.ExponentialInstruction

/-! Four fetched instructions for one shifted exponential. This reuses the
existing add/mul/ex2 leaves; it neither introduces sub.rn.f32 semantics nor
asserts a parallel kernel execution. The caller supplies the upper bound. -/
namespace Ptx.Scalar.ShiftedExp

inductive Instr where
  | binary (instruction : Scalar.Binary32.Instr)
  | exponential (instruction : Scalar.Exponential.Instr)
  deriving DecidableEq, Repr

inductive Event where
  | binary (event : Scalar.Binary32.Occurrence)
  | exponential (event : Scalar.Exponential.Occurrence)
  deriving DecidableEq, Repr

inductive Eval : Instr → Scalar.State → Scalar.State → Event → Prop
  | binary {i s t e} (step : Scalar.Binary32.Eval i s t e) :
      Eval (.binary i) s t (.binary e)
  | exponential {i s t e} (step : Scalar.Exponential.Eval i s t e) :
      Eval (.exponential i) s t (.exponential e)

/-- A genuine fetch from the shared mixed instruction list. -/
def Step (target : Ptx.Target) (program : List Instr)
    (s t : Scalar.State) (event : Event) : Prop :=
  Scalar.Binary32.SupportedTarget target ∧
    ∃ i, program[s.pc]? = some i ∧ Eval i s t event

/-- Exactly four actual steps; intermediate states and events are existential. -/
def Run (target : Ptx.Target) (program : List Instr) (s t : Scalar.State) : Prop :=
  ∃ s₁ s₂ s₃ e₀ e₁ e₂ e₃,
    Step target program s s₁ e₀ ∧ Step target program s₁ s₂ e₁ ∧
    Step target program s₂ s₃ e₂ ∧ Step target program s₃ t e₃

def negate (maximum destination : Nat) : Scalar.Binary32.Instr :=
  ⟨.always, .mul, destination, .reg maximum, .imm 0xbf800000⟩
def shift (input destination : Nat) : Scalar.Binary32.Instr :=
  ⟨.always, .add, destination, .reg input, .reg destination⟩
def convert (destination : Nat) : Scalar.Binary32.Instr :=
  ⟨.always, .mul, destination, .reg destination, .imm Ptx.Binary32.ExpArgument.constantWord⟩
def exponential (destination : Nat) : Scalar.Exponential.Instr :=
  ⟨.always, destination, .reg destination⟩

def program (input maximum destination : Nat) : List Instr :=
  [.binary (negate maximum destination), .binary (shift input destination),
   .binary (convert destination), .exponential (exponential destination)]

/-- Exact typed PTX statements, with decoded binary32 immediate words. -/
def text (input maximum destination : Nat) : List Scalar.Text.Statement :=
  [Scalar.Binary32.Text.encode (negate maximum destination),
   Scalar.Binary32.Text.encode (shift input destination),
   Scalar.Binary32.Text.encode (convert destination),
   Scalar.Exponential.Text.encode (exponential destination)]

private theorem binary_of_step {target p s t e i}
    (fetch : p[s.pc]? = some (.binary i)) (step : Step target p s t e) :
    ∃ event, Scalar.Binary32.Eval i s t event := by
  rcases step with ⟨_,j,hj,he⟩
  have same : j = .binary i := Option.some.inj (hj.symm.trans fetch)
  subst j
  cases he with | binary h => exact ⟨_,h⟩

private theorem exponential_of_step {target p s t e i}
    (fetch : p[s.pc]? = some (.exponential i)) (step : Step target p s t e) :
    ∃ event, Scalar.Exponential.Eval i s t event := by
  rcases step with ⟨_,j,hj,he⟩
  have same : j = .exponential i := Option.some.inj (hj.symm.trans fetch)
  subst j
  cases he with | exponential h => exact ⟨_,h⟩

/-- Every execution binds the numerical stages to the actual stored operands
and final destination. The scratch register may alias the maximum. -/
theorem run_results (target : Ptx.Target) (s t : Scalar.State)
    (input maximum destination : Nat) (start : s.pc = 0)
    (scratch : destination ≠ input)
    (run : Run target (program input maximum destination) s t) :
    (∃ negative shifted product,
      Ptx.Binary32.Results .mul (s.regs maximum) 0xbf800000 negative ∧
      Ptx.Binary32.Results .add (s.regs input) negative shifted ∧
      Ptx.Binary32.Results .mul shifted Ptx.Binary32.ExpArgument.constantWord product ∧
      Ptx.Binary32.Exponential.Results product (t.regs destination)) ∧
    t.pc = 4 ∧ t.memory = s.memory ∧ t.addrs = s.addrs ∧ t.preds = s.preds ∧
    (∀ other, other ≠ destination → t.regs other = s.regs other) := by
  rcases run with ⟨s₁,s₂,s₃,e₀,e₁,e₂,e₃,h₀,h₁,h₂,h₃⟩
  obtain ⟨a₀,b₀⟩ := binary_of_step (i := negate maximum destination) (by simp [program,start]) h₀
  have f₀ := Scalar.Binary32.eval_frame _ _ _ _ b₀
  have pc₁ : s₁.pc = 1 := by omega
  obtain ⟨a₁,b₁⟩ := binary_of_step (i := shift input destination) (by simp [program,pc₁]) h₁
  have f₁ := Scalar.Binary32.eval_frame _ _ _ _ b₁
  have pc₂ : s₂.pc = 2 := by omega
  obtain ⟨a₂,b₂⟩ := binary_of_step (i := convert destination) (by simp [program,pc₂]) h₂
  have f₂ := Scalar.Binary32.eval_frame _ _ _ _ b₂
  have pc₃ : s₃.pc = 3 := by omega
  obtain ⟨a₃,b₃⟩ := exponential_of_step (i := exponential destination) (by simp [program,pc₃]) h₃
  have f₃ := Scalar.Exponential.eval_frame _ _ _ _ b₃
  have r₀ := Scalar.Binary32.eval_destination _ _ _ _ b₀ (by rfl)
  have r₁ := Scalar.Binary32.eval_destination _ _ _ _ b₁ (by rfl)
  have r₂ := Scalar.Binary32.eval_destination _ _ _ _ b₂ (by rfl)
  have r₃ := Scalar.Exponential.eval_destination _ _ _ _ b₃ (by rfl)
  have saved : s₁.regs input = s.regs input :=
    Scalar.Binary32.eval_other _ _ _ _ input b₀ (Ne.symm scratch)
  simp only [negate,shift,convert,exponential,Scalar.Operand32.eval] at r₀ r₁ r₂ r₃
  rw [saved] at r₁
  refine ⟨⟨s₁.regs destination,s₂.regs destination,s₃.regs destination,r₀,r₁,r₂,r₃⟩,
    by omega, f₃.2.1.trans (f₂.2.1.trans (f₁.2.1.trans f₀.2.1)),
    f₃.2.2.1.trans (f₂.2.2.1.trans (f₁.2.2.1.trans f₀.2.2.1)),
    f₃.2.2.2.trans (f₂.2.2.2.trans (f₁.2.2.2.trans f₀.2.2.2)), ?_⟩
  intro other different
  exact (Scalar.Exponential.eval_other _ _ _ _ other b₃ different).trans
    ((Scalar.Binary32.eval_other _ _ _ _ other b₂ different).trans
      ((Scalar.Binary32.eval_other _ _ _ _ other b₁ different).trans
        (Scalar.Binary32.eval_other _ _ _ _ other b₀ different)))

/-- An all-execution bound, with intermediate finiteness and errors derived
from the original encoded inputs. -/
theorem correct (target : Ptx.Target) (s t : Scalar.State)
    (input maximum destination : Nat) (x m : ℝ)
    (start : s.pc = 0) (scratch : destination ≠ input)
    (inputValue : Ptx.Binary32.finiteReal (s.regs input) = some x)
    (maximumValue : Ptx.Binary32.finiteReal (s.regs maximum) = some m)
    (bounds : Ptx.Binary32.ShiftedExp.InputBounds x m)
    (run : Run target (program input maximum destination) s t) :
    ∃ u, Ptx.Binary32.finiteReal (t.regs destination) = some u ∧
      |u-Real.exp (x-m)| ≤ 5/(2:ℝ)^24 + Real.log 2 *
        Ptx.Binary32.ExpArgument.budget (TorchLean.Floats.round32 (x-m))
          (TorchLean.Floats.eps32 (x-m)) := by
  obtain ⟨⟨negative,shifted,product,r₀,r₁,r₂,r₃⟩,_⟩ :=
    run_results target s t input maximum destination start scratch run
  exact Ptx.Binary32.ShiftedExp.error _ _ negative shifted product _ x m
    inputValue maximumValue bounds r₀ r₁ r₂ r₃

/-- An entry attaining the supplied maximum produces exactly encoded +1,
even when its input words use different zero signs. -/
theorem maximal_score (target : Ptx.Target) (s t : Scalar.State)
    (input maximum destination : Nat) (m : ℝ)
    (start : s.pc = 0) (scratch : destination ≠ input)
    (inputValue : Ptx.Binary32.finiteReal (s.regs input) = some m)
    (maximumValue : Ptx.Binary32.finiteReal (s.regs maximum) = some m)
    (small : |m| ≤ (2:ℝ)^(124:ℤ))
    (run : Run target (program input maximum destination) s t) :
    t.regs destination = 0x3f800000 := by
  obtain ⟨⟨negative,shifted,product,r₀,r₁,r₂,r₃⟩,_⟩ :=
    run_results target s t input maximum destination start scratch run
  exact Ptx.Binary32.ShiftedExp.equal_scores _ _ negative shifted product _ m
    inputValue maximumValue small r₀ r₁ r₂ r₃

private def write (s : Scalar.State) (destination : Nat) (value : Word) : Scalar.State :=
  {s with pc := s.pc+1, regs := Scalar.update s.regs destination value}

/-- Existence is constructed from input-only bounds, not an assumed successful
exponential or caller-supplied intermediate states. -/
theorem execution_exists (target : Ptx.Target) (s : Scalar.State)
    (input maximum destination : Nat) (x m : ℝ)
    (supported : Scalar.Binary32.SupportedTarget target)
    (start : s.pc = 0) (scratch : destination ≠ input)
    (inputValue : Ptx.Binary32.finiteReal (s.regs input) = some x)
    (maximumValue : Ptx.Binary32.finiteReal (s.regs maximum) = some m)
    (bounds : Ptx.Binary32.ShiftedExp.InputBounds x m) :
    ∃ t, Run target (program input maximum destination) s t := by
  obtain ⟨n,z,a,u,r₀,r₁,r₂,r₃⟩ := Ptx.Binary32.ShiftedExp.stages_exist
    (s.regs input) (s.regs maximum) x m inputValue maximumValue bounds
  let s₁ := write s destination n
  let s₂ := write s₁ destination z
  let s₃ := write s₂ destination a
  let t := write s₃ destination u
  have b₀ : Scalar.Binary32.Eval (negate maximum destination) s s₁
      (Scalar.Binary32.occurrence s (negate maximum destination) true) :=
    .executed rfl r₀
  have b₁ : Scalar.Binary32.Eval (shift input destination) s₁ s₂
      (Scalar.Binary32.occurrence s₁ (shift input destination) true) := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [s₁,write,shift,Scalar.Operand32.eval,Scalar.update,Ne.symm scratch] using r₁
  have b₂ : Scalar.Binary32.Eval (convert destination) s₂ s₃
      (Scalar.Binary32.occurrence s₂ (convert destination) true) := by
    apply Scalar.Binary32.Eval.executed rfl
    simpa [s₂,write,convert,Scalar.Operand32.eval,Scalar.update] using r₂
  have b₃ : Scalar.Exponential.Eval (exponential destination) s₃ t
      (Scalar.Exponential.occurrence s₃ (exponential destination) true) := by
    apply Scalar.Exponential.Eval.executed rfl
    simpa [s₃,write,exponential,Scalar.Operand32.eval,Scalar.update] using r₃
  refine ⟨t,s₁,s₂,s₃,_,_,_,_,⟨supported,_,?_,.binary b₀⟩,
    ⟨supported,_,?_,.binary b₁⟩,⟨supported,_,?_,.binary b₂⟩,
    ⟨supported,_,?_,.exponential b₃⟩⟩ <;>
    simp [program,s₁,s₂,s₃,write,start]

end Ptx.Scalar.ShiftedExp
