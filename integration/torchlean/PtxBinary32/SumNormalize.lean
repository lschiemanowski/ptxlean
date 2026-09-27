import PtxBinary32.SumCorrect
import PtxBinary32.SoftmaxNormalize
import PtxBinary32.NormalizeProgram

/-! Explicit register-interface composition of the parallel sum and scalar
normalization components. The entry-state function copies the stored sum and
one original numerator into registers mathematically; it is not an implemented
PTX load, broadcast, launch or proof of combined softmax execution. -/
namespace Ptx.Scalar.Parallel.SumNormalize
open Ptx.Binary32
open Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section

/-- A separate scalar invocation starts with numerator in r0, the actual sum
word in r1, scratch r2 and entry PC zero. -/
def entry (numerator denominator : Word) : Scalar.State :=
  ⟨0,fun r => if r=0 then numerator else if r=1 then denominator else 0,
    fun _ => 0,fun _ => false,[]⟩

def program : List Scalar.Normalize.Instr := Scalar.Normalize.program 0 1 2

theorem run_stages (target : Ptx.Target) (numerator denominator : Word) (final : Scalar.State)
    (run : Scalar.Normalize.Run target program (entry numerator denominator) final) :
    Binary32.Normalize.Stages numerator denominator (final.regs 2) := by
  have result := Scalar.Normalize.run_results target (entry numerator denominator) final 0 1 2
    rfl (by decide) run
  simpa [entry,Binary32.Normalize.Stages] using result.1

/-- The two fetched scalar instructions exist for each explicit register handoff.
Their existence is separate from a parallel normalization-memory implementation. -/
theorem execution_exists (target : Ptx.Target) (numerator denominator : Word)
    (supported : Scalar.Binary32.SupportedTarget target) :
    ∃ final, Scalar.Normalize.Run target program (entry numerator denominator) final :=
  Scalar.Normalize.execution_exists target (entry numerator denominator) 0 1 2 supported rfl (by decide)

/-- A stored result from any completed admitted parallel sum supplies the
normalization denominator. Actual two-instruction scalar runs then satisfy the
softmax coordinate error contract through the stated register interface. -/
theorem completed_coordinate_accuracy (d : Nat) (bound : Sum.Bounds d)
    (input : Fin (Sum.width d) → Word) (values exact delta : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i)) (small : ∀i, |values i|≤2)
    (nonneg : ∀i, 0≤exact i) (upper : ∀i, exact i≤1) (lower : 1≤∑i,exact i)
    (exponential : ∀i, |values i-exact i|≤delta i)
    (budget : denominatorBudget delta (SumTree.budget d)≤1/2)
    (shared : List Word) (seeds : Fin (Sum.shape d).threads → Scalar.State)
    {events : List (Event (Sum.shape d).threads)} {sumFinal : State (Sum.shape d).threads}
    (sumRun : Runs (Sum.config d bound) (Sum.program d) (Sum.initial d input shared seeds) events sumFinal)
    (halted : ∀t, (sumFinal.lanes t).halted=true)
    (source co) (valid : Dense.Admitted (Sum.shape d) (Sum.denseBounds d bound)
      (Sum.global d input) shared seeds sumRun source co)
    (target : Ptx.Target) (normalized : Fin (Sum.width d) → Scalar.State)
    (runs : ∀i, Scalar.Normalize.Run target program
      (entry (input i) sumFinal.global[Sum.outputIndex d]!) (normalized i))
    (i : Fin (Sum.width d)) :
    ∃ y, finiteReal ((normalized i).regs 2)=some y ∧
      |y-exact i/(∑j,exact j)|≤coordinateBudget (delta i)
        (denominatorBudget delta (SumTree.budget d))
        (TorchLean.Floats.eps32 (1/Sum.rounded d values))
        (TorchLean.Floats.eps32 (values i*TorchLean.Floats.round32 (1/Sum.rounded d values))) := by
  obtain ⟨denominator,stored,sumValue,sumError⟩ :=
    Sum.completed_accuracy d bound input values finite small shared seeds sumRun halted source co valid
  have word : sumFinal.global[Sum.outputIndex d]! = denominator := by
    simp [List.getElem!_eq_getElem?_getD,stored]
  have stages : ∀j, Binary32.Normalize.Stages (input j) denominator ((normalized j).regs 2) := by
    intro j
    rw [← word]
    exact run_stages target _ _ _ (runs j)
  exact SoftmaxNormalize.coordinate_accuracy exact values delta (Sum.rounded d values)
    (SumTree.budget d) input (fun j => (normalized j).regs 2) denominator finite sumValue
    nonneg upper lower exponential sumError budget stages i

end
end Ptx.Scalar.Parallel.SumNormalize
