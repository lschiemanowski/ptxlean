import PtxBinary32.Reduction
import PtxBinary32.Relu

/-! Arithmetic contracts for a reduced row followed by bias and ReLU. These
remain arithmetic facts until connected to fetched instructions and memory. -/
namespace Ptx.Binary32.Reduction
open TorchLean.Floats (eps32)
open TorchLean.Floats.IEEE754.IEEE32Exec (fp32Round)

structure RowInput where
  tree : Tree DotError.Input
  safe : Safe tree
  bias : Word
  bh : ℝ
  b : ℝ
  eb : ℝ
  biasReal : finiteReal bias = some bh
  biasError : |bh-b| ≤ eb
  additionRange : |rounded tree+bh| ≤ Bounds.maxFinite

noncomputable def RowInput.affine (i : RowInput) : ℝ := fp32Round (rounded i.tree+i.bh)
noncomputable def RowInput.idealAffine (i : RowInput) : ℝ := ideal i.tree+i.b
noncomputable def RowInput.error (i : RowInput) : ℝ := eps32 (rounded i.tree+i.bh)+budget i.tree+i.eb

/-- Keep the intermediate word and addition choice explicit. -/
def RowEval (i : RowInput) (a : Word) : Prop :=
  ∃ dot, Eval (words i.tree) dot ∧ Results .add dot i.bias a

theorem row_eval_exists (i : RowInput) : ∃ a, RowEval i a := by
  obtain ⟨dot,hd⟩ := eval_exists (words i.tree)
  obtain ⟨a,ha⟩ := results_exists .add dot i.bias
  exact ⟨a,dot,hd,ha⟩

theorem row_affine_accuracy (i : RowInput) (allowed : RowEval i a) :
    finiteReal a = some i.affine ∧ |i.affine-i.idealAffine| ≤ i.error := by
  obtain ⟨dot,hd,ha⟩ := allowed
  obtain ⟨value,error⟩ := accuracy i.tree i.safe hd
  have roundedValue := Bounds.round_of_range .add dot i.bias a (rounded i.tree) i.bh
    value i.biasReal i.additionRange ha
  obtain ⟨_,z,hz,bound⟩ := Error.add_results dot i.bias a (rounded i.tree) i.bh
    (ideal i.tree) i.b (budget i.tree) i.eb value i.biasReal i.additionRange error i.biasError ha
  have eq : z = i.affine := Option.some.inj (hz.symm.trans roundedValue)
  exact ⟨roundedValue,by simpa [eq,RowInput.idealAffine,RowInput.error] using bound⟩

theorem row_forward_accuracy (i : RowInput) (allowed : RowEval i a) :
    finiteReal (Relu.forward a) = some (max i.affine 0) ∧
      |max i.affine 0-max i.idealAffine 0| ≤ i.error := by
  obtain ⟨value,error⟩ := row_affine_accuracy i allowed
  exact ⟨Relu.forward_real _ _ value,Relu.forward_error _ _ _ error⟩

/-- A strict initial-input error margin preserves the backward branch. Only the
incoming sensitivity's error remains at the gate, with no extra rounding. -/
theorem row_gate_accuracy (i : RowInput) (allowed : RowEval i a)
    (seed : finiteReal d = some dh) (seedError : |dh-dIdeal| ≤ ed)
    (margin : i.error < |i.idealAffine|) :
    finiteReal (Relu.gate a d) = some (if 0 < i.affine then dh else 0) ∧
      |(if 0 < i.affine then dh else 0)-(if 0 < i.idealAffine then dIdeal else 0)| ≤ ed ∧
      i.idealAffine ≠ 0 := by
  obtain ⟨value,error⟩ := row_affine_accuracy i allowed
  have stable := Relu.sign_stable _ _ _ error margin
  have nonnegative : 0 ≤ ed := (abs_nonneg _).trans seedError
  refine ⟨Relu.gate_real _ _ _ _ value seed,?_,?_⟩
  · by_cases active : 0 < i.idealAffine <;> simp [stable,active,seedError,nonnegative]
  · intro zero
    have nonnegativeError := (abs_nonneg _).trans error
    rw [zero,abs_zero] at margin
    linarith

end Ptx.Binary32.Reduction
