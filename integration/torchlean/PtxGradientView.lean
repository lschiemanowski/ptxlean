import PtxBinary32
import PtxAffineSquareVJP

/-! An observation interface for three stored gradients. The caller supplies the
actual codewords; allocation selection, execution and numerical error proofs are
separate obligations. Nonfinite encodings have no real-tensor interpretation. -/
namespace Ptx.GradientView
open Spec TorchLean
open Ptx.Binary32
open PtxTorchLean.AffineSquareVJP
noncomputable section

abbrev Triple := TensorPack ℝ [Shape.scalar, Shape.scalar, Shape.scalar]

/-- Exact encoded observations, in input, weight and bias sensitivity order. -/
structure Words where
  dx : Word
  dw : Word
  db : Word
  deriving DecidableEq, Repr

/-- Decode every component or reject the whole observation. -/
def decode (words : Words) : Option Triple := do
  let x ← finiteReal words.dx
  let w ← finiteReal words.dw
  let b ← finiteReal words.db
  pure (inputs x w b)

/-- Logical scalar coordinates of an arbitrary actual TorchLean pack. -/
def component (values : Triple) : Fin 3 → ℝ :=
  ![Tensor.item values.head, Tensor.item values.tail.head,
    Tensor.item values.tail.tail.head]

def Componentwise (observed reference : Triple) (ex ew eb : ℝ) : Prop :=
  ∀ i : Fin 3, |component observed i - component reference i| ≤ ![ex, ew, eb] i

/-- Approximation includes successful finite decoding; no default tensor exists. -/
def Approximates (words : Words) (reference : Triple) (ex ew eb : ℝ) : Prop :=
  ∃ observed, decode words = some observed ∧ Componentwise observed reference ex ew eb

@[simp] theorem component_inputs (x w b : ℝ) :
    component (inputs x w b) = ![x, w, b] := rfl

theorem componentwise_iff (observed reference : Triple) (ex ew eb : ℝ) :
    Componentwise observed reference ex ew eb ↔
      |component observed 0 - component reference 0| ≤ ex ∧
      |component observed 1 - component reference 1| ≤ ew ∧
      |component observed 2 - component reference 2| ≤ eb := by
  simp [Componentwise, Fin.forall_fin_succ]

theorem componentwise_inputs_iff (x w b : ℝ) (reference : Triple) (ex ew eb : ℝ) :
    Componentwise (inputs x w b) reference ex ew eb ↔
      |x - component reference 0| ≤ ex ∧ |w - component reference 1| ≤ ew ∧
      |b - component reference 2| ≤ eb := by
  simp [componentwise_iff]

theorem decode_of_finite (words : Words) (x w b : ℝ)
    (hx : finiteReal words.dx = some x) (hw : finiteReal words.dw = some w)
    (hb : finiteReal words.db = some b) :
    decode words = some (inputs x w b) := by simp [decode, hx, hw, hb]

theorem decode_some_iff (words : Words) (observed : Triple) :
    decode words = some observed ↔ ∃ x w b : ℝ,
      finiteReal words.dx = some x ∧ finiteReal words.dw = some w ∧
      finiteReal words.db = some b ∧ observed = inputs x w b := by
  cases hx : finiteReal words.dx <;> cases hw : finiteReal words.dw <;>
    cases hb : finiteReal words.db <;> simp [decode, hx, hw, hb, eq_comm]

theorem decode_none_iff (words : Words) :
    decode words = none ↔ finiteReal words.dx = none ∨
      finiteReal words.dw = none ∨ finiteReal words.db = none := by
  simp only [decode]
  cases hx : finiteReal words.dx <;> cases hw : finiteReal words.dw <;>
    cases hb : finiteReal words.db <;> simp

theorem nonfinite_rejected (words : Words)
    (bad : isFinite words.dx = false ∨ isFinite words.dw = false ∨
      isFinite words.db = false) : decode words = none := by
  apply (decode_none_iff words).mpr
  rcases bad with h | h | h
  · exact Or.inl (finiteReal_none _ h)
  · exact Or.inr (Or.inl (finiteReal_none _ h))
  · exact Or.inr (Or.inr (finiteReal_none _ h))

/-- A nonfinite selected word cannot satisfy an approximation claim. -/
theorem not_approximates_of_nonfinite (words : Words) (reference : Triple) (ex ew eb : ℝ)
    (bad : isFinite words.dx = false ∨ isFinite words.dw = false ∨
      isFinite words.db = false) : ¬ Approximates words reference ex ew eb := by
  simp [Approximates, nonfinite_rejected words bad]

theorem approximates_iff (words : Words) (x w b : ℝ) (reference : Triple)
    (ex ew eb : ℝ) (hx : finiteReal words.dx = some x)
    (hw : finiteReal words.dw = some w) (hb : finiteReal words.db = some b) :
    Approximates words reference ex ew eb ↔
      |x - component reference 0| ≤ ex ∧ |w - component reference 1| ≤ ew ∧
      |b - component reference 2| ≤ eb := by
  simp [Approximates, decode_of_finite words x w b hx hw hb, componentwise_inputs_iff]

/-- Specialization to the actual generated reverse result, not a replacement AD. -/
theorem generated_iff (words : Words) (rx rw rb x w b d ex ew eb : ℝ)
    (hx : finiteReal words.dx = some rx) (hw : finiteReal words.dw = some rw)
    (hb : finiteReal words.db = some rb) :
    Approximates words (graph.vjpWithSeed (inputs x w b) (Tensor.scalar d)) ex ew eb ↔
      |rx - 2*d*(x*w+b)*w| ≤ ex ∧ |rw - 2*d*(x*w+b)*x| ≤ ew ∧
      |rb - 2*d*(x*w+b)| ≤ eb := by
  rw [generated_vjp, approximates_iff words rx rw rb _ ex ew eb hx hw hb]
  simp [sensitivities]

/-- Consumer endpoint: local decoded-value bounds imply approximation of the
actual generated result, and the actual checked call succeeds. -/
theorem generated_of_bounds_checked (words : Words) (rx rw rb x w b d ex ew eb : ℝ)
    (hx : finiteReal words.dx = some rx) (hw : finiteReal words.dw = some rw)
    (hb : finiteReal words.db = some rb)
    (bx : |rx - 2*d*(x*w+b)*w| ≤ ex) (bw : |rw - 2*d*(x*w+b)*x| ≤ ew)
    (bb : |rb - 2*d*(x*w+b)| ≤ eb) :
    Approximates words (graph.vjpWithSeed (inputs x w b) (Tensor.scalar d)) ex ew eb ∧
    graph.vjpChecked (inputs x w b) () (Tensor.scalar d) =
      .ok (sensitivities x w b d, Tensor.scalar ((x*w+b)^2)) := by
  exact ⟨(generated_iff words rx rw rb x w b d ex ew eb hx hw hb).mpr ⟨bx, bw, bb⟩,
    checked_result x w b d⟩

/-- Different signed-zero codewords have the same real-tensor view. This is an
explicit counterexample to recovering codeword equality from real equality. -/
theorem signed_zero_same_view :
    (Words.mk 0 0 0) ≠ (Words.mk 0x80000000 0 0) ∧
    decode (Words.mk 0 0 0) = some (inputs 0 0 0) ∧
    decode (Words.mk 0x80000000 0 0) = some (inputs 0 0 0) := by
  have positive : finiteReal (0 : Word) = some 0 := by
    rw [finiteReal_some _ (by decide)]
    change some (FloatLib.Floats.Formats.BinaryInterchange.Model.toReal
      (FloatLib.Floats.Formats.BinaryInterchange.Model.posZero _)) = some 0
    rw [FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_posZero _ (by decide)]
  have negative : finiteReal (0x80000000 : Word) = some 0 := by
    rw [finiteReal_some _ (by decide)]
    change some (FloatLib.Floats.Formats.BinaryInterchange.Model.toReal
      (FloatLib.Floats.Formats.BinaryInterchange.Model.negZero _)) = some 0
    rw [FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_negZero _ (by decide)]
  exact ⟨by decide, decode_of_finite _ 0 0 0 positive positive positive,
    decode_of_finite _ 0 0 0 negative positive positive⟩

end
end Ptx.GradientView
