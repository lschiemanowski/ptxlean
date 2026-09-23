import PtxBinary32Error

/-! Four actual rounded operations: affine, then square using the affine kernel
again with a positive-zero bias. All range guards depend on initial real inputs.
This module proves arithmetic composition, not memory handoff or launch visibility. -/
namespace Ptx.Binary32.SquareError

open TorchLean.Floats (eps32)
open TorchLean.Floats.IEEE754.IEEE32Exec (fp32Round)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

noncomputable def roundedAffine (xh wh bh : ℝ) : ℝ :=
  fp32Round (fp32Round (xh*wh) + bh)

/-- The same actual intermediate word is consumed twice by the second kernel. -/
def Results (left weight bias product intermediate square output : Word) : Prop :=
  Error.AffineResults left weight bias product intermediate ∧
    Error.AffineResults intermediate intermediate 0 square output

noncomputable def budget (xh wh bh x w b ex ew eb : ℝ) : ℝ :=
  let r := roundedAffine xh wh bh
  let a := x*w+b
  let e := Error.affineBudget xh wh bh x w ex ew eb
  Error.affineBudget r r 0 a a e e 0

theorem zero_real : finiteReal (0 : Word) = some 0 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.posZero FloatFormat.binary32)) = some 0
  rw [Model.toReal_posZero _ (by decide)]

/-- The exact rounded intermediate follows from the actual result relation and
input guards; it is not supplied as an intermediate-value premise. -/
theorem affine_value (left weight bias product intermediate : Word) (xh wh bh : ℝ)
    (leftReal : finiteReal left = some xh) (weightReal : finiteReal weight = some wh)
    (biasReal : finiteReal bias = some bh)
    (multiplyRange : |xh*wh| ≤ Bounds.maxFinite)
    (additionRange : |xh*wh| + eps32 (xh*wh) + |bh| ≤ Bounds.maxFinite)
    (allowed : Error.AffineResults left weight bias product intermediate) :
    finiteReal intermediate = some (roundedAffine xh wh bh) := by
  have productReal := Bounds.round_of_range .mul left weight product xh wh
    leftReal weightReal multiplyRange allowed.1
  exact Bounds.round_of_range .add product bias intermediate (fp32Round (xh*wh)) bh
    productReal biasReal (Error.rounded_add_range (xh*wh) bh additionRange) allowed.2

/-- This displays every rounding contribution and the quadratic propagated error. -/
theorem budget_expansion (xh wh bh x w b ex ew eb : ℝ) :
    let r := roundedAffine xh wh bh
    let a := x*w+b
    let e := Error.affineBudget xh wh bh x w ex ew eb
    budget xh wh bh x w b ex ew eb =
      eps32 (fp32Round (r*r)) + eps32 (r*r) + 2*|a| *e + e*e := by
  dsimp only
  unfold budget Error.affineBudget
  simp only [add_zero, abs_zero, zero_mul, mul_zero]
  ring

/-- Universal accuracy for all four admitted numerical results. The second range
conditions refer to the explicit rounded expression in initial real inputs. -/
theorem results_error (left weight bias product intermediate square output : Word)
    (xh wh bh x w b ex ew eb : ℝ)
    (leftReal : finiteReal left = some xh) (weightReal : finiteReal weight = some wh)
    (biasReal : finiteReal bias = some bh)
    (multiplyRange : |xh*wh| ≤ Bounds.maxFinite)
    (additionRange : |xh*wh| + eps32 (xh*wh) + |bh| ≤ Bounds.maxFinite)
    (squareRange : |roundedAffine xh wh bh * roundedAffine xh wh bh| ≤ Bounds.maxFinite)
    (finalRange : |roundedAffine xh wh bh * roundedAffine xh wh bh| +
      eps32 (roundedAffine xh wh bh * roundedAffine xh wh bh) ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (weightError : |wh-w| ≤ ew) (biasError : |bh-b| ≤ eb)
    (allowed : Results left weight bias product intermediate square output) :
    isFinite intermediate = true ∧ isFinite output = true ∧
      ∃ z, finiteReal output = some z ∧
        |z-(x*w+b)^2| ≤ budget xh wh bh x w b ex ew eb := by
  have intermediateReal := affine_value left weight bias product intermediate xh wh bh
    leftReal weightReal biasReal multiplyRange additionRange allowed.1
  obtain ⟨_, intermediateFinite, value, valueReal, valueError⟩ :=
    Error.affine_results left weight bias product intermediate xh wh bh x w b ex ew eb
      leftReal weightReal biasReal multiplyRange additionRange leftError weightError biasError allowed.1
  have valueEq : value = roundedAffine xh wh bh :=
    Option.some.inj (valueReal.symm.trans intermediateReal)
  subst value
  obtain ⟨_, outputFinite, z, real, error⟩ := Error.affine_results
    intermediate intermediate 0 square output
    (roundedAffine xh wh bh) (roundedAffine xh wh bh) 0 (x*w+b) (x*w+b) 0
    (Error.affineBudget xh wh bh x w ex ew eb) (Error.affineBudget xh wh bh x w ex ew eb) 0
    intermediateReal intermediateReal zero_real squareRange
    (by simpa using finalRange) valueError valueError (by simp) allowed.2
  exact ⟨intermediateFinite, outputFinite, z, real, by simpa [budget, pow_two] using error⟩

/-- Nonempty four-operation semantics for every bit pattern, independent of any
finite-range promise. This does not establish hardware NaN realizability. -/
theorem results_exists (left weight bias : Word) :
    ∃ product intermediate square output, Results left weight bias product intermediate square output := by
  obtain ⟨product, mul⟩ := Ptx.Binary32.results_exists .mul left weight
  obtain ⟨intermediate, add⟩ := Ptx.Binary32.results_exists .add product bias
  obtain ⟨square, sq⟩ := Ptx.Binary32.results_exists .mul intermediate intermediate
  obtain ⟨output, zeroAdd⟩ := Ptx.Binary32.results_exists .add square 0
  exact ⟨product, intermediate, square, output, ⟨mul, add⟩, sq, zeroAdd⟩

end Ptx.Binary32.SquareError
