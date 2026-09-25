import PtxBinary32Error

/-! Finite binary32 ReLU and its backward gate, implemented using word tests.
Exceptional words still have a total bit-level result, without a real/NaN ReLU claim. -/
namespace Ptx.Binary32.Relu
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

/-- Strict positivity for finite binary32: exclude +0 and every sign-set word. -/
def positive (a : Word) : Bool := decide (0 < a.toNat ∧ a.toNat < 2147483648)
def gate (a payload : Word) : Word := if positive a then payload else 0
def forward (a : Word) : Word := gate a a

private theorem fields (a : Word) :
    positive a = ((!Model.signBit (Binary.toModel (decode a))) &&
      (!Model.isZero (Binary.toModel (decode a)))) := by
  have bits : (Binary.toModel (decode a)).bits = a := rfl
  have sign := Model.signBit_eq_false_iff_toNatBits_lt_signMaskNat (Binary.toModel (decode a))
  change (Model.signBit (Binary.toModel (decode a)) = false ↔ a.toNat < 2147483648) at sign
  apply Bool.eq_iff_iff.mpr
  simp only [positive, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', sign]
  simp only [Model.isZero, Model.IEEE.isZero, Model.expField, Model.fracField, bits]
  change (0 < a.toNat ∧ a.toNat < 2147483648) ↔
    (a.toNat < 2147483648 ∧
      (((a >>> 23) &&& 255).toNat == 0 && (a &&& 8388607).toNat == 0) = false)
  have mask8 : (255 : Word).toNat = 2^8-1 := rfl
  have mask23 : (8388607 : Word).toNat = 2^23-1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, mask8, mask23,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem positive_iff (a : Word) (x : ℝ) (real : finiteReal a = some x) :
    positive a = true ↔ 0 < x := by
  have finite : isFinite a = true := by
    have h := congrArg Option.isSome real
    simpa [finiteReal_isSome] using h
  have value : (Binary.toModel (decode a)).toReal = x :=
    Option.some.inj ((finiteReal_some a finite).symm.trans real)
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite (x := Binary.toModel (decode a)) finite
  have sign := Model.sign_eq_signBit_of_toDyadic?_some hd
  have zero := Model.isZero_eq_beq_zero_of_toDyadic?_some hd
  rw [fields, ← sign, zero]
  have dx : d.toReal = x := by simpa [Model.toReal_eq, hd] using value
  rw [← dx, FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.cast_signedSignificand]
  have powpos : 0 < (2 : ℝ) ^ d.exponent := zpow_pos (by norm_num) _
  cases hs : d.negative <;> simp [hs, mul_pos_iff, powpos, Nat.cast_pos, Nat.cast_nonneg]

@[simp] theorem zero_real : finiteReal 0 = some 0 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.posZero FloatFormat.binary32)) = some 0
  rw [Model.toReal_posZero _ (by decide)]

theorem gate_real (a payload : Word) (x d : ℝ)
    (real : finiteReal a = some x) (seed : finiteReal payload = some d) :
    finiteReal (gate a payload) = some (if 0 < x then d else 0) := by
  simp only [gate]
  by_cases h : 0 < x
  · simp [positive_iff a x real, h, seed]
  · simp only [positive_iff a x real, h, ite_false]
    exact zero_real

theorem forward_real (a : Word) (x : ℝ) (real : finiteReal a = some x) :
    finiteReal (forward a) = some (max x 0) := by
  rw [forward, gate_real a a x x real real]
  by_cases h : 0 < x
  · simp [h, max_eq_left (le_of_lt h)]
  · simp [h, max_eq_right (le_of_not_gt h)]

/-- ReLU does not enlarge absolute error, including across zero. -/
theorem forward_error (x a error : ℝ) (bound : |x-a| ≤ error) :
    |max x 0 - max a 0| ≤ error := by
  rcases le_total x 0 with hx | hx <;> rcases le_total a 0 with ha | ha
  all_goals simp only [max_eq_left hx, max_eq_right hx, max_eq_left ha, max_eq_right ha] at *
  all_goals rw [abs_le] at * <;> constructor <;> linarith [abs_nonneg (x-a)]

/-- A strict input error margin keeps the activation decision on the same side. -/
theorem sign_stable (x a error : ℝ) (bound : |x-a| ≤ error) (margin : error < |a|) :
    (0 < x ↔ 0 < a) := by
  rw [abs_le] at bound
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h] at margin
    constructor <;> intro <;> linarith
  · rw [abs_of_neg (lt_of_not_ge h)] at margin
    constructor <;> intro <;> linarith

end Ptx.Binary32.Relu
