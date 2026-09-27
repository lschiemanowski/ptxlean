import PtxBinary32Bounds
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
import Mathlib.Tactic

/-! Maximum selection on finite binary32 encodings using integer keys.
The selector returns an unchanged operand; the real theorem excludes exceptional inputs. -/
namespace Ptx.Binary32.Maximum

open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

def key (a : Word) : Word :=
  if a.toNat ≥ 2147483648 then a ^^^ 0xffffffff else a ^^^ 0x80000000

def choose (a b : Word) : Word :=
  if (key a).toNat < (key b).toNat then b else a

theorem choose_mem (a b : Word) : choose a b = a ∨ choose a b = b := by
  unfold choose
  split <;> simp

/-- The 23 fraction bits and biased exponent give one formula for normal
and subnormal magnitudes; at exponent zero the scale is 2^(-149). -/
private noncomputable def magnitude (e f : ℕ) : ℝ :=
  (if e = 0 then (f : ℝ) else (8388608 + f : ℝ)) *
    (2 : ℝ) ^ ((max e 1 : ℕ) - (150 : ℤ))

private theorem magnitude_nonneg (e f : ℕ) : 0 ≤ magnitude e f := by
  unfold magnitude
  positivity

private theorem magnitude_mono (e f e' f' : ℕ)
    (hf : f < 8388608) (hf' : f' < 8388608)
    (h : e < e' ∨ e = e' ∧ f ≤ f') : magnitude e f ≤ magnitude e' f' := by
  rcases h with h | ⟨rfl, h⟩
  · by_cases he : e = 0
    · subst e
      have he' : e' ≠ 0 := by omega
      have hs : (f : ℝ) ≤ 8388608 + f' := by exact_mod_cast (by omega : f ≤ 8388608 + f')
      have hp : (2 : ℝ) ^ ((1 : ℕ) - (150 : ℤ)) ≤
          (2 : ℝ) ^ ((max e' 1 : ℕ) - (150 : ℤ)) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        omega
      simp only [magnitude, ite_eq_right he', Nat.zero_max, ite_true]
      exact mul_le_mul hs hp (by positivity) (by positivity)
    · have he' : e' ≠ 0 := by omega
      have hs : (8388608 + f : ℝ) ≤ 2 * (8388608 + f' : ℝ) := by
        have hfR : (f : ℝ) < 8388608 := by exact_mod_cast hf
        have hfR' : (0 : ℝ) ≤ f' := by positivity
        linarith
      have hp : (2 : ℝ) ^ ((max e 1 : ℕ) - (150 : ℤ) + 1) ≤
          (2 : ℝ) ^ ((max e' 1 : ℕ) - (150 : ℤ)) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        omega
      simp only [magnitude, ite_eq_right he, ite_eq_right he']
      calc
        _ ≤ (2 * (8388608 + f' : ℝ)) * (2 : ℝ) ^ ((max e 1 : ℕ) - (150 : ℤ)) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (8388608 + f' : ℝ) * (2 : ℝ) ^ ((max e 1 : ℕ) - (150 : ℤ) + 1) := by
          rw [zpow_add₀ (by norm_num)]
          norm_num
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  · unfold magnitude
    have hR : (f : ℝ) ≤ f' := by exact_mod_cast h
    split <;> apply mul_le_mul_of_nonneg_right _ (by positivity) <;> linarith

private def exponent (a : Word) : ℕ := ((a >>> 23) &&& 255).toNat
private def fraction (a : Word) : ℕ := (a &&& 0x7fffff).toNat
private def negative (a : Word) : Bool := decide (2147483648 ≤ a.toNat)


private theorem value_shape (a : Word) (x : ℝ) (ha : finiteReal a = some x) :
    x = (if negative a then -1 else 1) * magnitude (exponent a) (fraction a) := by
  obtain ⟨hf, hx⟩ := Bounds.finiteReal_spec a x ha
  let m : Model FloatFormat.binary32 := Model.ofBits a
  change Model.isFinite m = true at hf
  change Model.toReal m = x at hx
  have he : Model.expField m = exponent a := by rfl
  have hfr : Model.fracField m = fraction a := by rfl
  have hs : Model.signBit m = negative a := by
    apply Bool.eq_iff_iff.mpr
    rw [Model.signBit_eq_true_iff_signMaskNat_le]
    change (2147483648 ≤ a.toNat) ↔ decide (2147483648 ≤ a.toNat) = true
    simp
  have hd := Model.toDyadic?_ofFields_of_isFinite FloatFormat.binary32
    (Model.signBit m) (Model.expField m) (Model.fracField m)
    (Model.expField_lt_pow2 m) (Model.fracField_lt_pow2 m)
    (by simpa only [Model.ofFields_signBit_expField_fracField] using hf)
  rw [Model.ofFields_signBit_expField_fracField] at hd
  rw [← hx, Model.toReal_eq, hd]
  rw [he, hfr, hs]
  change (match (if exponent a = 0 then
      if fraction a = 0 then some ⟨negative a, 0, 0⟩ else some ⟨negative a, fraction a, -149⟩
      else some ⟨negative a, 8388608 + fraction a, (exponent a : ℤ) - 127 - 23⟩) with
    | some d => FloatLib.Numerics.Dyadic.toReal d | none => 0) = _
  by_cases hE : exponent a = 0
  · by_cases hF : fraction a = 0
    · simp [hE, hF, magnitude, FloatLib.Numerics.Dyadic.toReal,
        FloatLib.Numerics.Dyadic.signedSignificand]
    · cases negative a <;>
        simp [hE, hF, magnitude, FloatLib.Numerics.Dyadic.toReal,
          FloatLib.Numerics.Dyadic.signedSignificand]
  · have hmax : max (exponent a) 1 = exponent a := by omega
    have heq : (exponent a : ℤ) - 127 - 23 = (exponent a : ℤ) - 150 := by omega
    cases negative a <;>
      simp [hE, hmax, heq, magnitude, FloatLib.Numerics.Dyadic.toReal,
        FloatLib.Numerics.Dyadic.signedSignificand]
    all_goals ring

private theorem exponent_eq (a : Word) : exponent a = a.toNat / 8388608 % 256 := by
  unfold exponent
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  change a.toNat >>> 23 &&& (2^8-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]


private theorem fraction_eq (a : Word) : fraction a = a.toNat % 8388608 := by
  unfold fraction
  simp only [BitVec.toNat_and]
  change a.toNat &&& (2^23-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]


private theorem key_nat (a : Word) : (key a).toNat =
    if 2147483648 ≤ a.toNat then 4294967295 - a.toNat else a.toNat + 2147483648 := by
  unfold key
  split
  · change (a ^^^ BitVec.allOnes 32).toNat = _
    simp only [BitVec.xor_allOnes, BitVec.toNat_not]
  · rename_i h
    have ha : a.toNat < 2147483648 := by omega
    have hm := Nat.xor_mod_two_pow (a := a.toNat) (b := 2147483648) (n := 31)
    have hd := Nat.xor_div_two_pow (a := a.toNat) (b := 2147483648) (n := 31)
    norm_num [Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha] at hm hd
    simp only [BitVec.toNat_xor]
    change (a.toNat ^^^ 2147483648) = _
    omega


private theorem key_order_cases (a b : Word) (h : (key a).toNat ≤ (key b).toNat) :
    (negative a = true ∧ negative b = false) ∨
    (negative a = false ∧ negative b = false ∧
      (exponent a < exponent b ∨ exponent a = exponent b ∧ fraction a ≤ fraction b)) ∨
    (negative a = true ∧ negative b = true ∧
      (exponent b < exponent a ∨ exponent b = exponent a ∧ fraction b ≤ fraction a)) := by
  rw [key_nat, key_nat] at h
  simp only [negative, decide_eq_true_eq, exponent_eq, fraction_eq]
  have ha := a.isLt
  have hb := b.isLt
  norm_num at ha hb
  split_ifs at h <;> simp_all [decide_eq_false_iff_not] <;> omega


private theorem fraction_bound (a : Word) : fraction a < 8388608 := by
  rw [fraction_eq]
  exact Nat.mod_lt _ (by decide)

/-- Unsigned keys preserve the real order of every finite pair, including signed zeros. -/
theorem key_order (a b : Word) (x y : ℝ)
    (ha : finiteReal a = some x) (hb : finiteReal b = some y)
    (h : (key a).toNat ≤ (key b).toNat) : x ≤ y := by
  rw [value_shape a x ha, value_shape b y hb]
  rcases key_order_cases a b h with ⟨hna, hnb⟩ | ⟨hna, hnb, ho⟩ | ⟨hna, hnb, ho⟩
  · simp only [hna, hnb, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
    exact le_trans (neg_nonpos.mpr (magnitude_nonneg _ _)) (magnitude_nonneg _ _)
  · simpa [hna, hnb] using magnitude_mono _ _ _ _ (fraction_bound a) (fraction_bound b) ho
  · have hm := magnitude_mono _ _ _ _ (fraction_bound b) (fraction_bound a) ho
    simpa [hna, hnb] using neg_le_neg hm

/-- Selection returns an operand with exactly the larger real value, without rounding. -/
theorem choose_real (a b : Word) (x y : ℝ)
    (ha : finiteReal a = some x) (hb : finiteReal b = some y) :
    finiteReal (choose a b) = some (max x y) := by
  unfold choose
  split
  · rename_i h
    rw [hb, max_eq_right (key_order a b x y ha hb (Nat.le_of_lt h))]
  · rename_i h
    rw [ha, max_eq_left (key_order b a y x hb ha (Nat.le_of_not_gt h))]

/-- The key convention selects positive zero in either operand order. -/
theorem choose_signed_zeros :
    choose 0 0x80000000 = 0 ∧ choose 0x80000000 0 = 0 := by decide

/-- Selection retains subnormals and correctly crosses the normal boundary. -/
theorem choose_subnormal_boundaries :
    choose 0 1 = 1 ∧ choose 0x80000001 0x80000000 = 0x80000000 ∧
    choose 0x007fffff 0x00800000 = 0x00800000 ∧
    choose 0x807fffff 0x80800000 = 0x807fffff := by decide

/-- Equal encodings retain the left operand. -/
theorem choose_self (a : Word) : choose a a = a := by simp [choose]

end Ptx.Binary32.Maximum
