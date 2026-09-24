import Std

/-! Small proof interfaces for fixed-width unsigned values, not PTX semantics. -/
namespace Ptx.BitVecProof

/-- Observations commute with a Boolean choice, including out-of-width indices. -/
theorem getLsbD_ite (condition : Bool) (left right : BitVec width) (bit : Nat) :
    (if condition then left else right).getLsbD bit =
      (if condition then left.getLsbD bit else right.getLsbD bit) := by
  cases condition <;> rfl

/-- Parentheses keep Boolean AND inside the right-hand side of equality. -/
theorem getLsbD_ite_zero (condition : Bool) (value : BitVec width) (bit : Nat) :
    (if condition then value else (0 : BitVec width)).getLsbD bit =
      (condition && value.getLsbD bit) := by
  cases condition <;> simp

/-- Widening an unsigned value preserves its natural-number value. -/
theorem toNat_widen (value : BitVec small) (widths : small ≤ large) :
    (BitVec.ofNat large value.toNat).toNat = value.toNat := by
  simpa only [BitVec.ofNat_toNat] using (BitVec.toNat_setWidth_of_le (b := value) widths)

/-- Widening and then narrowing returns the original value. -/
theorem narrow_widen (value : BitVec small) (widths : small ≤ large) :
    BitVec.ofNat small (BitVec.ofNat large value.toNat).toNat = value := by
  rw [toNat_widen value widths]
  simp

/-- Narrowing then widening is lossless only under the stated range bound. -/
theorem widen_narrow (value : BitVec large) (fits : value.toNat < 2 ^ small) :
    BitVec.ofNat large (BitVec.ofNat small value.toNat).toNat = value := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  simp

end Ptx.BitVecProof
