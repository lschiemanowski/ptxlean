import Ptx.BitVecProof

open Ptx.BitVecProof

-- A conditional mask: the bit-level law holds at any width and any bit index.
example (enabled : Bool) (a b : BitVec width) (bit : Nat) :
    (if enabled then a &&& b else (0 : BitVec width)).getLsbD bit =
      (enabled && (a.getLsbD bit && b.getLsbD bit)) := by
  rw [getLsbD_ite_zero, BitVec.getLsbD_and]

-- Complement needs a valid bit index: observations outside the width are false.
example (a : BitVec width) (bit : Nat) (valid : bit < width) :
    (~~~a).getLsbD bit = !a.getLsbD bit := by
  simp [valid]

-- A decoder stores an eight-bit operation parameter in a 32-bit immediate.
example (value : BitVec 8) :
    (BitVec.ofNat 32 value.toNat).toNat ≤ 255 := by
  rw [toNat_widen value (by decide : 8 ≤ 32)]
  have bound := value.isLt
  omega

example (value : BitVec 8) :
    BitVec.ofNat 8 (BitVec.ofNat 32 value.toNat).toNat = value :=
  narrow_widen value (by decide)

-- The reverse direction uses the decoder's range check, not just the widths.
example (value : BitVec 32) (accepted : value.toNat ≤ 255) :
    BitVec.ofNat 32 (BitVec.ofNat 8 value.toNat).toNat = value :=
  widen_narrow value (by omega)

-- Boundary examples expose why a missing range check loses information.
example : BitVec.ofNat 32 (BitVec.ofNat 8 256).toNat ≠ BitVec.ofNat 32 256 := by decide
example : BitVec.ofNat 32 (BitVec.ofNat 8 255).toNat = BitVec.ofNat 32 255 := by decide
example : (if true then (0 : BitVec 0) else 0).getLsbD 0 = false := by decide
example : (if true then (255 : BitVec 8) else 0).getLsbD 8 = false := by decide

#print axioms Ptx.BitVecProof.getLsbD_ite
#print axioms Ptx.BitVecProof.getLsbD_ite_zero
#print axioms Ptx.BitVecProof.toNat_widen
#print axioms Ptx.BitVecProof.narrow_widen
#print axioms Ptx.BitVecProof.widen_narrow
