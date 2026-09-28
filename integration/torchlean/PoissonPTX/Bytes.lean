import Std.Tactic.BVDecide
import Mathlib.Data.BitVec

/-! Byte-addressed, little-endian storage for the Poisson binary64 slice.
This is concrete storage, not by itself an admission rule for weak PTX reads. -/
namespace PtxTorchLean.Poisson.PTX

abbrev Byte := BitVec 8
abbrev Word := BitVec 64
abbrev Memory := Nat → Byte

def byte (w : Word) (i : Nat) : Byte := w.extractLsb' (8*i) 8

def read64 (m : Memory) (a : Nat) : Word :=
  m (a+7) ++ m (a+6) ++ m (a+5) ++ m (a+4) ++
  m (a+3) ++ m (a+2) ++ m (a+1) ++ m a

def write64 (m : Memory) (a : Nat) (w : Word) : Memory :=
  fun p => if a ≤ p ∧ p < a+8 then byte w (p-a) else m p

@[simp] theorem write64_at (m : Memory) (a : Nat) (w : Word) (i : Nat) (hi : i < 8) :
    write64 m a w (a+i) = byte w i := by simp [write64]; omega

theorem write64_outside (m : Memory) (a : Nat) (w : Word) (p : Nat)
    (outside : p < a ∨ a+8 ≤ p) : write64 m a w p = m p := by
  simp [write64]; omega

@[simp] theorem read64_write64 (m : Memory) (a : Nat) (w : Word) :
    read64 (write64 m a w) a = w := by
  simp only [read64]
  have h0 : write64 m a w a = byte w 0 := by simpa using write64_at m a w 0 (by omega)
  rw [write64_at m a w 7 (by omega), write64_at m a w 6 (by omega),
    write64_at m a w 5 (by omega), write64_at m a w 4 (by omega),
    write64_at m a w 3 (by omega), write64_at m a w 2 (by omega),
    write64_at m a w 1 (by omega), h0]
  simp only [byte]
  bv_decide

theorem read64_write64_disjoint (m : Memory) (a b : Nat) (w : Word)
    (disjoint : a+8 ≤ b ∨ b+8 ≤ a) : read64 (write64 m a w) b = read64 m b := by
  have h (i : Nat) (hi : i < 8) : write64 m a w (b+i) = m (b+i) :=
    write64_outside m a w (b+i) (by omega)
  simp only [read64]
  rw [h 7 (by omega),h 6 (by omega),h 5 (by omega),h 4 (by omega),
    h 3 (by omega),h 2 (by omega),h 1 (by omega),show write64 m a w b = m b from by simpa using h 0 (by omega)]

def Valid64 (start bytes address : Nat) : Prop :=
  start ≤ address ∧ address % 8 = 0 ∧ address+8 ≤ start+bytes ∧ start+bytes ≤ 2^64

instance (start bytes address : Nat) : Decidable (Valid64 start bytes address) := by
  unfold Valid64; infer_instance

theorem valid_nonwrapping (h : Valid64 start bytes address) : address < 2^64 := by
  rcases h with ⟨_,_,_,_⟩; omega

/-- The physical integer-address calculation used in every generated access. -/
def address64 (base : Word) (index : BitVec 32) (offset : Word) : Word :=
  base + BitVec.ofNat 64 (index.toNat*8) + offset

theorem address64_exact (base : Word) (index : BitVec 32) (offset : Word)
    (bound : base.toNat + index.toNat*8 + offset.toNat < 2^64) :
    (address64 base index offset).toNat = base.toNat + index.toNat*8 + offset.toNat := by
  have hi := index.isLt
  have hw : index.toNat*8 < 2^64 := by omega
  have hb : base.toNat + index.toNat*8 < 2^64 := by omega
  simp only [address64, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt bound]

end PtxTorchLean.Poisson.PTX
