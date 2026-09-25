import PtxBinary32.DenseProgram

/-! Natural-index layout agrees with represented word arithmetic on the bounded
kernel domain. Numeric address separation alone is not a memory-admission proof. -/
namespace Ptx.Scalar.Parallel.Dense

theorem thread_fits (s : Shape) (b : Bounds s) (t : Fin s.threads) : t.val < 2^32 := by
  have := t.isLt; have := b.threads; omega

theorem width_fits (s : Shape) (b : Bounds s) : s.width < 2^32 := by
  have := b.arithmetic; omega

theorem coordinates (s : Shape) (t : Fin s.threads) :
    t.val / s.width < s.rows ∧ t.val % s.width < s.width ∧
    s.thread (t.val / s.width) (t.val % s.width) = t.val := by
  have hp := width_positive s
  refine ⟨(Nat.div_lt_iff_lt_mul hp).mpr t.isLt,Nat.mod_lt _ hp,?_⟩
  simpa [Shape.thread,Nat.mul_comm] using Nat.div_add_mod t.val s.width

/-- Bit masking calculates the within-row column; logical shift calculates row. -/
theorem decoded_coordinates (s : Shape) (b : Bounds s) (t : Fin s.threads) :
    (Scalar.BinOp.eval .and (BitVec.ofNat 32 t.val) (BitVec.ofNat 32 (s.width-1))).toNat = t.val % s.width ∧
    (Scalar.BinOp.eval .shr (BitVec.ofNat 32 t.val) (BitVec.ofNat 32 s.depth)).toNat = t.val / s.width := by
  have ht := thread_fits s b t
  have hw := width_fits s b
  have hd : s.depth < 2^32 := by have := b.depth; omega
  norm_num at ht hw hd
  have mask : 2^s.depth-1 < 4294967296 := by change 2^s.depth < 4294967296 at hw; omega
  constructor
  · simp [Scalar.BinOp.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ht,
      Shape.width,Nat.mod_eq_of_lt mask]
  · simp [Scalar.BinOp.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt hd,b.depth,Nat.shiftRight_eq_div_pow,Shape.width]

def bytePointer (index : Nat) : Scalar.Address := BitVec.ofNat 64 (4*index)

theorem pointer_index (memory : List Word) (index : Nat)
    (inside : index < memory.length) (fits : 4*index < 2^64) :
    Scalar.addressIndex memory (bytePointer index) = .ok index := by
  change 4*index < 18446744073709551616 at fits
  simp [Scalar.addressIndex,bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits,inside]

/-- Widening before the two additions implements multiplication by four. -/
theorem pointer_arithmetic (index : Nat) (fits : index < 2^32) :
    let a : Scalar.Address := BitVec.ofNat 64 (BitVec.ofNat 32 index).toNat
    (a+a)+(a+a) = bytePointer index := by
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
  simp [bytePointer,← BitVec.ofNat_add,show index+index+(index+index)=4*index by omega]

theorem global_output_disjoint (s : Shape) (row col : Nat)
    (hr : row < s.rows) (hc : col < s.columns) :
    s.weight row col < s.outputBase ∧ col < s.outputBase ∧ s.biasBase+row < s.outputBase := by
  obtain ⟨input,_,weight,bias,_,_⟩ := global_slices s row col hr hc
  simp only [Shape.outputBase,Shape.biasBase,Shape.weightBase] at *
  omega

end Ptx.Scalar.Parallel.Dense
