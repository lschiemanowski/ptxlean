import PoissonPTX.ContractionLoads
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace PtxTorchLean.Poisson.PTX.Contraction

/-- Row-major arithmetic for Q1--Q4 (width at most five). The premises concern
index operands, not the values loaded or computed. -/
theorem index_exact (s : State) (width k : Nat) (m : Matrix)
    (hw : width ≤ 5)
    (hr : ((m.row.operand k).eval s).toNat < width)
    (hc : ((m.column.operand k).eval s).toNat < width) :
    (indexWord s width k m).toNat =
      ((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat := by
  have rowSmall : ((m.row.operand k).eval s).toNat < 2^32 := by omega
  have colSmall : ((m.column.operand k).eval s).toNat < 2^32 := by omega
  have widthSmall : width < 2^32 := by omega
  have productSmall : ((m.row.operand k).eval s).toNat * width < 2^32 := by
    interval_cases width <;> norm_num at * <;> omega
  have sumSmall : ((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat < 2^32 := by
    interval_cases width <;> norm_num at * <;> omega
  norm_num at rowSmall colSmall widthSmall productSmall sumSmall
  simp [indexWord,mul32,add32,BitVec.toNat_setWidth,BitVec.toNat_mul,BitVec.toNat_add,
    Nat.mod_eq_of_lt rowSmall,Nat.mod_eq_of_lt colSmall,Nat.mod_eq_of_lt widthSmall,
    Nat.mod_eq_of_lt productSmall,Nat.mod_eq_of_lt sumSmall]
  omega

theorem location_exact (s : State) (width k : Nat) (m : Matrix)
    (hw : width ≤ 5)
    (hr : ((m.row.operand k).eval s).toNat < width)
    (hc : ((m.column.operand k).eval s).toNat < width)
    (bound : (s.regs (baseRegister m.space)).toNat +
      (((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat)*8 + m.offset.toNat < 2^64) :
    (location s width k m).toNat = (s.regs (baseRegister m.space)).toNat +
      (((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat)*8 + m.offset.toNat := by
  have hi := index_exact s width k m hw hr hc
  have hs : ((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat < 2^32 := by
    interval_cases width <;> norm_num at * <;> omega
  norm_num at hs
  change (address64 (s.regs (baseRegister m.space)) ((indexWord s width k m).setWidth 32) m.offset).toNat = _
  rw [address64_exact]
  · simp [BitVec.toNat_setWidth,hi,Nat.mod_eq_of_lt hs]
  · simpa [BitVec.toNat_setWidth,hi,Nat.mod_eq_of_lt hs] using bound

/-- Contiguous complete matrices in the selected allocation supply every load's
alignment, bounds and nonwrapping conditions. -/
theorem valid_of_matrix (s : State) (width k : Nat) (m : Matrix)
    (hw : width ≤ 5)
    (hr : ((m.row.operand k).eval s).toNat < width)
    (hc : ((m.column.operand k).eval s).toNat < width)
    (base : (s.regs (baseRegister m.space)).toNat = s.start m.space)
    (aligned : s.start m.space % 8 = 0) (offsetAligned : m.offset.toNat % 8 = 0)
    (fits : m.offset.toNat + width*width*8 ≤ s.bytes m.space)
    (noWrap : s.start m.space + s.bytes m.space ≤ 2^64) : Valid s width k m := by
  have indexBound : (((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat)*8+8 ≤ width*width*8 := by
    interval_cases width <;> norm_num at * <;> omega
  have bound : (s.regs (baseRegister m.space)).toNat +
      (((m.row.operand k).eval s).toNat * width + ((m.column.operand k).eval s).toNat)*8 + m.offset.toNat < 2^64 := by
    rw [base]; omega
  unfold Valid
  rw [location_exact s width k m hw hr hc bound,base]
  refine ⟨by omega,?_,by omega,noWrap⟩
  simp [Nat.add_mod,aligned,offsetAligned]

end PtxTorchLean.Poisson.PTX.Contraction
