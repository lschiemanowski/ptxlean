import PoissonPTX.CellAccessBounds
import PoissonPTX.ByteHistoryStep

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

/-- The two physical allocations contain the coefficient tables and seven
shared planes, are aligned, and do not wrap the 64-bit address space. -/
def Allocation (width : Nat) (bases : Space → Word) (s : PTX.State) : Prop :=
  ∀ space, s.start space=(bases space).toNat ∧ s.start space%8=0 ∧
    extent width space≤s.bytes space ∧ s.start space+s.bytes space≤2^64

theorem allocation_data (actual : Data op s next access) (physical : Allocation width bases s) :
    Allocation width bases next := by
  obtain ⟨start,bytes⟩ := ByteHistory.data_allocation actual
  intro space
  simpa only [start,bytes] using physical space

theorem valid_operand {address : Operand} (physical : Allocation width bases s)
    (related : Matches bases memory regs s)
    (certificate : match Numeric.extract (operand regs address) with
      | some (sp,off) => sp=space ∧ off.toNat%8=0 ∧ off.toNat+8≤extent width space
      | none => False) :
    Valid64 (s.start space) (s.bytes space) (address.eval s).toNat := by
  have matchOperand := operand_sound related address
  cases extracted : Numeric.extract (operand regs address) with
  | none => simp [extracted] at certificate
  | some pair =>
    obtain ⟨sp,off⟩ := pair
    simp only [extracted] at certificate
    obtain ⟨rfl,aligned,within⟩ := certificate
    obtain ⟨base,baseAligned,enough,nowrap⟩ := physical sp
    have exactAddress := Numeric.extract_sound matchOperand extracted
    rw [exactAddress,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    rw [base] at baseAligned nowrap ⊢
    refine ⟨by omega,?_,by omega,nowrap⟩
    simp [Nat.add_mod,baseAligned,aligned]

/-- Access safety is derived from the checked instruction/address expression
and allocation geometry. No validity or loaded value is assumed for a step. -/
theorem next_valid {thread : Fin n} (bounds : AccessBounds width) (active : thread.val<width*width)
    (physical : Allocation width bases s)
    (related : Matches bases memory (atPC .addresses (program width) (Numeric.seed width thread.val) s.pc) s)
    (fetch : (program width)[s.pc]?=some (.data op)) : ByteHistory.ValidOp op s := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  have certificate := bounds ⟨thread.val,active⟩ ⟨s.pc,bound⟩
  cases op with
  | load64 space dst address =>
    simp only [accessCheck,fetch] at certificate
    exact valid_operand physical related certificate
  | store64 space address src =>
    simp only [accessCheck,fetch] at certificate
    exact valid_operand physical related certificate
  | _ => trivial

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
