import PtxBinary32.DenseAddressControl
import PtxBinary32.ParallelLoadControl

/-! Computed addresses and active predicates of the actual dense load sites. -/
namespace Ptx.Scalar.Parallel.Dense
open AddressControl (evaluate atPC)

private theorem product_read_prefix (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) (weight : Bool) :
    let j := if weight then 15 else 11
    let a := if weight then 1 else 0
    let index := if weight then s.weight (t.val/s.width) (t.val%s.width) else t.val%s.width
    (evaluate ((products s).take j) seed).addrs a=bytePointer index ∧
    (evaluate ((products s).take j) seed).preds 0=decide (t.val%s.width<s.columns) := by
  have decoded := decoded_coordinates s b t
  have col := congrArg (BitVec.ofNat 32) decoded.1
  have row := congrArg (BitVec.ofNat 32) decoded.2
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at col row
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have wf := weight_index_fits s b t
  have nf : s.columns<4294967296 := lt_of_le_of_lt s.padded (width_fits s b)
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  have wi : t.val/s.width*s.columns+t.val%s.width+s.weightBase=s.weight (t.val/s.width) (t.val%s.width) := by simp [Shape.weight]; omega
  have add (a b : Word) : Scalar.BinOp.eval .add a b=a+b := rfl
  have mul (a b : Word) : Scalar.BinOp.eval .mulLo a b=a*b := rfl
  cases weight <;>
    simp [evaluate,products,pointer,scalar,guarded,word,AddressControl.instruction,AddressControl.scalar,
      AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,tid,col,row,
      add,mul,Scalar.Compare.eval,← BitVec.ofNat_add,← BitVec.ofNat_mul,wi,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) cf,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) wf,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt nf,bytePointer,four]

theorem product_read_control (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (weight : Bool) :
    let j := if weight then 15 else 11
    let a := if weight then 1 else 0
    let index := if weight then s.weight (t.val/s.width) (t.val%s.width) else t.val%s.width
    (atPC (program s) (controlSeed s seeds t) j).addrs a=bytePointer index ∧
    (atPC (program s) (controlSeed s seeds t) j).preds 0=decide (t.val%s.width<s.columns) := by
  dsimp
  unfold atPC
  rw [program,List.append_assoc,List.take_append_of_le_length (show (if weight then 15 else 11)≤(products s).length by cases weight <;> simp)]
  exact product_read_prefix s b t _ (by simp [controlSeed]) weight

private theorem round_read_prefix (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (k : Nat) (hk : k<s.depth)
    (seed : Scalar.State) (coords : ControlCoordinates s t seed) (right : Bool) :
    let j := if right then 8 else 7
    let a := if right then 4 else 3
    let index := leftIndex s k t + if right then 1 else 0
    (evaluate ((round s k).take j) seed).addrs a=bytePointer index ∧
    (evaluate ((round s k).take j) seed).preds 0=decide (t.val%s.width<2^(s.depth-(k+1))) := by
  have fit := (round_indices s b k hk t).1
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have limit : 2^(s.depth-(k+1))<4294967296 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits s b)
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  have successor : ∀ x : Nat, 4*x+4=4*(x+1) := by intro x; omega
  cases right <;>
    simp [evaluate,round,pointer,scalar,guarded,word,AddressControl.instruction,AddressControl.scalar,
      AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,coords.1,coords.2.1,
      Scalar.BinOp.eval,Scalar.Compare.eval,← BitVec.ofNat_add,show t.val+t.val%s.width+k*s.threads=leftIndex s k t from rfl,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt limit,bytePointer,four,successor]

theorem round_read_control (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (k : Nat) (hk : k<s.depth) (right : Bool) :
    let j := if right then 8 else 7
    let a := if right then 4 else 3
    let index := leftIndex s k t + if right then 1 else 0
    (atPC (program s) (controlSeed s seeds t) (22+16*k+j)).addrs a=bytePointer index ∧
    (atPC (program s) (controlSeed s seeds t) (22+16*k+j)).preds 0=decide (t.val%s.width<2^(s.depth-(k+1))) := by
  dsimp
  rw [program_round_split s k hk]
  have len : (products s ++ (List.range k).flatMap (round s)).length=22+16*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [← len,control_atPC_slice _ _ _ _ _ (by cases right <;> simp),AddressControl.evaluate_append]
  exact round_read_prefix s b t k hk _ (rounds_control_coordinates s t _ _
    (products_control_coordinates s b t _ (by simp [controlSeed]))) right

private theorem output_read_prefix (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (seed : Scalar.State)
    (coords : ControlCoordinates s t seed) (bias : Bool) :
    let j := if bias then 10 else 5
    let a := if bias then 5 else 2
    let index := if bias then biasIndex s t else rootIndex s t
    (evaluate ((output s).take j) seed).addrs a=bytePointer index ∧
    (evaluate ((output s).take j) seed).preds 0=decide (t.val%s.width=0) := by
  have indices := output_indices s t
  have rf : rootIndex s t<2^32 := by have := b.arithmetic; omega
  have bf : biasIndex s t<2^32 := by
    have : s.outputBase≤s.globalWords := by simp [Shape.globalWords]
    have := b.arithmetic; omega
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  have gate : (BitVec.ofNat 32 (t.val%s.width) == (BitVec.ofNat 32 0))=decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  cases bias <;>
    simp [evaluate,output,pointer,scalar,guarded,word,AddressControl.instruction,AddressControl.scalar,
      AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,coords.1,coords.2.1,coords.2.2,
      Scalar.BinOp.eval,Scalar.Compare.eval,← BitVec.ofNat_add,
      show t.val+s.depth*s.threads=rootIndex s t from rfl,show t.val/s.width+s.biasBase=biasIndex s t from rfl,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) rf,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) bf,gate,bytePointer,four]

theorem output_read_control (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (bias : Bool) :
    let j := if bias then 10 else 5
    let a := if bias then 5 else 2
    let index := if bias then biasIndex s t else rootIndex s t
    (atPC (program s) (controlSeed s seeds t) (22+16*s.depth+j)).addrs a=bytePointer index ∧
    (atPC (program s) (controlSeed s seeds t) (22+16*s.depth+j)).preds 0=decide (t.val%s.width=0) := by
  dsimp
  have len : (products s ++ (List.range s.depth).flatMap (round s)).length=22+16*s.depth := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  have shape : program s=(products s ++ (List.range s.depth).flatMap (round s)) ++ output s ++ [] := by simp [program]
  rw [shape,← len,control_atPC_slice _ _ _ _ _ (by cases bias <;> simp),AddressControl.evaluate_append]
  exact output_read_prefix s b t _ (rounds_control_coordinates s t _ _
    (products_control_coordinates s b t _ (by simp [controlSeed]))) bias

end Ptx.Scalar.Parallel.Dense
