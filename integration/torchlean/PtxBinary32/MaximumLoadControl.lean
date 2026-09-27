import PtxBinary32.MaximumAddressControl
import PtxBinary32.ParallelLoadControl

/-! Actual computed load addresses, independently of all candidate word values. -/
namespace Ptx.Scalar.Parallel.Maximum
open AddressControl (evaluate atPC)

private theorem four (x : Nat) : x+x+(x+x)=4*x := by omega
private theorem successor (x : Nat) : 4*x+4=4*(x+1) := by omega

theorem publication_read_control (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) : (atPC (program d) (controlSeed d seeds t) 3).addrs 0=bytePointer t.val := by
  have fit := lt_trans t.isLt (width_fits b)
  unfold atPC
  rw [program,List.append_assoc,List.take_append_of_le_length (show 3≤publish.length by simp)]
  simp [evaluate,publish,publishCode,pointer,Dense.pointer,Dense.scalar,controlSeed,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,bytePointer,
    BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,←BitVec.ofNat_add,four]

private theorem round_read_prefix (b : Bounds d) (t : Fin (width d)) (k : Nat) (hk : k<d)
    (seed : Scalar.State) (tid : seed.regs 0=BitVec.ofNat 32 t.val) (right : Bool) :
    let j := if right then 8 else 7
    let a := if right then 2 else 1
    let index := k*width d+2*t.val + if right then 1 else 0
    (evaluate ((round d k).take j) seed).addrs a=bytePointer index ∧
    (evaluate ((round d k).take j) seed).preds 0=decide (t.val<2^(d-(k+1))) := by
  have hd := bounds_depth b
  have hw : width d≤1024 := b
  have ht := t.isLt
  have bk := Nat.mul_le_mul_right (width d) (show k≤10 by omega)
  have fit : k*width d+2*t.val<4294967296 := by omega
  have cf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have limit : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits b)
  cases right <;>
    simp [evaluate,round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,word,Dense.word,
      AddressControl.instruction,AddressControl.scalar,AddressControl.advance,
      Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,tid,
      Scalar.BinOp.eval,Scalar.Compare.eval,←BitVec.ofNat_add,
      show t.val+t.val+k*width d=k*width d+2*t.val by omega,
      BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt limit,bytePointer,four,successor]

theorem round_read_control (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) (k : Nat) (hk : k<d) (right : Bool) :
    let j := if right then 8 else 7
    let a := if right then 2 else 1
    let index := k*width d+2*t.val + if right then 1 else 0
    (atPC (program d) (controlSeed d seeds t) (6+24*k+j)).addrs a=bytePointer index ∧
    (atPC (program d) (controlSeed d seeds t) (6+24*k+j)).preds 0=decide (t.val<2^(d-(k+1))) := by
  dsimp
  rw [program_round_split d k hk]
  have len : (publish ++ (List.range k).flatMap (round d)).length=6+24*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [←len,control_atPC_slice _ _ _ _ _ (by cases right <;> simp),AddressControl.evaluate_append]
  exact round_read_prefix b t k hk _ (by rw [rounds_control_identity,publish_control_identity]; simp [controlSeed]) right

private theorem output_read_prefix (b : Bounds d) (t : Fin (width d)) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate ((output d).take 5) seed).addrs 0=bytePointer (d*width d) ∧
    (evaluate ((output d).take 5) seed).preds 0=decide (t.val=0) := by
  have rf : d*width d<2^32 := lt_trans (by simpa using plane_bound d d 0 (Nat.le_refl _) (Nat.two_pow_pos _)) (shared_fits b)
  have cf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have gate : (BitVec.ofNat 32 t.val == (BitVec.ofNat 32 0))=decide (t.val=0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.zero_mod]
  simp [evaluate,output,outputCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,word,Dense.word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,
    Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,tid,
    Scalar.BinOp.eval,Scalar.Compare.eval,←BitVec.ofNat_add,
    BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) rf,gate,bytePointer,four]

theorem output_read_control (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) :
    (atPC (program d) (controlSeed d seeds t) (6+24*d+5)).addrs 0=bytePointer (d*width d) ∧
    (atPC (program d) (controlSeed d seeds t) (6+24*d+5)).preds 0=decide (t.val=0) := by
  have len : (publish ++ (List.range d).flatMap (round d)).length=6+24*d := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  have shape : program d=(publish ++ (List.range d).flatMap (round d)) ++ output d ++ [] := by simp [program]
  rw [shape,←len,control_atPC_slice _ _ _ _ _ (by simp),AddressControl.evaluate_append]
  exact output_read_prefix b t _ (by rw [rounds_control_identity,publish_control_identity]; simp [controlSeed])

end Ptx.Scalar.Parallel.Maximum
