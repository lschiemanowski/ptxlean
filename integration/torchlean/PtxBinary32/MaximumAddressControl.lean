import PtxBinary32.MaximumControl
import PtxBinary32.ParallelAddressControl

/-! The supplied maximum instruction list satisfies the address-control projection
contract. Input data are omitted only after per-instruction compatibility is
proved; arbitrary candidate executions retain exactly these control values. -/
namespace Ptx.Scalar.Parallel.Maximum

open AddressControl (Agree evaluate atPC)

theorem program_address_compatible (d : Nat) : AddressControl.ProgramCompatible (program d) := by
  intro i member
  simp only [program,List.mem_append,List.mem_flatMap,List.mem_range] at member
  rcases member with (first | ⟨k,hk,roundMem⟩) | last
  · simp [publish,publishCode,pointer,Dense.pointer] at first
    rcases first with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,Dense.scalar,Scalar.Instr.plain]
  · simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer] at roundMem
    rcases roundMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,scalar,Dense.scalar,guarded,Dense.guarded,Scalar.Instr.plain,word,Dense.word]
  · simp [output,outputCode,pointer,Dense.pointer] at last
    rcases last with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,scalar,Dense.scalar,guarded,Dense.guarded,Scalar.Instr.plain,word,Dense.word]

def controlSeed (d : Nat) (seeds : Fin (width d) → Scalar.State) (t : Fin (width d)) : Scalar.State :=
  {seeds t with pc := 0,regs := Scalar.update (seeds t).regs 0 (BitVec.ofNat 32 t.val)}

theorem initial_address_control (d : Nat) (global shared : List Word) (seeds : Fin (width d) → Scalar.State) :
    AddressControl.Invariant (program d) (controlSeed d seeds) (initial d global shared seeds) := by
  intro t
  exact AddressControl.agree_refl (controlSeed d seeds t)

/-- No desired read values, address invariants or numerical facts are premises. -/
theorem candidate_address_control (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final) :
    AddressControl.Invariant (program d) (controlSeed d seeds) final :=
  AddressControl.runs_invariant run (program_address_compatible d) (initial_address_control d global shared seeds)
    (reset_aligned _ _ _ _)


/-- The thread identity survives every phase independently of candidate loads. -/
theorem publish_control_identity (state : Scalar.State) :
    (evaluate publish state).regs 0=state.regs 0 := by
  simp [evaluate,publish,publishCode,pointer,Dense.pointer,Dense.scalar,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Instr.plain]

theorem round_control_identity (d k : Nat) (state : Scalar.State) :
    (evaluate (round d k) state).regs 0=state.regs 0 := by
  simp [evaluate,round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.update,Scalar.Instr.plain,word,Dense.word]

theorem rounds_control_identity (d : Nat) (ks : List Nat) (state : Scalar.State) :
    (evaluate (ks.flatMap (round d)) state).regs 0=state.regs 0 := by
  induction ks generalizing state with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatMap_cons,AddressControl.evaluate_append]
    rw [ih,round_control_identity]

theorem control_atPC_slice (before code after : List Instr) (seed : Scalar.State) (k : Nat)
    (bound : k≤code.length) :
    atPC (before++code++after) seed (before.length+k)=evaluate (code.take k) (evaluate before seed) := by
  simp only [atPC,List.append_assoc,List.take_append]
  rw [List.take_of_length_le (by omega : before.length≤before.length+k)]
  simp only [Nat.add_sub_cancel_left]
  rw [Nat.sub_eq_zero_of_le bound]
  simp [AddressControl.evaluate_append]

abbrev bytePointer (index : Nat) : Scalar.Address := BitVec.ofNat 64 (4*index)

private theorem four (x : Nat) : x+x+(x+x)=4*x := by omega

private theorem publication_pointer (b : Bounds d) (t : Fin (width d)) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate (publish.take 4) seed).addrs 0=bytePointer t.val := by
  have fit := lt_trans t.isLt (width_fits b)
  simp [evaluate,publish,publishCode,pointer,Dense.pointer,Dense.scalar,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,tid,bytePointer,
    BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,←BitVec.ofNat_add,four]

private theorem round_pointer (b : Bounds d) (t : Fin (width d)) (k : Nat)
    (hk : k<d) (seed : Scalar.State) (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate ((round d k).take 22) seed).addrs 3=bytePointer ((k+1)*width d+t.val) := by
  have fit : (k+1)*width d+t.val<4294967296 := lt_trans (plane_bound d (k+1) t.val hk t.isLt) (shared_fits b)
  simp [evaluate,round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,word,Dense.word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,tid,Scalar.BinOp.eval,←BitVec.ofNat_add,
    Nat.add_comm t.val,bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,four]

private theorem output_pointer (b : Bounds d) (t : Fin (width d)) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate ((output d).take 10) seed).addrs 1=bytePointer (width d) ∧
    (evaluate ((output d).take 10) seed).preds 0=decide (t.val=0) := by
  have fit := width_fits b
  have tf : t.val<4294967296 := lt_trans t.isLt fit
  have gate : (BitVec.ofNat 32 t.val == (BitVec.ofNat 32 0))=decide (t.val=0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,←BitVec.toNat_inj,BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf,Nat.zero_mod]
  simp [evaluate,output,outputCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,word,Dense.word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,tid,Scalar.BinOp.eval,Scalar.Compare.eval,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,←BitVec.ofNat_add,four,gate]

theorem publication_control_address (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) : (atPC (program d) (controlSeed d seeds t) 4).addrs 0=bytePointer t.val := by
  unfold atPC
  rw [program,List.append_assoc,List.take_append_of_le_length (show 4≤publish.length by simp)]
  exact publication_pointer b t _ (by simp [controlSeed])

theorem round_control_address (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) (k : Nat) (hk : k<d) :
    (atPC (program d) (controlSeed d seeds t) (6+24*k+22)).addrs 3=bytePointer ((k+1)*width d+t.val) := by
  rw [program_round_split d k hk]
  have len : (publish ++ (List.range k).flatMap (round d)).length=6+24*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [←len,control_atPC_slice _ _ _ _ 22 (by simp),AddressControl.evaluate_append]
  exact round_pointer b t k hk _ (by rw [rounds_control_identity,publish_control_identity]; simp [controlSeed])

theorem output_control_address (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) :
    (atPC (program d) (controlSeed d seeds t) (6+24*d+10)).addrs 1=bytePointer (width d) ∧
    (atPC (program d) (controlSeed d seeds t) (6+24*d+10)).preds 0=decide (t.val=0) := by
  have len : (publish ++ (List.range d).flatMap (round d)).length=6+24*d := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  have shape : program d=(publish ++ (List.range d).flatMap (round d)) ++ output d ++ [] := by simp [program]
  rw [shape,←len,control_atPC_slice _ _ _ _ 10 (by simp),AddressControl.evaluate_append]
  exact output_pointer b t _ (by rw [rounds_control_identity,publish_control_identity]; simp [controlSeed])

/-- Active lanes are determined entirely by their fixed input position. -/
theorem round_control_active (b : Bounds d) (seeds : Fin (width d)→Scalar.State)
    (t : Fin (width d)) (k : Nat) (hk : k<d) :
    (atPC (program d) (controlSeed d seeds t) (6+24*k+22)).preds 0 =
      decide (t.val<2^(d-(k+1))) := by
  rw [program_round_split d k hk]
  have len : (publish ++ (List.range k).flatMap (round d)).length=6+24*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [←len,control_atPC_slice _ _ _ _ 22 (by simp),AddressControl.evaluate_append]
  have tid : (evaluate ((List.range k).flatMap (round d)) (evaluate publish (controlSeed d seeds t))).regs 0=BitVec.ofNat 32 t.val := by
    rw [rounds_control_identity,publish_control_identity]; simp [controlSeed]
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have limit : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits b)
  have active (state : Scalar.State) (ident : state.regs 0=BitVec.ofNat 32 t.val) :
      (evaluate ((round d k).take 22) state).preds 0=decide (t.val<2^(d-(k+1))) := by
    simp [evaluate,round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded,word,Dense.word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,ident,Scalar.Compare.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf,Nat.mod_eq_of_lt limit]
  exact active _ tid

end Ptx.Scalar.Parallel.Maximum
