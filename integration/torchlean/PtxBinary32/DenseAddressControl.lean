import PtxBinary32.DenseControl
import PtxBinary32.DenseAddress
import PtxBinary32.ParallelAddressControl

/-! The supplied dense instruction list satisfies the address-control projection
contract. Tensor data are omitted only after per-instruction compatibility is
proved; arbitrary candidate executions retain exactly these control values. -/
namespace Ptx.Scalar.Parallel.Dense

open AddressControl (Agree evaluate atPC)

theorem program_address_compatible (s : Shape) : AddressControl.ProgramCompatible (program s) := by
  intro i member
  simp only [program,List.mem_append,List.mem_flatMap,List.mem_range] at member
  rcases member with (first | ⟨k,hk,roundMem⟩) | last
  · simp [products,pointer] at first
    rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,scalar,guarded,Scalar.Instr.plain,word]
  · simp [round,pointer] at roundMem
    rcases roundMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,scalar,guarded,Scalar.Instr.plain,word]
  · simp [output,pointer] at last
    rcases last with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [AddressControl.Compatible,AddressControl.Allowed,AddressControl.Known,
      AddressControl.Visible,scalar,guarded,Scalar.Instr.plain,word]

def controlSeed (s : Shape) (seeds : Fin s.threads → Scalar.State) (t : Fin s.threads) : Scalar.State :=
  {seeds t with pc := 0,regs := Scalar.update (seeds t).regs 0 (BitVec.ofNat 32 t.val)}

theorem initial_address_control (s : Shape) (global shared : List Word) (seeds : Fin s.threads → Scalar.State) :
    AddressControl.Invariant (program s) (controlSeed s seeds) (initial s global shared seeds) := by
  intro t
  exact AddressControl.agree_refl (controlSeed s seeds t)

/-- No desired read values, address invariants or numerical facts are premises. -/
theorem candidate_address_control (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final) :
    AddressControl.Invariant (program s) (controlSeed s seeds) final :=
  AddressControl.runs_invariant run (program_address_compatible s) (initial_address_control s global shared seeds)
    (reset_aligned _ _ _ _)

/-- Coordinates used by all subsequent pointer calculations. -/
def ControlCoordinates (s : Shape) (t : Fin s.threads) (state : Scalar.State) : Prop :=
  state.regs 0=BitVec.ofNat 32 t.val ∧
  state.regs 1=BitVec.ofNat 32 (t.val%s.width) ∧
  state.regs 2=BitVec.ofNat 32 (t.val/s.width)

theorem products_control_coordinates (s : Shape) (b : Bounds s) (t : Fin s.threads) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) : ControlCoordinates s t (evaluate (products s) seed) := by
  have coords := decoded_coordinates s b t
  have col := congrArg (BitVec.ofNat 32) coords.1
  have row := congrArg (BitVec.ofNat 32) coords.2
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at col row
  simp [ControlCoordinates,evaluate,products,pointer,scalar,guarded,word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,
    Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,tid,col,row]

theorem round_control_coordinates (s : Shape) (t : Fin s.threads) (k : Nat) (state : Scalar.State)
    (coords : ControlCoordinates s t state) : ControlCoordinates s t (evaluate (round s k) state) := by
  simpa [ControlCoordinates,evaluate,round,pointer,scalar,guarded,word,
    AddressControl.instruction,AddressControl.scalar,AddressControl.advance,
    Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update] using coords

theorem rounds_control_coordinates (s : Shape) (t : Fin s.threads) (ks : List Nat) (state : Scalar.State)
    (coords : ControlCoordinates s t state) :
    ControlCoordinates s t (evaluate (ks.flatMap (round s)) state) := by
  induction ks generalizing state with
  | nil => exact coords
  | cons k ks ih =>
    simp only [List.flatMap_cons,AddressControl.evaluate_append]
    exact ih _ (round_control_coordinates s t k state coords)

theorem control_atPC_slice (before code after : List Instr) (seed : Scalar.State) (k : Nat)
    (bound : k≤code.length) :
    atPC (before++code++after) seed (before.length+k)=evaluate (code.take k) (evaluate before seed) := by
  simp only [atPC,List.append_assoc,List.take_append]
  rw [List.take_of_length_le (by omega : before.length≤before.length+k)]
  simp only [Nat.add_sub_cancel_left]
  rw [Nat.sub_eq_zero_of_le bound]
  simp [AddressControl.evaluate_append]

private theorem product_pointer (s : Shape) (b : Bounds s) (t : Fin s.threads) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate ((products s).take 20) seed).addrs 2=bytePointer t.val := by
  have fits := thread_fits s b t
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  simp [evaluate,products,pointer,scalar,guarded,word,AddressControl.instruction,
    AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,tid,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fits,← BitVec.ofNat_add,four]

private theorem round_pointer (s : Shape) (b : Bounds s) (t : Fin s.threads) (k : Nat)
    (hk : k<s.depth) (seed : Scalar.State) (coords : ControlCoordinates s t seed) :
    (evaluate ((round s k).take 14) seed).addrs 2=bytePointer (nextIndex s k t) := by
  have fit : nextIndex s k t<4294967296 := by
    have := (round_indices s b k hk t).2.1; have := b.arithmetic; omega
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  simp [evaluate,round,pointer,scalar,guarded,word,AddressControl.instruction,
    AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,coords.1,Scalar.BinOp.eval,← BitVec.ofNat_add,
    show t.val+(k+1)*s.threads=nextIndex s k t from rfl,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,four]

private theorem output_pointer (s : Shape) (b : Bounds s) (t : Fin s.threads) (seed : Scalar.State)
    (coords : ControlCoordinates s t seed) :
    (evaluate ((output s).take 18) seed).addrs 6=bytePointer (outputIndex s t) ∧
    (evaluate ((output s).take 18) seed).preds 0=decide (t.val%s.width=0) := by
  have fit : outputIndex s t<4294967296 := by have := (output_indices s t).2.2; have := b.arithmetic; omega
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  have gate : (BitVec.ofNat 32 (t.val%s.width) == (BitVec.ofNat 32 0))=decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  simp [evaluate,output,pointer,scalar,guarded,word,AddressControl.instruction,
    AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,coords.2.1,coords.2.2,Scalar.BinOp.eval,Scalar.Compare.eval,
    ← BitVec.ofNat_add,BitVec.toNat_ofNat,show t.val/s.width+s.outputBase=outputIndex s t from rfl,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,four,gate]

theorem product_control_address (s : Shape) (b : Bounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) : (atPC (program s) (controlSeed s seeds t) 20).addrs 2=bytePointer t.val := by
  unfold atPC
  rw [program,List.append_assoc,List.take_append_of_le_length (show 20≤(products s).length by simp)]
  exact product_pointer s b t _ (by simp [controlSeed])

theorem round_control_address (s : Shape) (b : Bounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (k : Nat) (hk : k<s.depth) :
    (atPC (program s) (controlSeed s seeds t) (22+16*k+14)).addrs 2=bytePointer (nextIndex s k t) := by
  rw [program_round_split s k hk]
  have len : (products s ++ (List.range k).flatMap (round s)).length=22+16*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [← len,control_atPC_slice _ _ _ _ 14 (by simp),AddressControl.evaluate_append]
  exact round_pointer s b t k hk _ (rounds_control_coordinates s t _ _
    (products_control_coordinates s b t _ (by simp [controlSeed])))

theorem output_control_address (s : Shape) (b : Bounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) :
    (atPC (program s) (controlSeed s seeds t) (22+16*s.depth+18)).addrs 6=bytePointer (outputIndex s t) ∧
    (atPC (program s) (controlSeed s seeds t) (22+16*s.depth+18)).preds 0=decide (t.val%s.width=0) := by
  have len : (products s ++ (List.range s.depth).flatMap (round s)).length=22+16*s.depth := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  have shape : program s=(products s ++ (List.range s.depth).flatMap (round s)) ++ output s ++ [] := by simp [program]
  rw [shape,← len,control_atPC_slice _ _ _ _ 18 (by simp),AddressControl.evaluate_append]
  exact output_pointer s b t _ (rounds_control_coordinates s t _ _
    (products_control_coordinates s b t _ (by simp [controlSeed])))

/-- Predicate zero selects exactly the active columns of this reduction round. -/
theorem round_control_active (s : Shape) (b : Bounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (k : Nat) (hk : k<s.depth) :
    (atPC (program s) (controlSeed s seeds t) (22+16*k+14)).preds 0 =
      decide (t.val%s.width<2^(s.depth-(k+1))) := by
  rw [program_round_split s k hk]
  have len : (products s ++ (List.range k).flatMap (round s)).length=22+16*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [← len,control_atPC_slice _ _ _ _ 14 (by simp),AddressControl.evaluate_append]
  have coords := rounds_control_coordinates s t (List.range k) _
    (products_control_coordinates s b t (controlSeed s seeds t) (by simp [controlSeed]))
  have colFit : t.val%s.width<2^32 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have limitFit : 2^(s.depth-(k+1))<2^32 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits s b)
  norm_num at colFit limitFit
  have active (state : Scalar.State) (hc : ControlCoordinates s t state) :
      (evaluate ((round s k).take 14) state).preds 0=decide (t.val%s.width<2^(s.depth-(k+1))) := by
    simp [evaluate,round,pointer,scalar,guarded,word,AddressControl.instruction,
      AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
      Scalar.Instr.plain,Scalar.update,hc.2.1,Scalar.Compare.eval,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt colFit,Nat.mod_eq_of_lt limitFit]
  exact active _ coords

end Ptx.Scalar.Parallel.Dense
