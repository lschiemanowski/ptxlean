import PtxBinary32.CompactDenseControl

/-! Compact per-group dense scratch. Arithmetic contracts are shared with Dense;
only the fetched shared addresses and their allocation change. -/
namespace Ptx.Scalar.Parallel.Dense.Compact
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

theorem products_control_coordinates (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (seed : Scalar.State)
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

private theorem product_pointer (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (seed : Scalar.State)
    (tid : seed.regs 0=BitVec.ofNat 32 t.val) :
    (evaluate ((products s).take 20) seed).addrs 2=bytePointer (t.val%s.width) := by
  have fits := lt_trans (coordinates s t).2.1 (width_fits s b)
  have decoded := decoded_coordinates s b t
  have col := congrArg (BitVec.ofNat 32) decoded.1
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at col
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  simp [evaluate,products,pointer,scalar,guarded,word,AddressControl.instruction,
    AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,tid,col,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fits,← BitVec.ofNat_add,four]

private theorem round_pointer (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (k : Nat)
    (hk : k<s.depth) (seed : Scalar.State) (coords : ControlCoordinates s t seed) :
    (evaluate ((round s k).take 14) seed).addrs 2=bytePointer (nextIndex s k t) := by
  have fit : nextIndex s k t<4294967296 := by
    have := (round_indices s b k hk t).2.1; have := b.arithmetic; have := shared_le s t; omega
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  simp [evaluate,round,pointer,scalar,guarded,word,AddressControl.instruction,
    AddressControl.scalar,AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,
    Scalar.Instr.plain,Scalar.update,coords.2.1,Scalar.BinOp.eval,← BitVec.ofNat_add,
    show t.val%s.width+(k+1)*s.width=nextIndex s k t from rfl,
    bytePointer,BitVec.setWidth_ofNat_of_le_of_lt (by omega : 32≤64) fit,four]

private theorem output_pointer (s : Shape) (b : ArithmeticBounds s) (t : Fin s.threads) (seed : Scalar.State)
    (coords : ControlCoordinates s t seed) :
    (evaluate ((output s).take 18) seed).addrs 6=bytePointer (outputIndex s t) ∧
    (evaluate ((output s).take 18) seed).preds 0=decide (t.val%s.width=0) := by
  have fit : outputIndex s t<4294967296 := by have := (output_indices s t).2.2; have := b.arithmetic; have := shared_le s t; omega
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

theorem product_control_address (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) : (atPC (program s) (controlSeed s seeds t) 20).addrs 2=bytePointer (t.val%s.width) := by
  unfold atPC
  rw [program,List.append_assoc,List.take_append_of_le_length (show 20≤(products s).length by simp)]
  exact product_pointer s b t _ (by simp [controlSeed])

theorem round_control_address (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
    (t : Fin s.threads) (k : Nat) (hk : k<s.depth) :
    (atPC (program s) (controlSeed s seeds t) (22+16*k+14)).addrs 2=bytePointer (nextIndex s k t) := by
  rw [program_round_split s k hk]
  have len : (products s ++ (List.range k).flatMap (round s)).length=22+16*k := by
    simp [List.length_flatMap,List.sum_replicate,Nat.mul_comm]
  rw [← len,control_atPC_slice _ _ _ _ 14 (by simp),AddressControl.evaluate_append]
  exact round_pointer s b t k hk _ (rounds_control_coordinates s t _ _
    (products_control_coordinates s b t _ (by simp [controlSeed])))

theorem output_control_address (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
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
theorem round_control_active (s : Shape) (b : ArithmeticBounds s) (seeds : Fin s.threads → Scalar.State)
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
      Scalar.BinOp.eval,Scalar.Compare.eval,← BitVec.ofNat_add,show t.val%s.width+t.val%s.width+k*s.width=leftIndex s k t from rfl,
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
  have rf : rootIndex s t<2^32 := by have := b.arithmetic; have := shared_le s t; omega
  have bf : biasIndex s t<2^32 := by
    have : s.outputBase≤s.globalWords := by simp [Shape.globalWords]
    have := b.arithmetic; have := shared_le s t; omega
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have four : ∀ x : Nat, x+x+(x+x)=4*x := by intro x; omega
  have gate : (BitVec.ofNat 32 (t.val%s.width) == (BitVec.ofNat 32 0))=decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf]
  cases bias <;>
    simp [evaluate,output,pointer,scalar,guarded,word,AddressControl.instruction,AddressControl.scalar,
      AddressControl.advance,Scalar.Operand32.eval,Scalar.Operand64.eval,Scalar.Instr.plain,Scalar.update,coords.1,coords.2.1,coords.2.2,
      Scalar.BinOp.eval,Scalar.Compare.eval,← BitVec.ofNat_add,
      show t.val%s.width+s.depth*s.width=rootIndex s t from rfl,show t.val/s.width+s.biasBase=biasIndex s t from rfl,
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


end Ptx.Scalar.Parallel.Dense.Compact
