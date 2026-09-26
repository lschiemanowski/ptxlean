import PtxBinary32.DenseData

namespace Ptx.Scalar.Parallel.Dense
open Ptx.Binary32
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem product_scalar_data (s : Shape) (b : Bounds s) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence)
    (data : Data s global t a)
    (fetch : (products s)[a.pc]?=some (.localStep i) ∨ ∃ space, (products s)[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global t occ.pc effect.value) :
    Data s global t next := by
  have bound : a.pc<22 := by
    rcases fetch with h | ⟨_,h⟩ <;> simpa using (List.getElem?_eq_some_iff.mp h).choose
  rcases data with ⟨tid,col,pg,inp,wei,prod,rg,left,right,red,og,root,bias,aff,sign,out⟩
  have decoded := decoded_coordinates s b t
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have nf : s.columns<4294967296 := lt_of_le_of_lt s.padded (width_fits s b)
  have columnBits : Scalar.BinOp.eval .and (BitVec.ofNat 32 t.val) (BitVec.ofNat 32 (s.width-1)) = BitVec.ofNat 32 (t.val%s.width) := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf] using decoded.1
  interval_cases pc : a.pc
  all_goals simp only [products,pointer,scalar,guarded,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_append,pc] at fetch
  all_goals simp at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : a.preds 0 <;> simp [enabled] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,pc,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply col; omega) | (apply pg <;> omega) | (apply inp <;> omega) | (apply wei <;> omega) | (apply prod <;> omega) | skip

  all_goals simp_all [operands,ReadData,Scalar.occurrence,Scalar.Compare.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt nf]

  all_goals simp [show ¬t.val%s.width<s.columns by omega]

theorem round_scalar_data (s : Shape) (b : Bounds s) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (k j : Nat) (hk : k<s.depth) (hj : j<16)
    (site : a.pc=22+16*k+j) (data : Data s global t a)
    (fetch : (round s k)[j]?=some (.localStep i) ∨ ∃ space, (round s k)[j]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global t occ.pc effect.value) :
    Data s global t next := by
  have columnNow := data.column (by omega : 1≤a.pc)
  have current : 1≤j → a.preds 0=decide (t.val%s.width<2^(s.depth-(k+1))) := fun h => data.roundGate k hk (by omega) (by omega)
  rcases data with ⟨tid,col,pg,inp,wei,prod,rg,left,right,red,og,root,bias,aff,sign,out⟩
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have nf : 2^(s.depth-(k+1))<4294967296 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits s b)
  interval_cases jp : j
  all_goals try simp only [jp] at current
  all_goals simp [round,pointer,scalar,guarded] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : a.preds 0 <;> simp [enabled] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals try have gateValue : a.preds 0=decide (t.val%s.width<2^(s.depth-(k+1))) := rg k hk (by omega) (by omega)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,site,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply col; omega) | (apply rg <;> omega) | (apply left <;> omega) | (apply right <;> omega) | (apply red <;> omega) | skip

  all_goals simp_all [ReadData,Scalar.occurrence,Scalar.Compare.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt nf]
  all_goals first
    | (rename_i phase h lo hi; have eq : phase=k := (by omega); subst phase; rfl)
    | (grind)


theorem output_scalar_data (s : Shape) (b : Bounds s) (global : List Word) (t : Fin s.threads)
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (j : Nat) (hj : j<20)
    (site : a.pc=22+16*s.depth+j) (data : Data s global t a)
    (fetch : (output s)[j]?=some (.localStep i) ∨ ∃ space, (output s)[j]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData s global t occ.pc effect.value) :
    Data s global t next := by
  have columnNow := data.column (by omega : 1≤a.pc)
  have current : 1≤j → a.preds 0=decide (t.val%s.width=0) := fun h => data.outputGate (by omega) (by omega)
  have relu : j=13 → t.val%s.width=0 → Output s global (t.val/s.width) (if a.preds 1 then 0 else a.regs 6) := by
    intro at13 leader
    obtain ⟨dot,hd,ha⟩ := data.affine (by omega) (by omega) leader
    refine ⟨dot,a.regs 6,hd,ha,?_⟩
    rw [data.sign (by omega)]
    simpa using relu_bits (a.regs 6)
  rcases data with ⟨tid,col,pg,inp,wei,prod,rg,left,right,red,og,root,bias,aff,sign,out⟩
  have cf : t.val%s.width<4294967296 := lt_trans (coordinates s t).2.1 (width_fits s b)
  have iszero : (BitVec.ofNat 32 (t.val%s.width) == (0 : Word))=decide (t.val%s.width=0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h; have eq := congrArg BitVec.toNat h; simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf] using eq
    · intro h; simp [h]
  interval_cases j
  all_goals simp [output,pointer,scalar,guarded] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : a.preds 0 <;> simp [enabled] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,site,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply col; omega) | (apply og <;> omega) | (apply root <;> omega) | (apply aff <;> omega) | (apply out <;> omega) | skip
  all_goals simp_all [ReadData,Scalar.occurrence,Scalar.Compare.eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt cf,iszero]
  all_goals grind

end Ptx.Scalar.Parallel.Dense
