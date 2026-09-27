import PtxBinary32.MaximumData
namespace Ptx.Scalar.Parallel.Maximum
open Ptx.Binary32.Maximum
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
theorem publish_scalar_data (d : Nat) (b : Bounds d) (global : List Word) (t : Fin (width d))
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence)
    (data : Data d global t a)
    (fetch : publish[a.pc]?=some (.localStep i) ∨ ∃ space, publish[a.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData d global t occ.pc effect.value) :
    Data d global t next := by
  have bound : a.pc<6 := by
    rcases fetch with h | ⟨_,h⟩ <;> simpa using (List.getElem?_eq_some_iff.mp h).choose
  rcases data with ⟨tid,pub,rg,left,right,ls,lr,lk,rs,rr,rk,cmp,sl,red,og,root⟩
  interval_cases pc : a.pc
  all_goals simp [publish,publishCode,Dense.pointer,Dense.scalar,Dense.guarded,pc] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Dense.word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : a.preds 0 <;> simp [enabled] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,pc,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply pub <;> omega) | skip
  all_goals simp_all [ReadData,Scalar.occurrence]

theorem round_scalar_data (d : Nat) (b : Bounds d) (global : List Word) (t : Fin (width d))
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (k j : Nat) (hk : k<d) (hj : j<24)
    (site : a.pc=6+24*k+j) (data : Data d global t a)
    (fetch : (round d k)[j]?=some (.localStep i) ∨ ∃ space, (round d k)[j]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData d global t occ.pc effect.value) :
    Data d global t next := by
  have current : 1≤j → a.preds 0=decide (t.val<2^(d-(k+1))) := fun h => data.roundGate k hk (by omega) (by omega)
  rcases data with ⟨tid,pub,rg,left,right,ls,lr,lk,rs,rr,rk,cmp,sl,red,og,root⟩
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have nf : 2^(d-(k+1))<4294967296 := lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.sub_le _ _)) (width_fits b)
  interval_cases jp : j
  all_goals try simp only [jp] at current
  all_goals simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,Dense.pointer,Dense.scalar,Dense.guarded] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Dense.word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals simp [Scalar.Guard.eval] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,site,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply pub <;> omega) | (apply rg <;> omega) | (apply left <;> omega) | (apply right <;> omega) | (apply ls <;> omega) | (apply lr <;> omega) | (apply lk <;> omega) | (apply rs <;> omega) | (apply rr <;> omega) | (apply rk <;> omega) | (apply cmp <;> omega) | (apply sl <;> omega) | (apply red <;> omega) | (apply og <;> omega) | (apply root <;> omega) | skip
  all_goals simp_all [ReadData,Scalar.occurrence,Scalar.Compare.eval,Scalar.BinOp.eval,word,Dense.word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf,Nat.mod_eq_of_lt nf]
  case «0».roundGate =>
    rename_i phase ph lo hi
    have eq : phase=k := by omega
    subst phase
    rfl
  case h_2.left =>
    rename_i phase ph lo hi active
    have eq : phase=k := by omega
    subst phase
    exact reads.1 k hk rfl
  case «7».isFalse.left =>
    rename_i phase guardValue ph lo hi active
    have eq : phase=k := by omega
    subst phase
    have inactive := rg k hk (by omega) (by omega)
    omega
  case h_2.right =>
    rename_i phase ph lo hi active
    have eq : phase=k := by omega
    subst phase
    exact reads.2.1 k hk rfl
  case «8».isFalse.right =>
    rename_i phase guardValue ph lo hi active
    have eq : phase=k := by omega
    subst phase
    have inactive := rg k hk (by omega) (by omega)
    omega
  case «11».isTrue.leftKey =>
    have sign := ls k hk (by omega) (by omega)
    simp [key, sign]
  case «11».isFalse.leftKey =>
    have sign := ls k hk (by omega) (by omega)
    rw [lr k hk rfl]
    simp [key, Nat.not_le.mpr sign]
  case «14».isTrue.rightKey =>
    have sign := rs k hk (by omega) (by omega)
    simp [key, sign]
  case «14».isFalse.rightKey =>
    have sign := rs k hk (by omega) (by omega)
    rw [rr k hk rfl]
    simp [key, Nat.not_le.mpr sign]
  case «15».compare =>
    rw [lk k hk (by omega) (by omega), rk k hk (by omega) (by omega)]
  case «17».isTrue.reduced =>
    rename_i phase guardValue ph lo hi active
    have eq : phase=k := by omega
    subst phase
    have leftValue := left k hk (by omega) (by omega) active
    have rightValue := right k hk (by omega) (by omega) active
    have comparison := cmp k hk (by omega) (by omega)
    change a.regs 5 = choose (node global k (2*t.val)) (node global k (2*t.val+1))
    rw [←leftValue, ←rightValue]
    simp [choose, comparison]
  case «17».isFalse.reduced =>
    rename_i phase guardValue ph lo hi active
    have eq : phase=k := by omega
    subst phase
    have leftValue := left k hk (by omega) (by omega) active
    have rightValue := right k hk (by omega) (by omega) active
    have comparison := cmp k hk (by omega) (by omega)
    rw [sl k hk rfl]
    change a.regs 4 = choose (node global k (2*t.val)) (node global k (2*t.val+1))
    rw [←leftValue, ←rightValue]
    simp [choose, Nat.not_lt.mpr comparison]


theorem output_scalar_data (d : Nat) (b : Bounds d) (global : List Word) (t : Fin (width d))
    (a next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence) (j : Nat) (hj : j<12)
    (site : a.pc=6+24*d+j) (data : Data d global t a)
    (fetch : (output d)[j]?=some (.localStep i) ∨ ∃ space, (output d)[j]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i a=.next next occ)
    (reads : ∀ effect, occ.memory=some effect → effect.kind=.load → ReadData d global t occ.pc effect.value) :
    Data d global t next := by
  have current : 1≤j → a.preds 0=decide (t.val=0) := fun h => data.outputGate (by omega) (by omega)
  rcases data with ⟨tid,pub,rg,left,right,ls,lr,lk,rs,rr,rk,cmp,sl,red,og,root⟩
  have tf : t.val<4294967296 := lt_trans t.isLt (width_fits b)
  have iszero : (BitVec.ofNat 32 t.val == (0 : Word))=decide (t.val=0) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf]
  interval_cases j
  all_goals simp [output,outputCode,Dense.pointer,Dense.scalar,Dense.guarded] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,word,Dense.word,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : a.preds 0 <;> simp [enabled] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals first | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated) | (obtain ⟨rfl,rfl⟩ := evaluated)
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,site,ite_apply,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply og <;> omega) | (apply root <;> omega) | skip
  all_goals simp_all [ReadData,Scalar.occurrence,Scalar.Compare.eval,word,Dense.word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt tf,iszero]
end Ptx.Scalar.Parallel.Maximum
