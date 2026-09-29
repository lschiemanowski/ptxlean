import PoissonPTX.CellFinalTensor

namespace PtxTorchLean.Poisson.PTX.CellFinal
open Contraction

/-- Four whole allocated operand matrices discharge every individual load's
bounds. Conditions concern storage and coordinates, not numerical answers. -/
theorem inputs_of_matrices (s : State) (hi : width≤5) (b d : Word)
    (row : (s.regs 16).toNat<width) (col : (s.regs 17).toNat<width)
    (global : (s.regs 0).toNat = s.globalStart) (shared : (s.regs 3).toNat = s.sharedStart)
    (ga : s.globalStart%8=0) (sa : s.sharedStart%8=0)
    (ba : b.toNat%8=0) (da : d.toNat%8=0)
    (bf : b.toNat+width*width*8≤s.globalBytes) (df : d.toNat+width*width*8≤s.globalBytes)
    (sf : 7*width*width*8≤s.sharedBytes)
    (gn : s.globalStart+s.globalBytes≤2^64) (sn : s.sharedStart+s.sharedBytes≤2^64) :
    Inputs s width b d := by
  intro k hk
  have ks : (BitVec.ofNat 64 k).toNat=k := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have plane (p : Nat) (hp : p=5 ∨ p=6) : Valid s width k (left width p) := by
    have off : p*width*width*8<2^64 := by rcases hp with rfl|rfl <;> interval_cases width <;> decide
    apply valid_of_matrix s width k (left width p) hi row (by simpa [left,Coord.operand,Operand.eval,ks] using hk) shared sa
    · simp [left,BitVec.toNat_ofNat,Nat.mul_mod]
    · change (BitVec.ofNat 64 (p*width*width*8)).toNat+width*width*8≤s.sharedBytes
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt off]
      rcases hp with rfl|rfl <;> nlinarith
    · exact sn
  have coeff (off : Word) (aligned : off.toNat%8=0) (fits : off.toNat+width*width*8≤s.globalBytes) :
      Valid s width k (right off) := by
    exact valid_of_matrix s width k (right off) hi (by simpa [right,Coord.operand,Operand.eval,ks] using hk) col global ga aligned fits gn
  exact ⟨⟨plane 5 (Or.inl rfl),coeff d da df⟩,⟨plane 6 (Or.inr rfl),coeff b ba bf⟩⟩

theorem index_exact (s : State) (hi : width≤5)
    (bound : (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32) :
    (index s width).toNat=(s.regs 15).toNat*(width*width)+(s.regs 14).toNat := by
  have ww : width*width<2^32 := by nlinarith
  have lane : (s.regs 14).toNat<2^32 := by omega
  have prod : (s.regs 15).toNat*(width*width)<2^32 := by omega
  simp only [index,Kernel.u32,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  norm_num at bound ww lane prod ⊢
  exact bound

theorem location_exact (s : State) (hi : width≤5)
    (bound : (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32)
    (nowrap : (s.regs 0).toNat+((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*8+output.toNat<2^64) :
    (location s width output).toNat=
      (s.regs 0).toNat+((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*8+output.toNat := by
  have idx := index_exact s hi bound
  have small := (index s width).isLt
  have eq : location s width output=address64 (s.regs 0) (index s width) output := by
    simp [location,indexed,address,PTX.wide,assign,PTX.advance,address64,
      BitVec.toNat_setWidth,Nat.mod_eq_of_lt small]
  rw [eq,address64_exact _ _ _ (by simpa [idx] using nowrap),idx]

/-- A complete output extent supplies alignment, allocation and nonwrapping
conditions for the actual integer multiply-add and address instructions. -/
theorem output_valid (s : State) (hi : width≤5)
    (bound : (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32)
    (base : (s.regs 0).toNat=s.globalStart) (aligned : s.globalStart%8=0) (oa : output.toNat%8=0)
    (fits : ((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*8+output.toNat+8≤s.globalBytes)
    (nowrap : s.globalStart+s.globalBytes≤2^64) :
    Valid64 s.globalStart s.globalBytes (location s width output).toNat := by
  rw [location_exact s hi bound (by rw [base]; omega),base]
  exact ⟨by omega,by simp [Nat.add_mod,aligned,oa],by omega,nowrap⟩

end PtxTorchLean.Poisson.PTX.CellFinal
