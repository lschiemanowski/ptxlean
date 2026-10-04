import PoissonPTX.DotInputLoop

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- Layout facts about two actual contiguous input fields in one byte arena.
Fields may coincide (a self-dot-product); no output is written by this loop. -/
def Arrays (s : State) (count : Nat) (left right : Word) : Prop :=
  s.globalStart=(s.regs 0).toNat ∧ (s.regs 0).toNat%8=0 ∧
  s.globalStart+s.globalBytes≤2^64 ∧
  (∀ off∈[left,right], off.toNat%8=0 ∧ off.toNat+count*8≤s.globalBytes)

theorem address_at (bounded : count<2^30) (inside : index<count)
    (space : (s.regs 0).toNat+count*8+off.toNat≤2^64) :
    (address (atCursor s index) 12 off).toNat=(s.regs 0).toNat+index*8+off.toNat := by
  have low : index<4294967296 := by omega
  have indexFits : index<18446744073709551616 := by omega
  have scaled : index*8<18446744073709551616 := by omega
  have base : (s.regs 0).toNat+index*8<18446744073709551616 := by omega
  have total : (s.regs 0).toNat+index*8+off.toNat<18446744073709551616 := by omega
  simp [address,wide,atCursor,Function.update_self,
    BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt low,Nat.mod_eq_of_lt indexFits,
    Nat.mod_eq_of_lt scaled,Nat.mod_eq_of_lt base,Nat.mod_eq_of_lt total]

theorem arrays_valid (arrays : Arrays s count left right) (bounded : count<2^30)
    (inside : index<count) : Valid (atCursor s index) left right := by
  have field (off : Word) (member : off∈[left,right]) :
      Valid64 s.globalStart s.globalBytes (address (atCursor s index) 12 off).toNat := by
    have alignment := (arrays.2.2.2 off member).1
    have extent := (arrays.2.2.2 off member).2
    have noWrap : (s.regs 0).toNat+count*8+off.toNat≤2^64 := by
      have room := arrays.2.2.1
      rw [arrays.1] at room; omega
    rw [address_at bounded inside noWrap]
    refine ⟨by rw [arrays.1]; omega,?_,by rw [arrays.1]; omega,arrays.2.2.1⟩
    simp [Nat.add_mod,arrays.2.1,alignment]
  exact ⟨field left (by simp),field right (by simp)⟩

def element (s : State) (off : Word) (index : Nat) : Float :=
  decode (read64 s.global ((s.regs 0).toNat+index*8+off.toNat))

theorem contribution_array (arrays : Arrays s count left right) (bounded : count<2^30)
    (inside : index<count) :
    contribution s left right index=element s left index*element s right index := by
  have location off (member : off∈[left,right]) := address_at (s:=s) bounded inside
    (show (s.regs 0).toNat+count*8+off.toNat≤2^64 from by
      have room := arrays.2.2.1
      have extent := (arrays.2.2.2 off member).2
      rw [arrays.1] at room; omega)
  simp only [contribution,product,atCursor]
  change decode (read64 s.global (address (atCursor s index) 12 left).toNat) *
    decode (read64 s.global (address (atCursor s index) 12 right).toNat)=_
  rw [location left (by simp),location right (by simp)]
  rfl

end PtxTorchLean.Poisson.PTX.DotInput
