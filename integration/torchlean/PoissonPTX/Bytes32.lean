import PoissonPTX.Bytes

namespace PtxTorchLean.Poisson.PTX

/-- Connectivity and CSR index arrays use four little-endian bytes. -/
def read32 (m : Memory) (a : Nat) : BitVec 32 :=
  m (a+3) ++ m (a+2) ++ m (a+1) ++ m a

def write32 (m : Memory) (a : Nat) (w : BitVec 32) : Memory :=
  fun p => if a≤p ∧ p<a+4 then w.extractLsb' (8*(p-a)) 8 else m p

def Valid32 (start bytes address : Nat) : Prop :=
  start≤address ∧ address%4=0 ∧ address+4≤start+bytes ∧ start+bytes≤2^64

instance : Decidable (Valid32 start bytes address) := by unfold Valid32; infer_instance

@[simp] theorem write32_at (m : Memory) (a : Nat) (w : BitVec 32) (i : Nat) (small : i<4) :
    write32 m a w (a+i)=w.extractLsb' (8*i) 8 := by simp [write32]; omega

theorem write32_outside (m : Memory) (a : Nat) (w : BitVec 32) (p : Nat)
    (outside : p<a ∨ a+4≤p) : write32 m a w p=m p := by simp [write32]; omega

@[simp] theorem read32_write32 (m : Memory) (a : Nat) (w : BitVec 32) :
    read32 (write32 m a w) a=w := by
  have first : write32 m a w a=w.extractLsb' 0 8 := by simpa using write32_at m a w 0 (by decide)
  simp only [read32]
  rw [write32_at m a w 3 (by decide),write32_at m a w 2 (by decide),
    write32_at m a w 1 (by decide),first]
  bv_decide

/-- A neighboring four-byte index is unaffected, even though its enclosing
aligned eight-byte word contains both entries. -/
theorem read32_write32_disjoint (m : Memory) (a b : Nat) (w : BitVec 32)
    (apart : a+4≤b ∨ b+4≤a) : read32 (write32 m a w) b=read32 m b := by
  have keep (i : Nat) (hi : i<4) : write32 m a w (b+i)=m (b+i) :=
    write32_outside _ _ _ _ (by omega)
  simp only [read32]
  rw [keep 3 (by decide),keep 2 (by decide),keep 1 (by decide),
    show write32 m a w b=m b from by simpa using keep 0 (by decide)]

theorem read32_write64_disjoint (m : Memory) (a b : Nat) (w : Word)
    (apart : a+8≤b ∨ b+4≤a) : read32 (write64 m a w) b=read32 m b := by
  have keep (i : Nat) (hi : i<4) : write64 m a w (b+i)=m (b+i) :=
    write64_outside _ _ _ _ (by omega)
  simp only [read32]
  rw [keep 3 (by decide),keep 2 (by decide),keep 1 (by decide),
    show write64 m a w b=m b from by simpa using keep 0 (by decide)]

/-- Actual unsigned widening multiply, followed by two modular additions. -/
def address32 (base : Word) (index : BitVec 32) (offset : Word) : Word :=
  base+BitVec.ofNat 64 (index.toNat*4)+offset

theorem address32_exact (base : Word) (index : BitVec 32) (offset : Word)
    (bound : base.toNat+index.toNat*4+offset.toNat<2^64) :
    (address32 base index offset).toNat=base.toNat+index.toNat*4+offset.toNat := by
  have small : index.toNat*4<2^64 := by have := index.isLt; omega
  have first : base.toNat+index.toNat*4<2^64 := by omega
  simp only [address32,BitVec.toNat_add,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt first,Nat.mod_eq_of_lt bound]

theorem valid32_of_array (base offset : Word) (count bytes : Nat) (index : BitVec 32)
    (baseAligned : base.toNat%4=0) (offsetAligned : offset.toNat%4=0)
    (inside : index.toNat<count) (extent : offset.toNat+count*4≤bytes)
    (nowrap : base.toNat+bytes≤2^64) :
    Valid32 base.toNat bytes (address32 base index offset).toNat := by
  have bound : base.toNat+index.toNat*4+offset.toNat<2^64 := by omega
  rw [address32_exact _ _ _ bound]
  refine ⟨by omega,?_,by omega,nowrap⟩
  simp [Nat.add_mod,baseAligned,offsetAligned]

end PtxTorchLean.Poisson.PTX
