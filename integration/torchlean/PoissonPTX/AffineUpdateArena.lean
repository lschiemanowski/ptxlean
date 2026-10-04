import PoissonPTX.AffineUpdateEntry
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

/-- Actual in-place direction layout: one coefficient and two arrays of
binary64 words. Separation concerns storage, not numerical input values. -/
structure Arena (nodes : Nat) where
  (base coefficient direction shift : Word)
  bytes : Nat
  small : nodes<2^30
  aligned : base.toNat%8=0
  noWrap : base.toNat+bytes≤2^64
  coefficientAligned : coefficient.toNat%8=0
  directionAligned : direction.toNat%8=0
  shiftAligned : shift.toNat%8=0
  coefficientFit : coefficient.toNat+8≤bytes
  directionFit : direction.toNat+nodes*8≤bytes
  shiftFit : shift.toNat+nodes*8≤bytes
  coefficientApart : coefficient.toNat+8≤direction.toNat ∨ direction.toNat+nodes*8≤coefficient.toNat
  shiftApart : shift.toNat+nodes*8≤direction.toNat ∨ direction.toNat+nodes*8≤shift.toNat

def Arena.context (a : Arena n) (i : Fin n) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 (i.val%256),BitVec.ofNat 32 (i.val/256)⟩

def Arena.start (a : Arena n) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩

def Arena.program (a : Arena n) := entry (BitVec.ofNat 32 n) a.coefficient a.direction a.shift a.direction

def Arena.slot (a : Arena n) (i : Fin n) := a.base.toNat+a.direction.toNat+i.val*8

def Arena.value (a : Arena n) (memory : Memory) (i : Fin n) : Float :=
  decode (read64 memory (a.base.toNat+a.shift.toNat+i.val*8))+
    decode (read64 memory (a.base.toNat+a.coefficient.toNat))*decode (read64 memory (a.slot i))

theorem Arena.index (a : Arena n) (i : Fin n) : (Kernel.Residual.index (a.context i)).toNat=i.val := by
  have hi:=i.isLt; have small:=a.small
  simp [Kernel.Residual.index,Arena.context,BitVec.toNat_add,BitVec.toNat_mul]
  omega

theorem Arena.live (a : Arena n) (i : Fin n) : Kernel.Residual.live (a.context i) (BitVec.ofNat 32 n) := by
  unfold Kernel.Residual.live
  rw [a.index i]
  have small : n<2^32 := by have := a.small; omega
  change i.val<n%2^32
  rw [Nat.mod_eq_of_lt small]
  exact i.isLt

theorem Arena.scalar_address (a : Arena n) : (a.base+a.coefficient).toNat=a.base.toNat+a.coefficient.toNat := by
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt]
  have := a.coefficientFit; have := a.noWrap; omega

theorem Arena.vector_address (a : Arena n) (i : Fin n) (field : Word) (fit : field.toNat+n*8≤a.bytes) :
    (address64 a.base (Kernel.Residual.index (a.context i)) field).toNat=a.base.toNat+field.toNat+i.val*8 := by
  rw [address64_exact _ _ _ (by rw [a.index]; have := a.noWrap; have := i.isLt; omega),a.index]
  omega

theorem Arena.setup_address (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (field : Word) (fit : field.toNat+n*8≤a.bytes) :
    (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 field).toNat=
      a.base.toNat+field.toNat+i.val*8 := by
  have eq : address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 field=
      address64 a.base (Kernel.Residual.index (a.context i)) field := by
    simp [address,wide,Assembly.setup,address64,BitVec.toNat_setWidth,Arena.context]
    change BitVec.ofNat 64 (((Kernel.Residual.index (a.context i)).toNat % 2^32)*8)=
      BitVec.ofNat 64 ((Kernel.Residual.index (a.context i)).toNat*8)
    rw [Nat.mod_eq_of_lt (Kernel.Residual.index (a.context i)).isLt]
  rw [eq,a.vector_address i field fit]

theorem Arena.vector_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (field : Word) (fit : field.toNat+n*8≤a.bytes) (aligned : field.toNat%8=0) :
    Valid64 a.base.toNat a.bytes
      (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 field).toNat := by
  rw [a.setup_address memory regs i field fit]
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · simp [Nat.add_mod,a.aligned,aligned]
  · have := i.isLt; omega

theorem Arena.owners (a : Arena n) (i j : Fin n) (different : i≠j) : Sources.Disjoint (a.slot i) (a.slot j) := by
  have different : i.val≠j.val := fun eq => different (Fin.ext eq)
  unfold Sources.Disjoint Arena.slot
  omega

end PtxTorchLean.Poisson.PTX.AffineUpdate
