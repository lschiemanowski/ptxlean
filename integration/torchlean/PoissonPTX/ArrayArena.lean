import PoissonPTX.AssemblyPrologue
import PoissonPTX.AssemblyMask
import PoissonPTX.Sources

namespace PtxTorchLean.Poisson.PTX

/-- A nonwrapping launch over named binary64 arrays and four-byte boundary
flags. Distinct fields occupy disjoint ranges; each thread owns one word. -/
structure ArrayArena (Field : Type) (nodes : Nat) where
  (base boundary : Word)
  vector : Field → Word
  bytes : Nat
  small : nodes<2^30
  aligned : base.toNat%8=0
  noWrap : base.toNat+bytes≤2^64
  boundaryAligned : boundary.toNat%4=0
  vectorAligned : ∀ f, (vector f).toNat%8=0
  boundaryFit : boundary.toNat+nodes*4≤bytes
  vectorFit : ∀ f, (vector f).toNat+nodes*8≤bytes
  vectorApart : ∀ f g, f≠g → (vector f).toNat+nodes*8≤(vector g).toNat ∨ (vector g).toNat+nodes*8≤(vector f).toNat
  boundaryApart : ∀ f, boundary.toNat+nodes*4≤(vector f).toNat ∨ (vector f).toNat+nodes*8≤boundary.toNat

variable {Field : Type}

def ArrayArena.context (a : ArrayArena Field n) (i : Fin n) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 (i.val%256),BitVec.ofNat 32 (i.val/256)⟩
def ArrayArena.start (a : ArrayArena Field n) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩
def ArrayArena.slot (a : ArrayArena Field n) (f : Field) (i : Fin n) := a.base.toNat+(a.vector f).toNat+i.val*8

theorem ArrayArena.index (a : ArrayArena Field n) (i : Fin n) : (Kernel.Residual.index (a.context i)).toNat=i.val := by
  have hi:=i.isLt; have small:=a.small
  simp [Kernel.Residual.index,ArrayArena.context,BitVec.toNat_add,BitVec.toNat_mul]
  omega

theorem ArrayArena.live (a : ArrayArena Field n) (i : Fin n) : Kernel.Residual.live (a.context i) (BitVec.ofNat 32 n) := by
  unfold Kernel.Residual.live
  rw [a.index i]
  have small : n<2^32 := by have := a.small; omega
  change i.val<n%2^32
  rw [Nat.mod_eq_of_lt small]
  exact i.isLt

theorem ArrayArena.vector_address (a : ArrayArena Field n) (i : Fin n) (f : Field) :
    (address64 a.base (Kernel.Residual.index (a.context i)) (a.vector f)).toNat=a.slot f i := by
  rw [address64_exact _ _ _ (by rw [a.index]; have := a.vectorFit f; have := a.noWrap; have := i.isLt; omega),a.index]
  unfold ArrayArena.slot; omega

theorem ArrayArena.boundary_address (a : ArrayArena Field n) (i : Fin n) :
    (address32 a.base (Kernel.Residual.index (a.context i)) a.boundary).toNat=a.base.toNat+a.boundary.toNat+i.val*4 := by
  rw [address32_exact _ _ _ (by rw [a.index]; have := a.boundaryFit; have := a.noWrap; have := i.isLt; omega),a.index]
  omega

theorem ArrayArena.setup_address (a : ArrayArena Field n) (memory : Memory) (regs : Registers) (i : Fin n) (f : Field) :
    (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)).toNat=a.slot f i := by
  have eq : address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)=
      address64 a.base (Kernel.Residual.index (a.context i)) (a.vector f) := by
    simp [address,wide,Assembly.setup,address64,BitVec.toNat_setWidth,ArrayArena.context]
    change BitVec.ofNat 64 (((Kernel.Residual.index (a.context i)).toNat % 2^32)*8)=
      BitVec.ofNat 64 ((Kernel.Residual.index (a.context i)).toNat*8)
    rw [Nat.mod_eq_of_lt (Kernel.Residual.index (a.context i)).isLt]
  rw [eq,a.vector_address]

theorem ArrayArena.setup_boundary (a : ArrayArena Field n) (memory : Memory) (regs : Registers) (i : Fin n) :
    (Assembly.maskAddress (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.boundary).toNat=
      a.base.toNat+a.boundary.toNat+i.val*4 := by
  have eq : Assembly.maskAddress (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.boundary=
      address32 a.base (Kernel.Residual.index (a.context i)) a.boundary := by
    simp [Assembly.maskAddress,Assembly.setup,ArrayArena.context,Kernel.u32]
  rw [eq,a.boundary_address]

theorem ArrayArena.owners (a : ArrayArena Field n) (f g : Field) (i j : Fin n) (different : f≠g ∨ i≠j) :
    Sources.Disjoint (a.slot f i) (a.slot g j) := by
  classical
  unfold Sources.Disjoint ArrayArena.slot
  by_cases same : f=g
  · subst g
    have different : i.val≠j.val := by
      intro eq; rcases different with h|h; exact h rfl; exact h (Fin.ext eq)
    omega
  · have apart := a.vectorApart f g same
    have hi := i.isLt; have hj := j.isLt; omega

theorem ArrayArena.boundary_disjoint (a : ArrayArena Field n) (f : Field) (i j : Fin n) :
    a.slot f i+8≤a.base.toNat+a.boundary.toNat+j.val*4 ∨ a.base.toNat+a.boundary.toNat+j.val*4+4≤a.slot f i := by
  have apart := a.boundaryApart f; have hi := i.isLt; have hj := j.isLt
  unfold ArrayArena.slot; omega

theorem ArrayArena.overlap_owner (a : ArrayArena Field n) (f g : Field) (i j : Fin n) (k l : Fin 8)
    (overlap : a.slot f i+k.val=a.slot g j+l.val) : f=g ∧ i=j := by
  classical
  by_cases same : f=g ∧ i=j
  · exact same
  · have apart := a.owners f g i j (by tauto)
    have hk := k.isLt; have hl := l.isLt
    unfold Sources.Disjoint at apart; omega

end PtxTorchLean.Poisson.PTX
