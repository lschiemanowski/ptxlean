import PoissonPTX.UpdateXRZExists

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

inductive Field where
  | p | x | ap | r | diagonal | z
  deriving DecidableEq, Repr

/-- Physical launch and array geometry. Inputs and outputs are distinct fields;
x and r each reuse their own initial storage. Boundary flags occupy four bytes. -/
structure Arena (nodes : Nat) where
  (base alpha boundary : Word)
  vector : Field → Word
  bytes : Nat
  small : nodes<2^30
  aligned : base.toNat%8=0
  noWrap : base.toNat+bytes≤2^64
  alphaAligned : alpha.toNat%8=0
  boundaryAligned : boundary.toNat%4=0
  vectorAligned : ∀ f, (vector f).toNat%8=0
  alphaFit : alpha.toNat+8≤bytes
  boundaryFit : boundary.toNat+nodes*4≤bytes
  vectorFit : ∀ f, (vector f).toNat+nodes*8≤bytes
  vectorApart : ∀ f g, f≠g → (vector f).toNat+nodes*8≤(vector g).toNat ∨ (vector g).toNat+nodes*8≤(vector f).toNat
  alphaApart : ∀ f, alpha.toNat+8≤(vector f).toNat ∨ (vector f).toNat+nodes*8≤alpha.toNat
  boundaryApart : ∀ f, boundary.toNat+nodes*4≤(vector f).toNat ∨ (vector f).toNat+nodes*8≤boundary.toNat

def Arena.context (a : Arena n) (i : Fin n) : Kernel.Context :=
  ⟨a.base,BitVec.ofNat 32 (i.val%256),BitVec.ofNat 32 (i.val/256)⟩
def Arena.start (a : Arena n) (memory : Memory) (regs : Registers) : Flow.State :=
  ⟨{pc:=0,regs:=regs,global:=memory,shared:=fun _ => 0,globalStart:=a.base.toNat,
    globalBytes:=a.bytes,sharedStart:=0,sharedBytes:=0},fun _ => false,false⟩
def Arena.program (a : Arena n) := entry (BitVec.ofNat 32 n) a.alpha (a.vector .p) (a.vector .x)
  (a.vector .ap) (a.vector .r) (a.vector .diagonal) a.boundary (a.vector .z)
def Arena.slot (a : Arena n) (f : Field) (i : Fin n) := a.base.toNat+(a.vector f).toNat+i.val*8

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

theorem Arena.scalar_address (a : Arena n) : (a.base+a.alpha).toNat=a.base.toNat+a.alpha.toNat := by
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt]
  have := a.alphaFit; have := a.noWrap; omega

theorem Arena.vector_address (a : Arena n) (i : Fin n) (f : Field) :
    (address64 a.base (Kernel.Residual.index (a.context i)) (a.vector f)).toNat=a.slot f i := by
  rw [address64_exact _ _ _ (by rw [a.index]; have := a.vectorFit f; have := a.noWrap; have := i.isLt; omega),a.index]
  unfold Arena.slot; omega

theorem Arena.boundary_address (a : Arena n) (i : Fin n) :
    (address32 a.base (Kernel.Residual.index (a.context i)) a.boundary).toNat=a.base.toNat+a.boundary.toNat+i.val*4 := by
  rw [address32_exact _ _ _ (by rw [a.index]; have := a.boundaryFit; have := a.noWrap; have := i.isLt; omega),a.index]
  omega

theorem Arena.setup_address (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) (f : Field) :
    (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)).toNat=a.slot f i := by
  have eq : address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)=
      address64 a.base (Kernel.Residual.index (a.context i)) (a.vector f) := by
    simp [address,wide,Assembly.setup,address64,BitVec.toNat_setWidth,Arena.context]
    change BitVec.ofNat 64 (((Kernel.Residual.index (a.context i)).toNat % 2^32)*8)=
      BitVec.ofNat 64 ((Kernel.Residual.index (a.context i)).toNat*8)
    rw [Nat.mod_eq_of_lt (Kernel.Residual.index (a.context i)).isLt]
  rw [eq,a.vector_address]

theorem Arena.setup_boundary (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    (Assembly.maskAddress (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.boundary).toNat=
      a.base.toNat+a.boundary.toNat+i.val*4 := by
  have eq : Assembly.maskAddress (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.boundary=
      address32 a.base (Kernel.Residual.index (a.context i)) a.boundary := by
    simp [Assembly.maskAddress,Assembly.setup,Arena.context,Kernel.u32]
  rw [eq,a.boundary_address]

theorem Arena.owners (a : Arena n) (f g : Field) (i j : Fin n) (different : f≠g ∨ i≠j) :
    Sources.Disjoint (a.slot f i) (a.slot g j) := by
  unfold Sources.Disjoint Arena.slot
  by_cases same : f=g
  · subst g
    have different : i.val≠j.val := by
      intro eq; rcases different with h|h; exact h rfl; exact h (Fin.ext eq)
    omega
  · have apart := a.vectorApart f g same
    have hi := i.isLt; have hj := j.isLt; omega

theorem Arena.alpha_disjoint (a : Arena n) (f : Field) (i : Fin n) :
    Sources.Disjoint (a.slot f i) (a.base.toNat+a.alpha.toNat) := by
  have apart := a.alphaApart f; have hi := i.isLt
  unfold Sources.Disjoint Arena.slot; omega

theorem Arena.boundary_disjoint (a : Arena n) (f : Field) (i j : Fin n) :
    a.slot f i+8≤a.base.toNat+a.boundary.toNat+j.val*4 ∨ a.base.toNat+a.boundary.toNat+j.val*4+4≤a.slot f i := by
  have apart := a.boundaryApart f; have hi := i.isLt; have hj := j.isLt
  unfold Arena.slot; omega

theorem Arena.overlap_owner (a : Arena n) (f g : Field) (i j : Fin n) (k l : Fin 8)
    (overlap : a.slot f i+k.val=a.slot g j+l.val) : f=g ∧ i=j := by
  by_cases same : f=g ∧ i=j
  · exact same
  · have apart := a.owners f g i j (by tauto)
    have hk := k.isLt; have hl := l.isLt
    unfold Sources.Disjoint at apart; omega

end PtxTorchLean.Poisson.PTX.UpdateXRZ
