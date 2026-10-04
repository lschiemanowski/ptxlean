import PoissonPTX.ArrayArena

namespace PtxTorchLean.Poisson.PTX
variable {Field : Type}

theorem ArrayArena.vector_valid (a : ArrayArena Field n) (memory : Memory) (regs : Registers) (i : Fin n) (f : Field) :
    Valid64 a.base.toNat a.bytes
      (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)).toNat := by
  rw [a.setup_address]
  unfold ArrayArena.slot
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · simp [Nat.add_mod,a.aligned,a.vectorAligned]
  · have := a.vectorFit f; have := i.isLt; omega

theorem ArrayArena.boundary_valid (a : ArrayArena Field n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Valid32 a.base.toNat a.bytes
      (Assembly.maskAddress (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core a.boundary).toNat := by
  rw [a.setup_boundary]
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · have base4 : a.base.toNat%4=0 := by have := a.aligned; omega
    simp [Nat.add_mod,base4,a.boundaryAligned]
  · have := a.boundaryFit; have := i.isLt; omega

end PtxTorchLean.Poisson.PTX
