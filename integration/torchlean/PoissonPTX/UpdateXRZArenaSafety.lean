import PoissonPTX.UpdateXRZArena

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

theorem Arena.vector_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) (f : Field) :
    Valid64 a.base.toNat a.bytes
      (address (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core 12 (a.vector f)).toNat := by
  rw [a.setup_address]
  unfold Arena.slot
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · simp [Nat.add_mod,a.aligned,a.vectorAligned]
  · have := a.vectorFit f; have := i.isLt; omega

theorem Arena.local_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Valid (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core
      a.alpha (a.vector .p) (a.vector .x) (a.vector .ap) (a.vector .r) (a.vector .diagonal) a.boundary (a.vector .z) := by
  constructor
  · change Valid64 a.base.toNat a.bytes (a.base+a.alpha).toNat
    rw [a.scalar_address]
    refine ⟨by omega,?_,?_,a.noWrap⟩
    · simp [Nat.add_mod,a.aligned,a.alphaAligned]
    · have := a.alphaFit; omega
  constructor
  · intro field member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h <;> subst field
    all_goals exact a.vector_valid memory regs i _
  · rw [a.setup_boundary]
    change Valid32 a.base.toNat a.bytes _
    refine ⟨by omega,?_,?_,a.noWrap⟩
    · have base4 : a.base.toNat%4=0 := by have := a.aligned; omega
      simp [Nat.add_mod,base4,a.boundaryAligned]
    · have := a.boundaryFit; have := i.isLt; omega

theorem Arena.local_separate (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Separate (Assembly.setup (a.context i) (BitVec.ofNat 32 n) (a.start memory regs)).core
      (a.vector .x) (a.vector .ap) (a.vector .r) (a.vector .diagonal) a.boundary (a.vector .z) := by
  constructor
  all_goals simp only [a.setup_address,a.setup_boundary]
  all_goals first | exact a.owners _ _ i i (Or.inl (by decide)) | exact a.boundary_disjoint _ i i

end PtxTorchLean.Poisson.PTX.UpdateXRZ
