import PoissonPTX.AssemblyArena

namespace PtxTorchLean.Poisson.PTX.Assembly

theorem Arena.output_address (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    (address (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core 12 a.output).toNat=
      a.base.toNat+a.output.toNat+i.val*8 := by
  have eq : address (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core 12 a.output=
      address64 a.base (Kernel.Residual.index (a.context i)) a.output := by
    simp [address,wide,ready,prepared,setup,address64,BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Kernel.Residual.index (a.context i)).isLt]
    rfl
  rw [eq,address64_exact _ _ _ (by rw [a.index]; have := a.outputFit; have := a.noWrap; have := i.isLt; omega),a.index]
  omega

theorem Arena.boundary_address (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    (maskAddress (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core a.boundary).toNat=
      a.base.toNat+a.boundary.toNat+i.val*4 := by
  have eq : maskAddress (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core a.boundary=
      address32 a.base (Kernel.Residual.index (a.context i)) a.boundary := by
    simp [maskAddress,ready,prepared,setup,Arena.context,Kernel.u32]
  rw [eq,address32_exact _ _ _ (by rw [a.index]; have := a.boundaryFit; have := a.noWrap; have := i.isLt; omega),a.index]
  omega

theorem Arena.output_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Valid64 (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core.globalStart
      (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core.globalBytes
      (address (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core 12 a.output).toNat := by
  rw [a.output_address]
  change Valid64 a.base.toNat a.bytes _
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · simp [Nat.add_mod,a.aligned,a.outputAligned]
  · have := a.outputFit; have := i.isLt; omega

theorem Arena.boundary_valid (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n) :
    Valid32 (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core.globalStart
      (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core.globalBytes
      (maskAddress (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core a.boundary).toNat := by
  rw [a.boundary_address]
  change Valid32 a.base.toNat a.bytes _
  refine ⟨by omega,?_,?_,a.noWrap⟩
  · have base4 : a.base.toNat%4=0 := by have := a.aligned; omega
    simp [Nat.add_mod,base4,a.boundaryAligned]
  · have := a.boundaryFit; have := i.isLt; omega

def Arena.loop_layout (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (contents : a.Contents memory) :
    Layout (ready (a.context i) (BitVec.ofNat 32 n) a.offsets (a.start memory regs)).core a.entries a.element where
  entryCount := a.entryCount
  elementCount := a.elementCount
  base := by simp [ready,prepared,setup,Arena.start,Arena.context]
  aligned := a.aligned
  entriesAligned := a.entryAligned
  elementAligned := a.elementAligned
  endBound := by rw [a.ready_limit]; exact contents.last i.val i.isLt
  small := a.entriesSmall
  entriesFit := a.entriesFit
  elementFit := a.elementFit
  noWrap := a.noWrap
  indices := contents.indices

/-- The array geometry discharges every memory premise of the complete entry. -/
theorem Arena.complete (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (contents : a.Contents memory) (mask : Bool)
    (run : Flow.Runs (a.context i) (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (a.start memory regs) t) (done : t.halted=true) :
    ∃ word, t.core.global=write64 memory (a.base.toNat+a.output.toNat+i.val*8) word ∧
      decode word=entryValue (a.context i) (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary (a.start memory regs) := by
  have result := entry_written run rfl rfl done (a.live i) (a.prepare_valid memory regs i)
    (a.loop_layout memory regs i contents)
    (by rw [a.ready_cursor,a.ready_limit]; exact contents.ordered i.val i.isLt)
    (fun _ => a.boundary_valid memory regs i) (a.output_valid memory regs i)
  rw [a.output_address] at result
  exact result

theorem Arena.exists (a : Arena n) (memory : Memory) (regs : Registers) (i : Fin n)
    (contents : a.Contents memory) (mask : Bool) :
    ∃ t, Flow.Runs (a.context i) (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (a.start memory regs) t ∧ t.halted=true :=
  entry_exists _ rfl rfl (a.live i) (a.prepare_valid memory regs i)
    (a.loop_layout memory regs i contents)
    (by rw [a.ready_cursor,a.ready_limit]; exact contents.ordered i.val i.isLt)
    (fun _ => a.boundary_valid memory regs i) (a.output_valid memory regs i)

/-- Every active coordinate has exactly one eight-byte output slot. -/
theorem Arena.owners (a : Arena n) (i j : Fin n) (different : i≠j) :
    Sources.Disjoint (a.base.toNat+a.output.toNat+i.val*8) (a.base.toNat+a.output.toNat+j.val*8) := by
  have different : i.val≠j.val := fun eq => different (Fin.ext eq)
  unfold Sources.Disjoint
  omega

end PtxTorchLean.Poisson.PTX.Assembly
