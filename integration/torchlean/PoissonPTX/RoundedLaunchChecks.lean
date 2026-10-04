import PoissonPTX.RoundedLaunchProjection

namespace PtxTorchLean.Poisson.PTX.Rounded.Checks

/-- Exact-block and neighboring sizes exercise both guard outcomes. -/
theorem sizes : count 0=0 ∧ count 1=256 ∧ count 255=256 ∧ count 256=256 ∧ count 257=512 := by decide +kernel

theorem first_padding :
    ¬Kernel.Residual.live (context (n:=257) 0 (⟨257,by decide⟩ : Fin (count 257))) (BitVec.ofNat 32 257) := by
  rw [live 0 (by decide)]; decide

theorem last_active :
    Kernel.Residual.live (context (n:=257) 0 (⟨256,by decide⟩ : Fin (count 257))) (BitVec.ofNat 32 257) := by
  rw [live 0 (by decide)]; decide

/-- At the largest admitted size, the padded lane still has an exact unsigned
index and cannot wrap into an active coordinate. -/
theorem large_padding : count (2^30-1)=2^30 ∧
    ¬Kernel.Residual.live (context (n:=2^30-1) 0 (⟨2^30-1,by decide⟩ : Fin (count (2^30-1))))
      (BitVec.ofNat 32 (2^30-1)) := by
  constructor
  · decide +kernel
  · rw [live (n:=2^30-1) 0 (by decide)]; decide +kernel

end PtxTorchLean.Poisson.PTX.Rounded.Checks
