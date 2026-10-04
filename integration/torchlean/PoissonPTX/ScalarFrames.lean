import PoissonPTX.ScalarMemory

namespace PtxTorchLean.Poisson.PTX.Scalar

theorem loaded64_frame (dst0 : dst≠0) : (loaded64 s dst offset).core.global=s.core.global ∧
    (loaded64 s dst offset).core.globalStart=s.core.globalStart ∧ (loaded64 s dst offset).core.globalBytes=s.core.globalBytes ∧
    (loaded64 s dst offset).core.regs 0=s.core.regs 0 ∧ (loaded64 s dst offset).halted=s.halted := by
  simp [loaded64,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,Ne.symm dst0]

theorem loaded64_reg : (loaded64 s dst offset).core.regs dst=read64 s.core.global (s.core.regs 0+offset).toNat := by
  simp [loaded64,ScalarLoad.loaded,assign]

theorem stored64_frame : (stored64 s offset value).core.globalStart=s.core.globalStart ∧
    (stored64 s offset value).core.globalBytes=s.core.globalBytes ∧
    (stored64 s offset value).core.regs 0=s.core.regs 0 ∧ (stored64 s offset value).halted=s.halted := by
  simp [stored64,ScalarLoad.addressed,put,assign,advance]

theorem stored64_global : (stored64 s offset value).core.global=
    write64 s.core.global (s.core.regs 0+offset).toNat (value.eval (ScalarLoad.addressed s.core offset)) := rfl

theorem addressed_reg (h1 : reg≠1) (h2 : reg≠2) : (ScalarLoad.addressed s offset).regs reg=s.regs reg := by
  simp [ScalarLoad.addressed,assign,advance,h1,h2]

theorem stored32_global : (stored32 s offset value).core.global=
    write32 s.core.global (s.core.regs 0+offset).toNat (Kernel.u32 (value.eval (ScalarLoad.addressed s.core offset))) := rfl

theorem read64_write32_disjoint (memory : Memory) (a b : Nat) (value : BitVec 32)
    (apart : a+4≤b ∨ b+8≤a) : read64 (write32 memory a value) b=read64 memory b := by
  have keep (i : Nat) (small : i<8) : write32 memory a value (b+i)=memory (b+i) := write32_outside _ _ _ _ (by omega)
  simp only [read64]
  rw [keep 7 (by omega),keep 6 (by omega),keep 5 (by omega),keep 4 (by omega),
    keep 3 (by omega),keep 2 (by omega),keep 1 (by omega),
    show write32 memory a value b=memory b from by simpa using keep 0 (by omega)]

end PtxTorchLean.Poisson.PTX.Scalar
