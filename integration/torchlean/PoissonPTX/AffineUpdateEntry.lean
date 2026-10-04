import PoissonPTX.VectorEntry
import PoissonPTX.AffineUpdateCorrect

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

def entry (count : BitVec 32) (coefficient input shift output : Word) : List Flow.Instr :=
  VectorEntry.program count (code coefficient input shift output)

/-- Complete active-thread correspondence from the fetched entry: prologue,
actual scalar/vector loads, separately rounded multiply/add, store and return. -/
theorem entry_correct (run : Flow.Runs ctx (entry count coefficient input shift output) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count)
    (hi : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 input).toNat)
    (hz : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 shift).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 output).toNat) :
    decode (read64 t.core.global (address (Assembly.setup ctx count s).core 12 output).toNat)=
      result (Assembly.setup ctx count s).core coefficient input shift ∧
    (∀ p, p<(address (Assembly.setup ctx count s).core 12 output).toNat ∨
      (address (Assembly.setup ctx count s).core 12 output).toNat+8≤p → t.core.global p=s.core.global p) := by
  obtain ⟨core,body,same⟩ := VectorEntry.completed_body run pc running done live
  have answer := correct body hi hz ho
  subst t
  exact ⟨answer.1,answer.2.1⟩

theorem entry_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (live : Kernel.Residual.live ctx count)
    (hc : Valid64 s.core.globalStart s.core.globalBytes ((Assembly.setup ctx count s).core.regs 0+coefficient).toNat)
    (hi : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 input).toNat)
    (hz : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 shift).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (Assembly.setup ctx count s).core 12 output).toNat) :
    ∃ t, Flow.Runs ctx (entry count coefficient input shift output) s t ∧ t.halted=true := by
  have body := executes (Assembly.setup ctx count s).core coefficient input shift output hc hi hz ho
  exact ⟨_,VectorEntry.executes pc running live body,rfl⟩

theorem inactive_correct (run : Flow.Runs ctx (entry count coefficient input shift output) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) : t.core.global=s.core.global := by
  rw [VectorEntry.inactive run pc running done inactive]
  rfl

theorem inactive_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (inactive : ¬Kernel.Residual.live ctx count) :
    ∃ t, Flow.Runs ctx (entry count coefficient input shift output) s t ∧ t.halted=true :=
  ⟨_,VectorEntry.setup_run pc running,Assembly.setup_inactive inactive⟩

end PtxTorchLean.Poisson.PTX.AffineUpdate
