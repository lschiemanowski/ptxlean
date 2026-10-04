import PoissonPTX.ScalarNormSources

namespace PtxTorchLean.Poisson.PTX.Scalar.Norm
variable {a : Arena}

theorem admitted_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final events, Observed.Runs a.context (entry (a.offset .trueSquare) (a.offset .residual)) (a.start memory regs) events final ∧
      final.halted=true ∧ Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  have src : Valid64 (a.start memory regs).core.globalStart (a.start memory regs).core.globalBytes
      (a.context.arena+a.offset .trueSquare).toNat := by
    simpa only [Arena.start,Arena.context,a.address] using a.valid64 .trueSquare rfl
  have out : Valid64 (a.start memory regs).core.globalStart (a.start memory regs).core.globalBytes
      (a.context.arena+a.offset .residual).toNat := by
    simpa only [Arena.start,Arena.context,a.address] using a.valid64 .residual rfl
  obtain ⟨final,run,done⟩ := entry_exists (ctx:=a.context) (a.start memory regs) rfl rfl src out
  have ordinary : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
    simpa only [chunks_code,entry] using run
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_entry_recorded ordinary done chunks_valid (fun _ => reads_before_writes)
  exact ⟨final,events,by simpa only [chunks_code,entry] using recorded,done,compatible,admitted⟩

theorem admitted_publication
    (actual : Observed.Runs a.context (entry (a.offset .trueSquare) (a.offset .residual)) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    decode (read64 (Sources.publish (a.start memory regs).core.memory events .global) (a.slot .residual))=
      Float.sqrt (decode (read64 memory (a.slot .trueSquare))) ∧
    ∀ byte, byte<a.slot .residual ∨ a.slot .residual+8≤byte →
      Sources.publish (a.start memory regs).core.memory events .global byte=memory byte := by
  have result := entry_correct (admitted_replay actual done compatible admitted) rfl rfl done
    (by simpa only [Arena.start,Arena.context,a.address] using a.valid64 .residual rfl)
  have bytes := congrArg (fun m : Space → Memory => m .global) (Observed.runs_memory actual)
  change final.core.global=_ at bytes
  rw [bytes] at result
  simpa only [Arena.start,Arena.context,a.address] using result

end PtxTorchLean.Poisson.PTX.Scalar.Norm

namespace PtxTorchLean.Poisson.PTX.Scalar.RestartFlag
variable {a : Arena}

theorem admitted_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final events, Observed.Runs a.context (entry (a.offset .active)) (a.start memory regs) events final ∧
      final.halted=true ∧ Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  have valid : Valid32 (a.start memory regs).core.globalStart (a.start memory regs).core.globalBytes
      (a.context.arena+a.offset .active).toNat := by
    simpa only [Arena.start,Arena.context,a.address] using a.valid32 .active rfl
  obtain ⟨final,run,done⟩ := entry_exists (ctx:=a.context) (a.start memory regs) rfl rfl valid
  have ordinary : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
    simpa only [chunks_code,entry] using run
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_entry_recorded ordinary done chunks_valid (fun _ => reads_before_writes)
  exact ⟨final,events,by simpa only [chunks_code,entry] using recorded,done,compatible,admitted⟩

theorem admitted_publication
    (actual : Observed.Runs a.context (entry (a.offset .active)) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    read32 (Sources.publish (a.start memory regs).core.memory events .global) (a.slot .active)=1 ∧
    ∀ byte, byte<a.slot .active ∨ a.slot .active+4≤byte →
      Sources.publish (a.start memory regs).core.memory events .global byte=memory byte := by
  have result := entry_correct (admitted_replay actual done compatible admitted) rfl rfl done
    (by simpa only [Arena.start,Arena.context,a.address] using a.valid32 .active rfl)
  have bytes := congrArg (fun m : Space → Memory => m .global) (Observed.runs_memory actual)
  change final.core.global=_ at bytes
  rw [bytes] at result
  simpa only [Arena.start,Arena.context,a.address] using result

end PtxTorchLean.Poisson.PTX.Scalar.RestartFlag
