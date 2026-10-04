import PoissonPTX.ScalarEntrySources
import PoissonPTX.ScalarStartSources
import PoissonPTX.ScalarAlphaSources
import PoissonPTX.ScalarBetaSources

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena}

theorem admitted_replay
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (entry a.offset) (a.start memory regs) final := by
  have run : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final := by
    simpa only [chunks_code,entry] using actual
  simpa only [chunks_code,entry] using chunks_entry_replay run done chunks_valid (fun _ => reads_before_writes) compatible admitted

theorem admitted_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final events, Observed.Runs a.context (entry a.offset) (a.start memory regs) events final ∧ final.halted=true ∧
      Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  obtain ⟨final,run,done⟩ := entry_exists a memory regs
  have ordinary : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
    simpa only [chunks_code,entry] using run
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_entry_recorded ordinary done chunks_valid (fun _ => reads_before_writes)
  exact ⟨final,events,by simpa only [chunks_code,entry] using recorded,done,compatible,admitted⟩

end PtxTorchLean.Poisson.PTX.Scalar.Start

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha
variable {a : Arena}

theorem admitted_replay
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (entry a.offset) (a.start memory regs) final := by
  have run : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final := by
    simpa only [chunks_code,entry] using actual
  simpa only [chunks_code,entry] using chunks_entry_replay run done chunks_valid (fun _ => reads_before_writes) compatible admitted

theorem admitted_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final events, Observed.Runs a.context (entry a.offset) (a.start memory regs) events final ∧ final.halted=true ∧
      Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  obtain ⟨final,run,done⟩ := entry_exists a memory regs
  have ordinary : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
    simpa only [chunks_code,entry] using run
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_entry_recorded ordinary done chunks_valid (fun _ => reads_before_writes)
  exact ⟨final,events,by simpa only [chunks_code,entry] using recorded,done,compatible,admitted⟩

end PtxTorchLean.Poisson.PTX.Scalar.Alpha

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena}

theorem admitted_replay
    (actual : Observed.Runs a.context (entry a.offset) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (entry a.offset) (a.start memory regs) final := by
  have run : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final := by
    simpa only [chunks_code,entry] using actual
  simpa only [chunks_code,entry] using chunks_entry_replay run done chunks_valid (fun _ => reads_before_writes) compatible admitted

theorem admitted_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final events, Observed.Runs a.context (entry a.offset) (a.start memory regs) events final ∧ final.halted=true ∧
      Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  obtain ⟨final,run,done⟩ := entry_exists a memory regs
  have ordinary : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
    simpa only [chunks_code,entry] using run
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_entry_recorded ordinary done chunks_valid (fun _ => reads_before_writes)
  exact ⟨final,events,by simpa only [chunks_code,entry] using recorded,done,compatible,admitted⟩

end PtxTorchLean.Poisson.PTX.Scalar.Beta

