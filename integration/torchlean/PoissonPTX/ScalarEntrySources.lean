import PoissonPTX.ScalarObservedExecution

namespace PtxTorchLean.Poisson.PTX.Scalar
variable {a : Arena} {chunks : List Chunk}

/-- Replay the complete fetched single-thread entry, including launch setup
and return, using only physical field layout and necessary source admission. -/
theorem chunks_entry_replay
    (actual : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final)
    (done : final.halted=true) (valid : ∀ chunk∈chunks, chunk.valid)
    (ordered : ∀ pc, ReadBeforeWrite (footprints a.offset pc chunks))
    (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final := by
  have plain : ∀ i∈chunksCode a.offset chunks, segment i=true := fun i mem => (chunks_safe valid i mem).2
  obtain ⟨middle,bodyRun,same⟩ := Observed.entry_result actual rfl rfl done plain
  have replay := chunks_replay bodyRun valid rfl (a.setup_ready memory regs) (ordered _) compatible admitted
  rw [same]
  exact Scalar.entry_executes replay plain rfl rfl

/-- An existing finite scalar execution supplies a finite candidate history
whose actual byte sources satisfy compatibility and the no-future rule. -/
theorem chunks_entry_recorded
    (actual : Scalar.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) final)
    (done : final.halted=true) (valid : ∀ chunk∈chunks, chunk.valid)
    (ordered : ∀ pc, ReadBeforeWrite (footprints a.offset pc chunks)) :
    ∃ events, Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final ∧
      Sources.Compatible (a.start memory regs).core.memory events (fun _ _ => .initial) ∧
      Sources.NoFuture events (fun _ _ => .initial) := by
  have plain : ∀ i∈chunksCode a.offset chunks, segment i=true := fun i mem => (chunks_safe valid i mem).2
  obtain ⟨middle,bodyRun,same⟩ := Scalar.entry_result actual rfl rfl done plain
  obtain ⟨events,recorded,compatible,admitted⟩ := chunks_recorded bodyRun valid rfl (a.setup_ready memory regs) (ordered _)
  refine ⟨events,?_,compatible,admitted⟩
  rw [same]
  exact Observed.entry_executes recorded plain rfl rfl

end PtxTorchLean.Poisson.PTX.Scalar
