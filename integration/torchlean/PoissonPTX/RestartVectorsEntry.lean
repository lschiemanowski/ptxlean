import PoissonPTX.RestartVectorsCorrect

namespace PtxTorchLean.Poisson.PTX.RestartVectors

theorem entry_correct (actual : Flow.Runs ctx (entry count source r diagonal boundary z p) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (live : Kernel.Residual.live ctx count)
    (valid : Valid (Assembly.setup ctx count s).core source r diagonal boundary z p)
    (separated : Separate (Assembly.setup ctx count s).core r diagonal boundary z p) :
    read64 final.core.global (address (Assembly.setup ctx count s).core 12 r).toNat=
      read64 s.core.global (address (Assembly.setup ctx count s).core 12 source).toNat ∧
    decode (read64 final.core.global (address (Assembly.setup ctx count s).core 12 z).toNat)=
      quotient (Assembly.setup ctx count s).core source diagonal boundary ∧
    read64 final.core.global (address (Assembly.setup ctx count s).core 12 p).toNat=
      read64 final.core.global (address (Assembly.setup ctx count s).core 12 z).toNat ∧
    (∀ byte, (∀ field∈[r,z,p], byte<(address (Assembly.setup ctx count s).core 12 field).toNat ∨
      (address (Assembly.setup ctx count s).core 12 field).toNat+8≤byte) → final.core.global byte=s.core.global byte) := by
  obtain ⟨middle,bodyRun,eq⟩ := VectorFlowEntry.completed_body actual pc running done live body_segment
  subst final
  have answer := correct bodyRun (Assembly.setup_active (s:=s) live) valid separated
  exact answer

theorem entry_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (live : Kernel.Residual.live ctx count)
    (valid : Valid (Assembly.setup ctx count s).core source r diagonal boundary z p) :
    ∃ final, Flow.Runs ctx (entry count source r diagonal boundary z p) s final ∧ final.halted=true := by
  obtain ⟨middle,bodyRun,_⟩ := body_exists (ctx:=ctx) (Assembly.setup ctx count s) (Assembly.setup_active (s:=s) live) valid
  exact ⟨_,VectorFlowEntry.executes pc running live body_segment bodyRun,rfl⟩

theorem inactive (actual : Flow.Runs ctx (entry count source r diagonal boundary z p) s final)
    (pc : s.core.pc=0) (running : s.halted=false) (done : final.halted=true)
    (inactive : ¬Kernel.Residual.live ctx count) : final.core.global=s.core.global := by
  rw [VectorFlowEntry.inactive actual pc running done inactive]
  rfl

theorem inactive_exists (s : Flow.State) (pc : s.core.pc=0) (running : s.halted=false)
    (inactive : ¬Kernel.Residual.live ctx count) :
    ∃ final, Flow.Runs ctx (entry count source r diagonal boundary z p) s final ∧ final.halted=true :=
  ⟨_,VectorFlowEntry.setup_run pc running,Assembly.setup_inactive inactive⟩

end PtxTorchLean.Poisson.PTX.RestartVectors
