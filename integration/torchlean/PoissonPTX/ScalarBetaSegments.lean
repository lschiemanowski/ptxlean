import PoissonPTX.ScalarBeta

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena} {s : Flow.State}

theorem middle_ready (ready : a.Ready s) : a.Ready (middle a s) :=
  a.ready_load64 (a.ready_load64 (a.ready_store64 (a.ready_store64 ready)) (by decide)) (by decide)

theorem squared_ready (ready : a.Ready s) : a.Ready (squared s value) := a.ready_assign ready (by decide)

theorem final_ready (ready : a.Ready s) : a.Ready (Coefficient.betaFinal ctx s) := by
  simpa only [Arena.Ready,Coefficient.beta_final_values.2.2.1,Coefficient.beta_final_values.2.2.2.1,
    Coefficient.beta_final_values.2.2.2.2.1] using ready

theorem middle_trace (running : s.halted=false) (ready : a.Ready s) :
    Sequence ctx (middleCode a.offset) s (middle a s) := by
  have one := store64_trace (ctx:=ctx) (value:=.reg 6) running (a.state_valid64 ready .beta rfl)
  have two := store64_trace (ctx:=ctx) (s:=betaStored a s) (value:=.reg 4) running (a.state_valid64 (a.ready_store64 ready) .rho rfl)
  have three := load64_trace (ctx:=ctx) (s:=rhoStored a s) (dst:=4) running
    (a.state_valid64 (a.ready_store64 (a.ready_store64 ready)) .rr rfl)
  have four := load64_trace (ctx:=ctx) (s:=rrLoaded a s) (dst:=5) running
    (a.state_valid64 (a.ready_load64 (a.ready_store64 (a.ready_store64 ready)) (by decide)) .tolerance rfl)
  exact sequence_append (sequence_append (sequence_append one two) three) four

theorem tail_trace (running : s.halted=false) (ready : a.Ready s) :
    Sequence ctx (tailCode a.offset) s (finished ctx a s) :=
  sequence_append (Coefficient.beta_final_trace running)
    (store32_trace (Coefficient.beta_final_values.2.2.2.2.2.trans running) (a.state_valid32 (final_ready ready) .active rfl))

theorem middle_plain : ∀ i∈middleCode a.offset, noFP i=true := by
  simp [middleCode,load64Code,ops,ScalarLoad.code,store64Code,store64Ops,noFP,Flow.noFP,Indexed.noFP,PTX.noFP]

theorem tail_plain : ∀ i∈tailCode a.offset, noFP i=true := by
  intro i member
  rcases List.mem_append.mp member with guard | store
  · exact Control.plain (Coefficient.beta_final_supported i guard)
  · exact store32_plain i store

theorem body_segment : ∀ i∈body a.offset, segment i=true := by
  simp [body,prefixCode,middleCode,tailCode,selectCode,Coefficient.inputCode,Coefficient.betaBrokenCode,
    Coefficient.finiteCode,Coefficient.betaFinalCode,ConditionalDivide.code,
    load64Code,load32Code,store64Code,store64Ops,store32Code,address4Code,ScalarLoad.code,ops,segment,Flow.segment]

theorem entry_length : (entry a.offset).length=63 := by
  simp [entry,program,prologue,body,prefixCode,middleCode,tailCode,selectCode,Coefficient.inputCode,Coefficient.betaBrokenCode,
    Coefficient.finiteCode,Coefficient.betaFinalCode,ConditionalDivide.code,
    load64Code,load32Code,store64Code,store64Ops,store32Code,address4Code,ScalarLoad.code,ops]

theorem middle_values (ready : a.Ready s) :
    (middle a s).core.regs 4=read64 s.core.global (a.slot .rr) ∧
    (middle a s).core.regs 5=read64 s.core.global (a.slot .tolerance) ∧
    (middle a s).core.regs 22=s.core.regs 22 ∧ (middle a s).predicates=s.predicates ∧
    (middle a s).core.global=write64 (write64 s.core.global (a.slot .beta) (s.core.regs 6)) (a.slot .rho) (s.core.regs 4) := by
  simp [middle,rrLoaded,rhoStored,betaStored,loaded64,stored64,ScalarLoad.loaded,ScalarLoad.addressed,
    put,assign,advance,Operand.eval,ready.1,a.address,
    read64_write64_disjoint _ _ _ _ (a.word_separate .rho .rr (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .beta .rr (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .rho .tolerance (by decide) rfl rfl),
    read64_write64_disjoint _ _ _ _ (a.word_separate .beta .tolerance (by decide) rfl rfl)]

theorem tail_global (ready : a.Ready s) :
    (finished ctx a s).core.global=write32 s.core.global (a.slot .active) (if Coefficient.betaActive s then 1 else 0) := by
  rw [finished,stored32_global]
  simp only [Operand.eval,addressed_reg (by decide : 21≠1) (by decide : 21≠2),Coefficient.beta_final_values.1,
    Coefficient.beta_final_values.2.1,(final_ready ready).1,a.address]

end PtxTorchLean.Poisson.PTX.Scalar.Beta
