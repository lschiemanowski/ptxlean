import PoissonPTX.ScalarAlphaValues

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha
variable {a : Arena} {s : Flow.State}

theorem body_result (actual : Sequence ctx (body a.offset) s final) (running : s.halted=false) (ready : a.Ready s) :
    ∃ value, Allowed a s.core.global value ∧ final=finished a (beforeDivide ctx a s) value := by
  rw [body,List.append_assoc] at actual
  obtain ⟨middle,prefixRun,rest⟩ := sequence_split _ _ actual
  have same := prefix_state prefixRun running ready
  rw [same] at rest
  obtain ⟨divided,divideRun,storeRun⟩ := sequence_split _ _ rest
  obtain ⟨value,allowed,sameDiv⟩ := ConditionalDivide.result divideRun (by decide) (by decide)
  rw [sameDiv] at storeRun
  refine ⟨value,(allowed_iff ready).mp allowed,?_⟩
  exact store64_state storeRun (a.state_valid64 (ConditionalDivide.ready (before_ready ready)) .alpha rfl)
    (ConditionalDivide.frame.2.2.2.2.1.trans (before_running.trans running))

theorem body_trace (running : s.halted=false) (ready : a.Ready s) (allowed : Allowed a s.core.global value) :
    Sequence ctx (body a.offset) s (finished a (beforeDivide ctx a s) value) := by
  have one := prefix_trace (ctx:=ctx) running ready
  have two := ConditionalDivide.trace (ctx:=ctx) (s:=beforeDivide ctx a s) (before_running.trans running) ((allowed_iff ready).mpr allowed) (by decide : 5≠6) (by decide : 4≠6)
  have three := store64_trace (ctx:=ctx) (s:=ConditionalDivide.finish (beforeDivide ctx a s) value) (value:=.reg 6)
    (ConditionalDivide.frame.2.2.2.2.1.trans (before_running.trans running))
    (a.state_valid64 (ConditionalDivide.ready (before_ready ready)) .alpha rfl)
  exact sequence_append (sequence_append one two) three

theorem entry_publication (actual : Runs a.context (entry a.offset) (a.start memory regs) final) (done : final.halted=true) :
    ∃ value, Allowed a memory value ∧ final.core.global=publish a memory value := by
  obtain ⟨middle,trace,same⟩ := entry_result (body:=body a.offset) actual rfl rfl done (body_segment (a:=a))
  obtain ⟨value,allowed,middleEq⟩ := body_result trace rfl (a.setup_ready memory regs)
  refine ⟨value,allowed,?_⟩
  have pub := finished_global (ctx:=a.context) (value:=value) (a.setup_ready memory regs)
  have mid := congrArg (fun st : Flow.State => st.core.global) middleEq
  have last := congrArg (fun st : Flow.State => st.core.global) same
  exact last.trans (mid.trans pub)

theorem entry_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final, Runs a.context (entry a.offset) (a.start memory regs) final ∧ final.halted=true := by
  have ready := a.setup_ready memory regs
  obtain ⟨value,allowed⟩ := ConditionalDivide.exists_allowed (beforeDivide a.context a (setup a.context (a.start memory regs))) 5 4
  have trace := body_trace (ctx:=a.context) rfl ready ((allowed_iff ready).mp allowed)
  exact ⟨_,entry_executes trace body_segment rfl rfl,rfl⟩

theorem published_outside (a : Arena) (memory : Memory) (value : Word) (byte : Nat)
    (outside : ∀ f∈[Field.broken,.useStep,.alpha],byte<a.slot f ∨ a.slot f+f.width≤byte) :
    publish a memory value byte=memory byte := by
  unfold publish flags
  rw [write64_outside _ _ _ _ (outside .alpha (by simp)),write32_outside _ _ _ _ (outside .useStep (by simp)),
    write32_outside _ _ _ _ (outside .broken (by simp))]

end PtxTorchLean.Poisson.PTX.Scalar.Alpha
