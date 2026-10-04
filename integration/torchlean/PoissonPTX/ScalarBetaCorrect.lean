import PoissonPTX.ScalarBetaValues

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta
variable {a : Arena} {s : Flow.State}

def Result (ctx : Kernel.Context) (a : Arena) (s final : Flow.State) : Prop := ∃ value square,
  Allowed a s.core.global value ∧
  decode square=decode (read64 s.core.global (a.slot .tolerance))*decode (read64 s.core.global (a.slot .tolerance)) ∧
  final=finished ctx a (squared (readySquare ctx a s value) square)

theorem body_result (actual : Sequence ctx (body a.offset) s final) (running : s.halted=false) (ready : a.Ready s) :
    Result ctx a s final := by
  simp only [body,List.append_assoc] at actual
  obtain ⟨prepared,prepareRun,rest⟩ := sequence_split _ _ actual
  have preparedEq := sequence_unique prepareRun (prefix_trace (ctx:=ctx) running ready) prefix_plain
  rw [preparedEq] at rest
  obtain ⟨divided,divideRun,rest⟩ := sequence_split _ _ rest
  obtain ⟨value,allowed,dividedEq⟩ := ConditionalDivide.result divideRun (by decide : 4≠6) (by decide : 5≠6)
  rw [dividedEq] at rest
  have dividedReady := ConditionalDivide.ready (before_ready (ctx:=ctx) ready) (value:=value)
  have dividedAlive := (ConditionalDivide.frame (s:=beforeDivide ctx a s) (value:=value)).2.2.2.2.1
  obtain ⟨beforeSquare,middleRun,rest⟩ := sequence_split _ _ rest
  have middleEq := sequence_unique middleRun (middle_trace (ctx:=ctx) (dividedAlive.trans (before_running.trans running)) dividedReady) middle_plain
  have squareEq : beforeSquare=readySquare ctx a s value := middleEq
  rw [squareEq] at rest
  obtain ⟨squareState,squareRun,tailRun⟩ := sequence_split _ _ rest
  obtain ⟨square,actualSquare,rounded⟩ := fp_result squareRun
  have same : squareState=squared (readySquare ctx a s value) square := actualSquare
  rw [same] at tailRun
  have squareReady := squared_ready (value:=square) (middle_ready dividedReady)
  have alive : (squared (readySquare ctx a s value) square).halted=false := by
    exact dividedAlive.trans (before_running.trans running)
  have tailEq := sequence_unique tailRun (tail_trace (ctx:=ctx) alive squareReady) tail_plain
  refine ⟨value,square,(allowed_iff ready).mp allowed,?_,tailEq⟩
  simp only [FP.Result,FP.apply,Operand.eval] at rounded
  simpa only [(ready_square_values ready).2.1] using rounded

def nextActive (a : Arena) (memory : Memory) (square : Word) : Bool :=
  useStep a memory && Comparison.apply .gt (read64 memory (a.slot .rr)) square && (broken a memory==0)

def publish (a : Arena) (memory : Memory) (value square : Word) : Memory :=
  write32 (dividedMemory a memory value) (a.slot .active) (if nextActive a memory square then 1 else 0)

theorem finished_global (ready : a.Ready s) :
    (finished ctx a (squared (readySquare ctx a s value) square)).core.global=publish a s.core.global value square := by
  have ready' : a.Ready (squared (readySquare ctx a s value) square) := squared_ready (middle_ready (ConditionalDivide.ready (before_ready ready)))
  rw [tail_global (ctx:=ctx) ready']
  simp only [Coefficient.betaActive,squared,assign,advance,Function.update_self,Function.update_of_ne (by decide : (4:Nat)≠5),
    Function.update_of_ne (by decide : (22:Nat)≠5)]
  rw [(ready_square_values ready).1,(ready_square_values ready).2.2.1,(ready_square_values ready).2.2.2.1,
    (ready_square_values ready).2.2.2.2]
  rfl

theorem entry_publication (actual : Runs a.context (entry a.offset) (a.start memory regs) final) (done : final.halted=true) :
    ∃ value square, Allowed a memory value ∧
      decode square=decode (read64 memory (a.slot .tolerance))*decode (read64 memory (a.slot .tolerance)) ∧
      final.core.global=publish a memory value square := by
  obtain ⟨middle,trace,same⟩ := entry_result (body:=body a.offset) actual rfl rfl done (body_segment (a:=a))
  obtain ⟨value,square,allowed,rounded,middleEq⟩ := body_result trace rfl (a.setup_ready memory regs)
  have pub := finished_global (ctx:=a.context) (value:=value) (square:=square) (a.setup_ready memory regs)
  have mid := congrArg (fun st : Flow.State => st.core.global) middleEq
  have last := congrArg (fun st : Flow.State => st.core.global) same
  exact ⟨value,square,allowed,rounded,last.trans (mid.trans pub)⟩

theorem published_outside (a : Arena) (memory : Memory) (value square : Word) (byte : Nat)
    (outside : ∀ f∈[Field.broken,.beta,.rho,.active],byte<a.slot f ∨ a.slot f+f.width≤byte) :
    publish a memory value square byte=memory byte := by
  unfold publish dividedMemory flagged
  rw [write32_outside _ _ _ _ (outside .active (by simp)),write64_outside _ _ _ _ (outside .rho (by simp)),
    write64_outside _ _ _ _ (outside .beta (by simp)),write32_outside _ _ _ _ (outside .broken (by simp))]

end PtxTorchLean.Poisson.PTX.Scalar.Beta
