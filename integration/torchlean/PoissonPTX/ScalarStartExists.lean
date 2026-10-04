import PoissonPTX.ScalarStartResult

namespace PtxTorchLean.Poisson.PTX.Scalar.Start
variable {a : Arena} {s : Flow.State} {norm product tolerance value : Word}

theorem body_exists (s : Flow.State) (running : s.halted=false) (ready : a.Ready s) :
    ∃ final, Sequence ctx (body a.offset) s final ∧ final.halted=false := by
  let norm := encode (Float.sqrt (decode (read64 s.core.global (a.slot .rhsSquare))))
  let product := encode (decode (read64 s.core.global (a.slot .rtol))*decode norm)
  let tolerance := encode (maximum product (read64 s.core.global (a.slot .atol)))
  have rootReady : a.Ready (rooted a s norm) := rooted_ready ready
  have load := load64_trace (ctx:=ctx) (dst:=4) running (a.state_valid64 ready .rhsSquare rfl)
  have root : Sequence ctx [.sqrt 4 (.reg 4)] (loaded64 s 4 (a.offset .rhsSquare)) (rooted a s norm) := by
    refine Sequence.cons (s := loaded64 s 4 (a.offset .rhsSquare))
      (middle := rooted a s norm) running (Eval.sqrt (value := norm) ?_) .nil
    simp only [norm,decode_encode,Operand.eval,loaded64_reg,a.state_address ready]
  have inputs := middle_trace (ctx:=ctx) (s:=rooted a s norm) running rootReady
  have multiply : Sequence ctx [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 4))))]
      (middle a (rooted a s norm)) (scaled (middle a (rooted a s norm)) product) := by
    refine Sequence.cons (s := middle a (rooted a s norm))
      (middle := scaled (middle a (rooted a s norm)) product) running
      (Eval.base (Flow.Eval.data (Indexed.Eval.data (PTX.Eval.fp (out := product) ?_)))) .nil
    change decode product=decode ((middle a (rooted a s norm)).core.regs 5)*decode ((middle a (rooted a s norm)).core.regs 4)
    rw [(middle_values rootReady).2.1,(middle_values rootReady).1]
    simp only [rooted,Norm.rooted_frame.1,Norm.rooted_frame.2.2.2.2.2,product,decode_encode]
  have max : Sequence ctx [.max 5 (.reg 5) (.reg 6)] (scaled (middle a (rooted a s norm)) product)
      (maximumStored (scaled (middle a (rooted a s norm)) product) tolerance) := by
    refine Sequence.cons (s := scaled (middle a (rooted a s norm)) product)
      (middle := maximumStored (scaled (middle a (rooted a s norm)) product) tolerance) running
      (Eval.max (value := tolerance) ?_) .nil
    simp only [Operand.eval,scaled,assign,advance,Function.update_self,Function.update_of_ne (by decide : (6:Nat)≠5)]
    rw [(middle_values rootReady).2.2.1]
    simp only [tolerance,decode_encode,rooted,Norm.rooted_frame.1]
  have last := tail_trace (ctx:=ctx) (s:=maximumStored (scaled (middle a (rooted a s norm)) product) tolerance)
    running (maximum_ready (scaled_ready (middle_ready rootReady)))
  have joined := sequence_append (sequence_append (sequence_append (sequence_append (sequence_append load root) inputs) multiply) max) last
  have actual : Sequence ctx (body a.offset) s (finished a (maximumStored (scaled (middle a (rooted a s norm)) product) tolerance)) := by simpa only [body,List.append_assoc,List.cons_append,List.nil_append] using joined
  exact ⟨_,actual,(sequence_running actual body_segment).trans running⟩

theorem entry_exists (a : Arena) (memory : Memory) (regs : Registers) :
    ∃ final, Runs a.context (entry a.offset) (a.start memory regs) final ∧ final.halted=true := by
  obtain ⟨middle,trace,_⟩ := body_exists (ctx:=a.context) (setup a.context (a.start memory regs)) rfl (a.setup_ready memory regs)
  exact ⟨_,entry_executes trace body_segment rfl rfl,rfl⟩

end PtxTorchLean.Poisson.PTX.Scalar.Start
