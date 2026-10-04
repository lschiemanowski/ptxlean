import PoissonPTX.RestartVectors

namespace PtxTorchLean.Poisson.PTX.RestartVectors

theorem ready_address : address (ready ctx s source r diagonal boundary).core 12 field=address s.core 12 field := by
  simp only [address,wide,ready_frame.2.2.1,ready_frame.2.2.2.1]

theorem state_result (actual : Flow.Sequence ctx (body source r diagonal boundary z p) s final)
    (running : s.halted=false) (valid : Valid s.core source r diagonal boundary z p) :
    ∃ value, final=finish ctx s source r diagonal boundary z p value ∧
      decode value=DividePair.result (ready ctx s source r diagonal boundary).core := by
  obtain ⟨middle,first,last⟩ := Flow.sequence_split (prefixCode source r diagonal boundary)
    ((DividePair.code z p).map (Flow.Instr.data ∘ Indexed.Instr.data)) actual
  have same := Flow.sequence_unique first (prefix_trace running valid) prefix_plain
  subst middle
  obtain ⟨block,state⟩ := Flow.scalar_segment last
  obtain ⟨value,eq,decoded⟩ := DividePair.state_result block
    (by simpa only [ready_frame.1,ready_frame.2.1,ready_address] using valid.1 z (by simp))
    (by simpa only [ready_frame.1,ready_frame.2.1,ready_address] using valid.1 p (by simp))
  refine ⟨value,?_,decoded⟩
  rw [state,eq]
  rfl

theorem body_exists (s : Flow.State) (running : s.halted=false) (valid : Valid s.core source r diagonal boundary z p) :
    ∃ final, Flow.Sequence ctx (body source r diagonal boundary z p) s final ∧ final.halted=false := by
  have first := prefix_trace (ctx:=ctx) running valid
  have block := DividePair.executes (ready ctx s source r diagonal boundary).core z p
    (by simpa only [ready_frame.1,ready_frame.2.1,ready_address] using valid.1 z (by simp))
    (by simpa only [ready_frame.1,ready_frame.2.1,ready_address] using valid.1 p (by simp))
  have last := Flow.scalar_sequence (ctx:=ctx) (s:=ready ctx s source r diagonal boundary) block
    (ready_frame.2.2.2.2.trans running)
  have joined := Flow.sequence_append first last
  exact ⟨_,joined,(Flow.sequence_running joined body_segment).trans running⟩

theorem ready_word : (ready ctx s source r diagonal boundary).core.regs 4=
    read64 s.core.global (address s.core 12 source).toNat := by
  simp [ready,PreconditionUpdate.ready,PreconditionUpdate.prepared,PreconditionUpdate.diagonalLoaded,
    Assembly.maskLoaded,Flow.simple,Flow.next,assign,advance,addressed,copied,
    VectorCopy.finish,VectorCopy.loaded,put]
  split <;> simp

theorem ready_divisor : (ready ctx s source r diagonal boundary).core.regs 5=
    PreconditionUpdate.divisor (copied s source r).core diagonal boundary := PreconditionUpdate.ready_values.1

theorem finish_global : (finish ctx s source r diagonal boundary z p value).core.global=
    write64 (write64 (write64 s.core.global (address s.core 12 r).toNat
      (read64 s.core.global (address s.core 12 source).toNat)) (address s.core 12 z).toNat value)
      (address s.core 12 p).toNat value := by
  simp only [finish,DividePair.finish_global,ready_address]
  simp only [ready,PreconditionUpdate.ready_frame.1,copied,VectorCopy.finish_global]

end PtxTorchLean.Poisson.PTX.RestartVectors
