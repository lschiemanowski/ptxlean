import PoissonPTX.InitializePrefix

namespace PtxTorchLean.Poisson.PTX.Initialize

theorem divided_address : address (divided ctx s boundary input rhs r diagonal z p value).core 12 field=address s.core 12 field := by
  simp only [divided,address,wide,DividePair.finish_frame.2.2.2.1,DividePair.finish_frame.2.2.2.2,
    ready_frame.2.2.2.1,ready_frame.2.2.2.2.1]

theorem divided_frame :
    (divided ctx s boundary input rhs r diagonal z p value).core.globalStart=s.core.globalStart ∧
    (divided ctx s boundary input rhs r diagonal z p value).core.globalBytes=s.core.globalBytes ∧
    (divided ctx s boundary input rhs r diagonal z p value).halted=s.halted := by
  simp only [divided,DividePair.finish_frame.1,DividePair.finish_frame.2.1,
    ready_frame.2.1,ready_frame.2.2.1,ready_frame.2.2.2.2.2,and_self]

theorem state_result (actual : Flow.Sequence ctx (body boundary input rhs r diagonal z p x) s final)
    (running : s.halted=false) (valid : Valid s.core boundary input rhs r diagonal z p x) :
    ∃ value, final=finish ctx s boundary input rhs r diagonal z p x value ∧
      decode value=DividePair.result (ready ctx s boundary input rhs r diagonal).core := by
  have splitBody : body boundary input rhs r diagonal z p x=
      prefixCode boundary input rhs r diagonal++
      ((DividePair.code z p).map (Flow.Instr.data ∘ Indexed.Instr.data)++
      (StoreZero.code x).map (Flow.Instr.data ∘ Indexed.Instr.data)) := by simp [body,List.append_assoc]
  rw [splitBody] at actual
  obtain ⟨middle,first,rest⟩ := Flow.sequence_split _ _ actual
  have same := Flow.sequence_unique first (prefix_trace running valid) prefix_plain
  subst middle
  obtain ⟨middle,divide,last⟩ := Flow.sequence_split _ _ rest
  obtain ⟨block,state⟩ := Flow.scalar_segment divide
  obtain ⟨value,eq,decoded⟩ := DividePair.state_result block
    (by simpa only [ready_frame.2.1,ready_frame.2.2.1,ready_address] using valid.1 z (by simp))
    (by simpa only [ready_frame.2.1,ready_frame.2.2.1,ready_address] using valid.1 p (by simp))
  have mid : middle=divided ctx s boundary input rhs r diagonal z p value := by rw [state,eq]; rfl
  subst middle
  obtain ⟨zero,state⟩ := Flow.scalar_segment last
  have eq := StoreZero.block_eq zero (by
    simpa only [divided_frame.1,divided_frame.2.1,divided_address] using valid.1 x (by simp))
  refine ⟨value,?_,decoded⟩
  rw [state,eq]; rfl

theorem body_exists (s : Flow.State) (running : s.halted=false) (valid : Valid s.core boundary input rhs r diagonal z p x) :
    ∃ final, Flow.Sequence ctx (body boundary input rhs r diagonal z p x) s final ∧ final.halted=false := by
  have first := prefix_trace (ctx:=ctx) running valid
  let value := encode (DividePair.result (ready ctx s boundary input rhs r diagonal).core)
  have block := DividePair.executes (ready ctx s boundary input rhs r diagonal).core z p
    (by simpa only [ready_frame.2.1,ready_frame.2.2.1,ready_address] using valid.1 z (by simp))
    (by simpa only [ready_frame.2.1,ready_frame.2.2.1,ready_address] using valid.1 p (by simp))
  have divide := Flow.scalar_sequence (ctx:=ctx) (s:=ready ctx s boundary input rhs r diagonal) block
    (ready_frame.2.2.2.2.2.trans running)
  have zero := Flow.scalar_sequence (ctx:=ctx) (s:=divided ctx s boundary input rhs r diagonal z p value)
    (run_sound (StoreZero.executes _ x (by
      simpa only [divided_frame.1,divided_frame.2.1,divided_address] using valid.1 x (by simp))))
    (divided_frame.2.2.trans running)
  have joined := Flow.sequence_append (Flow.sequence_append first divide) zero
  exact ⟨_,joined,(Flow.sequence_running joined body_segment).trans running⟩

end PtxTorchLean.Poisson.PTX.Initialize
