import PoissonPTX.PreconditionUpdate

namespace PtxTorchLean.Poisson.PTX.PreconditionUpdate

theorem state_result (actual : Flow.Sequence ctx (code diagonal boundary output) s final)
    (running : s.halted=false)
    (hd : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 diagonal).toNat)
    (hb : Valid32 s.core.globalStart s.core.globalBytes (Assembly.maskAddress s.core boundary).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 output).toNat) :
    ∃ value, final=finish ctx s diagonal boundary output value ∧ decode value=result s.core diagonal boundary := by
  obtain ⟨middle,first,last⟩ := Flow.sequence_split (setupCode diagonal boundary)
    (([Op.fp .div 6 (.reg 6) (.reg 5)]++storeCode 6 12 output).map (Flow.Instr.data ∘ Indexed.Instr.data)) actual
  have same := Flow.sequence_unique first (setup_trace running hd hb) setup_plain
  subst middle
  obtain ⟨block,pred,halt⟩ := Flow.sequence_data_block (ctx:=ctx) (s:=ready ctx s diagonal boundary) (t:=final)
    (code:=([Op.fp .div 6 (.reg 6) (.reg 5)]++storeCode 6 12 output).map Indexed.Instr.data)
    (by simpa only [List.map_map] using last)
  have block := Indexed.underlying_block block
  cases block with
  | cons divide rest =>
    cases divide with
    | @fp _ _ _ _ _ value allowed =>
      have valueEq : decode value=result s.core diagonal boundary := by
        simpa only [FP.Result,FP.apply,Operand.eval,ready_values.1,ready_values.2,result] using allowed
      have stored := store_block_eq rest (by decide) (by decide)
        (by simpa [assign,advance,address,wide,ready_frame.1,ready_frame.2.2.1,ready_frame.2.2.2.1,
          ready_frame.2.2.2.2.1,ready_frame.2.2.2.2.2.1] using ho)
      refine ⟨value,?_,valueEq⟩
      cases final
      simp only [finish]
      congr 1
      · simpa [address,wide,assign,advance,ready_frame.2.2.2.2.1,ready_frame.2.2.2.2.2.1] using stored

theorem executes (s : Flow.State) (running : s.halted=false)
    (hd : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 diagonal).toNat)
    (hb : Valid32 s.core.globalStart s.core.globalBytes (Assembly.maskAddress s.core boundary).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address s.core 12 output).toNat) :
    Flow.Sequence ctx (code diagonal boundary output) s (finish ctx s diagonal boundary output (encode (result s.core diagonal boundary))) := by
  have readyRun := setup_trace (ctx:=ctx) running hd hb
  let preparedState := ready ctx s diagonal boundary
  have allowed : FP.Result .div ((.reg 6 : Operand).eval preparedState.core) ((.reg 5 : Operand).eval preparedState.core)
      (encode (result s.core diagonal boundary)) := by
    simp only [FP.Result,FP.apply,Operand.eval,preparedState,ready_values.1,ready_values.2,decode_encode,result]
  have divide : Block [.fp .div 6 (.reg 6) (.reg 5)] preparedState.core
      (assign preparedState.core 6 (encode (result s.core diagonal boundary))) := .cons (.fp allowed) .nil
  have stored := run_sound (store_run (assign preparedState.core 6 (encode (result s.core diagonal boundary))) 6 12 output
    (by decide) (by decide) (by simpa [preparedState,assign,advance,address,wide,
      ready_frame.2.2.1,ready_frame.2.2.2.1,ready_frame.2.2.2.2.1,ready_frame.2.2.2.2.2.1] using ho))
  have body := Flow.sequence_data (ctx:=ctx) (s:=preparedState) (Indexed.scalar_block (block_append divide stored))
    (ready_frame.2.2.2.2.2.2.trans running)
  have joined := Flow.sequence_append readyRun body
  simpa [code,finish,preparedState,List.map_map,Function.comp_def,assign,advance,address,wide,
    ready_frame.2.2.2.2.1,ready_frame.2.2.2.2.2.1] using joined

end PtxTorchLean.Poisson.PTX.PreconditionUpdate
