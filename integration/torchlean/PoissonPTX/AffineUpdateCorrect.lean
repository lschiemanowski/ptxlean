import PoissonPTX.AffineUpdate

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

theorem executes (s : State) (coefficient input shift output : Word)
    (hc : Valid64 s.globalStart s.globalBytes (s.regs 0+coefficient).toNat)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    Block (code coefficient input shift output) s
      (finish s coefficient input shift output (encode (product s coefficient input)) (encode (result s coefficient input shift))) := by
  have inputs := load_executes s coefficient input shift hc hi hz
  have mul : Block [.fp .mul 10 (.reg 4) (.reg 5)] (loaded s coefficient input shift)
      (assign (loaded s coefficient input shift) 10 (encode (product s coefficient input))) := by
    apply Block.cons (Eval.fp ?_) Block.nil
    simp [FP.Result,FP.apply,Operand.eval,product,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide]
  have add : Block [.fp .add 6 (.reg 6) (.reg 10)]
      (assign (loaded s coefficient input shift) 10 (encode (product s coefficient input)))
      (assign (assign (loaded s coefficient input shift) 10 (encode (product s coefficient input))) 6 (encode (result s coefficient input shift))) := by
    apply Block.cons (Eval.fp ?_) Block.nil
    simp [FP.Result,FP.apply,Operand.eval,result,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide]
  have stored := run_sound (store_run
    (assign (assign (loaded s coefficient input shift) 10 (encode (product s coefficient input))) 6 (encode (result s coefficient input shift))) 6 12 output
    (by decide) (by decide) (by simpa [loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using ho))
  have joined := block_append (block_append (block_append inputs mul) add) stored
  simpa [code,finish,List.append_assoc,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using joined

/-- Universal decoded output and byte frame for the actual update body.
No initial disjointness is needed for this scalar theorem: all operands are
loaded before the only store. Concurrent in-place reads need separate admission. -/
theorem correct (actual : Block (code coefficient input shift output) s final)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    decode (read64 final.global (address s 12 output).toNat)=result s coefficient input shift ∧
    (∀ p, p<(address s 12 output).toNat ∨ (address s 12 output).toNat+8≤p → final.global p=s.global p) ∧
    final.shared=s.shared := by
  obtain ⟨middle,inputs,rest⟩ := block_split
    (ScalarLoad.code 4 coefficient ++ loadCode 5 12 input ++ loadCode 6 12 shift)
    ([.fp .mul 10 (.reg 4) (.reg 5),.fp .add 6 (.reg 6) (.reg 10)] ++ storeCode 6 12 output)
    (by simpa [code,List.append_assoc] using actual)
  have same := loads_eq inputs hi hz
  subst middle
  cases rest with
  | cons mul rest =>
    cases mul with
    | @fp _ _ _ _ _ mulWord productAllowed =>
      have productEq : decode mulWord=product s coefficient input := by
        simpa [FP.Result,FP.apply,Operand.eval,product,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using productAllowed
      cases rest with
      | cons add rest =>
        cases add with
        | @fp _ _ _ _ _ value allowed =>
          have resultEq : decode value=result s coefficient input shift := by
            simpa [FP.Result,FP.apply,Operand.eval,result,productEq,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using allowed
          have finalEq := store_block_eq rest (by decide) (by decide)
            (by simpa [loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using ho)
          subst final
          refine ⟨?_,?_,rfl⟩
          · simpa [put,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using resultEq
          · intro p outside
            simpa [put,loaded,left,scalar,ScalarLoad.loaded,ScalarLoad.addressed,assign,advance,addressed,address,wide] using
              write64_outside s.global (address s 12 output).toNat value p outside

end PtxTorchLean.Poisson.PTX.AffineUpdate
