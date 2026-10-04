import PoissonPTX.ScalarLoad

namespace PtxTorchLean.Poisson.PTX.RegisterUpdate

/-- A scalar coefficient already loaded in register 4 is reused. The update
loads two vector words, rounds the product, combines it, then writes one word. -/
def code (combine : FP) (input shift output : Word) : List Op :=
  loadCode 5 12 input ++ loadCode 6 12 shift ++
    [.fp .mul 10 (.reg 4) (.reg 5),.fp combine 6 (.reg 6) (.reg 10)] ++ storeCode 6 12 output

def left (s : State) (input : Word) : State :=
  assign (addressed s 12 input) 5 (read64 s.global (address s 12 input).toNat)

def loaded (s : State) (input shift : Word) : State :=
  assign (addressed (left s input) 12 shift) 6 (read64 s.global (address s 12 shift).toNat)

def product (s : State) (input : Word) : Float :=
  decode (s.regs 4)*decode (read64 s.global (address s 12 input).toNat)

def result (combine : FP) (s : State) (input shift : Word) : Float :=
  combine.apply (decode (read64 s.global (address s 12 shift).toNat)) (product s input)

def finish (s : State) (input shift output mulWord value : Word) : State :=
  put (addressed (assign (assign (loaded s input shift) 10 mulWord) 6 value) 12 output)
    .global (address s 12 output).toNat value

theorem loads_execute (s : State) (input shift : Word)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat) :
    Block (loadCode 5 12 input ++ loadCode 6 12 shift) s (loaded s input shift) := by
  have first := run_sound (load_run s 5 12 input hi)
  have second := run_sound (load_run (left s input) 6 12 shift
    (by simpa [left,assign,advance,addressed,address,wide] using hz))
  exact block_append first (by simpa [loaded,left,assign,advance,addressed,address,wide] using second)

theorem loads_eq (actual : Block (loadCode 5 12 input ++ loadCode 6 12 shift) s final)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat) : final=loaded s input shift := by
  obtain ⟨middle,first,second⟩ := block_split (loadCode 5 12 input) (loadCode 6 12 shift) actual
  have same : middle=left s input := load_block_eq first hi
  subst middle
  simpa [loaded,left,assign,advance,addressed,address,wide] using
    load_block_eq second (by simpa [left,assign,advance,addressed,address,wide] using hz)

theorem executes (s : State) (combine : FP) (input shift output : Word)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    Block (code combine input shift output) s
      (finish s input shift output (encode (product s input)) (encode (result combine s input shift))) := by
  have inputs := loads_execute s input shift hi hz
  have mul : Block [.fp .mul 10 (.reg 4) (.reg 5)] (loaded s input shift)
      (assign (loaded s input shift) 10 (encode (product s input))) := by
    apply Block.cons (Eval.fp ?_) Block.nil
    simp [FP.Result,FP.apply,Operand.eval,product,loaded,left,assign,advance,addressed,address,wide]
  have add : Block [.fp combine 6 (.reg 6) (.reg 10)]
      (assign (loaded s input shift) 10 (encode (product s input)))
      (assign (assign (loaded s input shift) 10 (encode (product s input))) 6 (encode (result combine s input shift))) := by
    apply Block.cons (Eval.fp ?_) Block.nil
    simp [FP.Result,Operand.eval,result,loaded,left,assign,advance,addressed,address,wide]
  have stored := run_sound (store_run
    (assign (assign (loaded s input shift) 10 (encode (product s input))) 6 (encode (result combine s input shift))) 6 12 output
    (by decide) (by decide) (by simpa [loaded,left,assign,advance,addressed,address,wide] using ho))
  simpa [code,finish,List.append_assoc,loaded,left,assign,advance,addressed,address,wide] using
    block_append (block_append (block_append inputs mul) add) stored

/-- Retain the actual permitted product and output encodings, as well as the
whole post-state, for composition with later instructions. -/
theorem state_result (actual : Block (code combine input shift output) s final)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 input).toNat)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 shift).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    ∃ mulWord value, final=finish s input shift output mulWord value ∧
      decode mulWord=product s input ∧ decode value=result combine s input shift := by
  obtain ⟨middle,inputs,rest⟩ := block_split
    (loadCode 5 12 input ++ loadCode 6 12 shift)
    ([.fp .mul 10 (.reg 4) (.reg 5),.fp combine 6 (.reg 6) (.reg 10)] ++ storeCode 6 12 output)
    (by simpa [code,List.append_assoc] using actual)
  have same := loads_eq inputs hi hz
  subst middle
  cases rest with
  | cons mul rest =>
    cases mul with
    | @fp _ _ _ _ _ mulWord productAllowed =>
      have productEq : decode mulWord=product s input := by
        simpa [FP.Result,FP.apply,Operand.eval,product,loaded,left,assign,advance,addressed,address,wide] using productAllowed
      cases rest with
      | cons add rest =>
        cases add with
        | @fp _ _ _ _ _ value allowed =>
          have resultEq : decode value=result combine s input shift := by
            simpa [FP.Result,Operand.eval,result,productEq,loaded,left,assign,advance,addressed,address,wide] using allowed
          have finalEq := store_block_eq rest (by decide) (by decide)
            (by simpa [loaded,left,assign,advance,addressed,address,wide] using ho)
          exact ⟨mulWord,value,finalEq,productEq,resultEq⟩

end PtxTorchLean.Poisson.PTX.RegisterUpdate
