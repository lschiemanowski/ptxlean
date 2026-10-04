import PoissonPTX.MemoryBlocks

namespace PtxTorchLean.Poisson.PTX.DividePair

/-- The initializer and restart divide registers 4 and 5, then publish the
same actual quotient word to z and p with separately executed stores. -/
def code (z p : Word) : List Op := [.fp .div 6 (.reg 4) (.reg 5)]++storeCode 6 12 z++storeCode 6 12 p

def first (s : State) (z value : Word) : State :=
  put (addressed (assign s 6 value) 12 z) .global (address s 12 z).toNat value

def finish (s : State) (z p value : Word) : State :=
  put (addressed (first s z value) 12 p) .global (address s 12 p).toNat value

def result (s : State) : Float := decode (s.regs 4)/decode (s.regs 5)

theorem executes (s : State) (z p : Word)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 z).toNat)
    (hp : Valid64 s.globalStart s.globalBytes (address s 12 p).toNat) :
    Block (code z p) s (finish s z p (encode (result s))) := by
  have divide : Block [.fp .div 6 (.reg 4) (.reg 5)] s (assign s 6 (encode (result s))) :=
    .cons (.fp (by simp [FP.Result,FP.apply,Operand.eval,result])) .nil
  have storeZ := run_sound (store_run (assign s 6 (encode (result s))) 6 12 z (by decide) (by decide)
    (by simpa [assign,advance,address,wide] using hz))
  have storeP := run_sound (store_run (first s z (encode (result s))) 6 12 p (by decide) (by decide)
    (by simpa [first,put,assign,advance,addressed,address,wide] using hp))
  have storeZ' : Block (storeCode 6 12 z) (assign s 6 (encode (result s))) (first s z (encode (result s))) := by
    simpa [first,assign,advance,address,wide] using storeZ
  simpa [code,finish,first,put,assign,advance,addressed,address,wide] using
    block_append (block_append divide storeZ') storeP

theorem state_result (actual : Block (code z p) s final)
    (hz : Valid64 s.globalStart s.globalBytes (address s 12 z).toNat)
    (hp : Valid64 s.globalStart s.globalBytes (address s 12 p).toNat) :
    ∃ value, final=finish s z p value ∧ decode value=result s := by
  simp only [code,List.cons_append,List.nil_append] at actual
  cases actual with
  | cons divide rest =>
    cases divide with
    | @fp _ _ _ _ _ value allowed =>
      have valueEq : decode value=result s := allowed
      obtain ⟨middle,storeZ,storeP⟩ := block_split (storeCode 6 12 z) (storeCode 6 12 p) rest
      have mid : middle=first s z value := by
        simpa [first,assign,advance,address,wide] using store_block_eq storeZ (by decide) (by decide)
          (by simpa [assign,advance,address,wide] using hz)
      subst middle
      have last := store_block_eq storeP (by decide) (by decide)
        (by simpa [first,put,assign,advance,addressed,address,wide] using hp)
      refine ⟨value,?_,valueEq⟩
      simpa [finish,first,put,assign,advance,addressed,address,wide] using last

theorem finish_global : (finish s z p value).global=
    write64 (write64 s.global (address s 12 z).toNat value) (address s 12 p).toNat value := by
  simp [finish,first,put,assign,advance,addressed]

theorem finish_frame : (finish s z p value).globalStart=s.globalStart ∧
    (finish s z p value).globalBytes=s.globalBytes ∧ (finish s z p value).shared=s.shared ∧
    (finish s z p value).regs 0=s.regs 0 ∧ (finish s z p value).regs 12=s.regs 12 := by
  simp [finish,first,put,assign,advance,addressed]

end PtxTorchLean.Poisson.PTX.DividePair
