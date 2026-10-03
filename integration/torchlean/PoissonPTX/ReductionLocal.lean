import PoissonPTX.ConcurrentLocalBlock
import PoissonPTX.ReductionCorrect

/-! Symbolic local execution witnesses with arbitrary initial words and chosen
load words. These are later joined into full-block rounds and admitted sources. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

def sum (a b : Word) : Word := encode (decode a+decode b)
def prepared (s : PTX.State) : PTX.State :=
  assign (assign s 1 (wide s 14)) 2 (s.regs 3+wide s 14)
def loaded (s : PTX.State) (left right : Word) : PTX.State :=
  assign (assign (prepared s) 4 left) 5 right

def finish (s : PTX.State) (left right : Word) : PTX.State :=
  put (assign (loaded s left right) 8 (sum left right)) .shared
    (PTX.Reduction.Update.address s).toNat (sum left right)

def updateEvents (s : PTX.State) (offset left right : Word) : List Access :=
  [⟨.shared,⟨s.pc+2,false,(PTX.Reduction.Update.address s).toNat,left⟩⟩,
   ⟨.shared,⟨s.pc+3,false,(PTX.Reduction.Update.address s+offset).toNat,right⟩⟩,
   ⟨.shared,⟨s.pc+5,true,(PTX.Reduction.Update.address s).toNat,sum left right⟩⟩]

theorem update_block (s : PTX.State) (offset left right : Word)
    (valid : PTX.Reduction.Update.Valid s offset) :
    Local.Block (PTX.Reduction.Update.code offset) s (updateEvents s offset left right) (finish s left right) := by
  rcases valid with ⟨vl,vr⟩
  have first : Data (.wide8 1 (.reg 14)) s (assign s 1 (wide s 14)) none := .ordinary rfl (.wide8)
  have second : Data (.add64 2 (.reg 3) (.reg 1)) (assign s 1 (wide s 14)) (prepared s) none := by
    simpa [prepared,assign,advance,Operand.eval] using
      (Data.ordinary rfl (Eval.add64 (s:=assign s 1 (wide s 14)) (dst:=2) (a:=.reg 3) (b:=.reg 1)))
  have third : Data (.load64 .shared 4 (.reg 2)) (prepared s) (assign (prepared s) 4 left)
      (some ⟨.shared,⟨s.pc+2,false,(PTX.Reduction.Update.address s).toNat,left⟩⟩) := by
    simpa [prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,Nat.add_assoc] using
      (Data.load (s:=prepared s) (sp:=.shared) (dst:=4) (addr:=.reg 2) (word:=left)
        (by simpa [prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,PTX.State.start,PTX.State.bytes] using vl))
  have fourth : Data (.load64 .shared 5 (.offset 2 offset)) (assign (prepared s) 4 left) (loaded s left right)
      (some ⟨.shared,⟨s.pc+3,false,(PTX.Reduction.Update.address s+offset).toNat,right⟩⟩) := by
    simpa [loaded,prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,Nat.add_assoc] using
      (Data.load (s:=assign (prepared s) 4 left) (sp:=.shared) (dst:=5) (addr:=.offset 2 offset) (word:=right)
        (by simpa [prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,PTX.State.start,PTX.State.bytes] using vr))
  have fifth : Data (.fp .add 8 (.reg 4) (.reg 5)) (loaded s left right)
      (assign (loaded s left right) 8 (sum left right)) none := by
    apply Data.ordinary rfl
    apply Eval.fp
    simp [FP.Result,FP.apply,sum,loaded,Operand.eval,assign,advance]
  have sixth : Data (.store64 .shared (.reg 2) (.reg 8)) (assign (loaded s left right) 8 (sum left right))
      (finish s left right) (some ⟨.shared,⟨s.pc+5,true,(PTX.Reduction.Update.address s).toNat,sum left right⟩⟩) := by
    simpa [finish,loaded,prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,Nat.add_assoc] using
      (Data.store (s:=assign (loaded s left right) 8 (sum left right)) (sp:=.shared) (addr:=.reg 2) (src:=.reg 8)
        (by simpa [loaded,prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,PTX.State.start,PTX.State.bytes] using vl))
  exact .cons first (.cons second (.cons third (.cons fourth (.cons fifth (.cons sixth .nil)))))

def initialEvents (s : PTX.State) : List Access :=
  [⟨.shared,⟨s.pc+2,true,(PTX.Reduction.Update.address s).toNat,s.regs 8⟩⟩]

theorem initial_block (s : PTX.State) (valid : SharedStore.Valid s 0) :
    Local.Block (SharedStore.code 0 8) s (initialEvents s) (SharedStore.finish s 0 8) := by
  have first : Data (.wide8 1 (.reg 14)) s (assign s 1 (wide s 14)) none := .ordinary rfl (.wide8)
  have second : Data (.add64 2 (.reg 3) (.reg 1)) (assign s 1 (wide s 14)) (prepared s) none := by
    simpa [prepared,assign,advance,Operand.eval] using
      (Data.ordinary rfl (Eval.add64 (s:=assign s 1 (wide s 14)) (dst:=2) (a:=.reg 3) (b:=.reg 1)))
  have third : Data (.store64 .shared (.offset 2 0) (.reg 8)) (prepared s)
      (SharedStore.finish s 0 8) (some ⟨.shared,⟨s.pc+2,true,(PTX.Reduction.Update.address s).toNat,s.regs 8⟩⟩) := by
    simpa [SharedStore.finish,SharedStore.location,prepared,assign,advance,Operand.eval,PTX.Reduction.Update.address,Nat.add_assoc] using
      (Data.store (s:=prepared s) (sp:=.shared) (addr:=.offset 2 0) (src:=.reg 8)
        (by simpa [SharedStore.Valid,SharedStore.location,prepared,assign,advance,Operand.eval,PTX.State.start,PTX.State.bytes] using valid))
  exact .cons first (.cons second (.cons third .nil))

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
