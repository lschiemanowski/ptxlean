import PoissonPTX.DotWitnessLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail

def code (output : Word) : List Op :=
  [.load64 .shared 8 (.reg 3),.wide8 1 (.imm 0),.add64 2 (.reg 0) (.reg 1),
    .add64 2 (.reg 2) (.imm output),.store64 .global (.reg 2) (.reg 8)]

def prepared (s : PTX.State) (output word : Word) : PTX.State :=
  assign (assign (assign (assign s 8 word) 1 0) 2 (s.regs 0)) 2 (s.regs 0+output)

def finish (s : PTX.State) (output word : Word) : PTX.State :=
  put (prepared s output word) .global (s.regs 0+output).toNat word

def events (s : PTX.State) (output word : Word) : List Access :=
  [⟨.shared,⟨s.pc,false,(s.regs 3).toNat,word⟩⟩,
    ⟨.global,⟨s.pc+4,true,(s.regs 0+output).toNat,word⟩⟩]

theorem body_fetch (j : Fin 5) :
    (program count left right output scratch)[98+j.val]?=
      ((code output)[j.val]?).map (fun op => NativeFlow.Instr.flow (.data (.data op))) := by
  rw [show 98+j.val=96+(2+j.val) by omega,tail_fetch]
  fin_cases j <;> rfl

/-- Choose the final publication's exact bits as the candidate shared read.
The later admission proof must connect this read to the actual final store. -/
theorem block (s : PTX.State) (output word : Word)
    (shared : Valid64 s.sharedStart s.sharedBytes (s.regs 3).toNat)
    (global : Valid64 s.globalStart s.globalBytes (s.regs 0+output).toNat) :
    Local.Block (code output) s (events s output word) (finish s output word) := by
  have first : Data (.load64 .shared 8 (.reg 3)) s (assign s 8 word)
      (some ⟨.shared,⟨s.pc,false,(s.regs 3).toNat,word⟩⟩) := .load shared
  have second : Data (.wide8 1 (.imm 0)) (assign s 8 word) (assign (assign s 8 word) 1 0) none := by
    simpa [Operand.eval] using (Data.ordinary rfl (Eval.wide8 (s:=assign s 8 word) (dst:=1) (index:=.imm 0)))
  have third : Data (.add64 2 (.reg 0) (.reg 1)) (assign (assign s 8 word) 1 0)
      (assign (assign (assign s 8 word) 1 0) 2 (s.regs 0)) none := by
    simpa [assign,advance,Operand.eval] using
      (Data.ordinary rfl (Eval.add64 (s:=assign (assign s 8 word) 1 0) (dst:=2) (a:=.reg 0) (b:=.reg 1)))
  have fourth : Data (.add64 2 (.reg 2) (.imm output)) (assign (assign (assign s 8 word) 1 0) 2 (s.regs 0))
      (prepared s output word) none := by
    simpa [prepared,assign,advance,Operand.eval] using
      (Data.ordinary rfl (Eval.add64 (s:=assign (assign (assign s 8 word) 1 0) 2 (s.regs 0)) (dst:=2) (a:=.reg 2) (b:=.imm output)))
  have fifth : Data (.store64 .global (.reg 2) (.reg 8)) (prepared s output word) (finish s output word)
      (some ⟨.global,⟨s.pc+4,true,(s.regs 0+output).toNat,word⟩⟩) := by
    simpa [prepared,finish,assign,advance,Operand.eval,Nat.add_assoc] using
      (Data.store (s:=prepared s output word) (sp:=.global) (addr:=.reg 2) (src:=.reg 8)
        (by simpa [prepared,assign,advance,Operand.eval,PTX.State.start,PTX.State.bytes] using global))
  exact .cons first (.cons second (.cons third (.cons fourth (.cons fifth .nil))))

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail
