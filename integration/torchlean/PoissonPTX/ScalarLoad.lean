import PoissonPTX.MemoryBlocks

namespace PtxTorchLean.Poisson.PTX.ScalarLoad

/-- A scalar arena field uses the emitted immediate-zero wide multiply,
followed by the same two address additions as vector fields. -/
def code (dst : Nat) (offset : Word) : List Op :=
  [.wide8 1 (.imm 0),.add64 2 (.reg 0) (.reg 1),.add64 2 (.reg 2) (.imm offset),.load64 .global dst (.reg 2)]

def addressed (s : State) (offset : Word) : State :=
  assign (assign (assign s 1 0) 2 (s.regs 0)) 2 (s.regs 0+offset)

def loaded (s : State) (dst : Nat) (offset : Word) : State :=
  assign (addressed s offset) dst (read64 s.global (s.regs 0+offset).toNat)

theorem executes (s : State) (dst : Nat) (offset : Word)
    (valid : Valid64 s.globalStart s.globalBytes (s.regs 0+offset).toNat) :
    run (code dst offset) s=some (loaded s dst offset) := by
  simp [code,run,eval,Operand.eval,loaded,addressed,assign,advance,State.start,State.bytes,State.memory]
  simpa only [BitVec.toNat_add] using valid

theorem block_eq (actual : Block (code dst offset) s final) :
    final=loaded s dst offset := by
  cases actual with
  | cons first rest =>
    cases first
    cases rest with
    | cons second rest =>
      cases second
      cases rest with
      | cons third rest =>
        cases third
        cases rest with
        | cons last done =>
          cases last
          cases done
          simp [loaded,addressed,Operand.eval,assign,advance,State.memory]

end PtxTorchLean.Poisson.PTX.ScalarLoad
