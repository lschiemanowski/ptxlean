import PoissonPTX.MemoryBlocks

namespace PtxTorchLean.Poisson.PTX.StoreZero

/-- The final initialization store uses an immediate positive-zero word. -/
def code (output : Word) : List Op := addressCode 12 output++[.store64 .global (.reg 2) (.imm 0)]

def finish (s : State) (output : Word) : State := put (addressed s 12 output) .global (address s 12 output).toNat 0

theorem executes (s : State) (output : Word)
    (valid : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    run (code output) s=some (finish s output) := by
  simp [code,run_append,address_run,run,eval,Operand.eval,State.start,State.bytes,valid,finish]

theorem block_eq (actual : Block (code output) s t)
    (valid : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) : t=finish s output :=
  Option.some.inj ((block_complete actual (by simp [code,addressCode,noFP])).symm.trans (executes s output valid))

theorem finish_global : (finish s output).global=write64 s.global (address s 12 output).toNat 0 := rfl

theorem finish_frame : (finish s output).globalStart=s.globalStart ∧
    (finish s output).globalBytes=s.globalBytes ∧ (finish s output).shared=s.shared ∧
    (finish s output).regs 0=s.regs 0 ∧ (finish s output).regs 12=s.regs 12 := by
  simp [finish,put,addressed,assign,advance]

end PtxTorchLean.Poisson.PTX.StoreZero
