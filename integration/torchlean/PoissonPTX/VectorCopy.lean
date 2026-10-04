import PoissonPTX.MemoryBlocks

namespace PtxTorchLean.Poisson.PTX.VectorCopy

def code (source output : Word) : List Op := loadCode 4 12 source++storeCode 4 12 output

def loaded (s : State) (source : Word) : State :=
  assign (addressed s 12 source) 4 (read64 s.global (address s 12 source).toNat)

def finish (s : State) (source output : Word) : State :=
  put (addressed (loaded s source) 12 output) .global (address s 12 output).toNat
    (read64 s.global (address s 12 source).toNat)

theorem executes (s : State) (source output : Word)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 source).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) :
    run (code source output) s=some (finish s source output) := by
  rw [code,run_append,load_run s 4 12 source hi]
  have next := store_run (loaded s source) 4 12 output (by decide) (by decide)
    (by simpa [loaded,assign,advance,addressed,address,wide] using ho)
  simpa [finish,loaded,assign,advance,addressed,address,wide] using next

theorem block_eq (actual : Block (code source output) s t)
    (hi : Valid64 s.globalStart s.globalBytes (address s 12 source).toNat)
    (ho : Valid64 s.globalStart s.globalBytes (address s 12 output).toNat) : t=finish s source output :=
  Option.some.inj ((block_complete actual (by simp [code,loadCode,storeCode,addressCode,noFP])).symm.trans (executes s source output hi ho))

theorem finish_global : (finish s source output).global=
    write64 s.global (address s 12 output).toNat (read64 s.global (address s 12 source).toNat) := by
  simp [finish,loaded,put,assign,advance,addressed]

theorem finish_frame : (finish s source output).globalStart=s.globalStart ∧
    (finish s source output).globalBytes=s.globalBytes ∧ (finish s source output).shared=s.shared ∧
    (finish s source output).regs 0=s.regs 0 ∧ (finish s source output).regs 12=s.regs 12 ∧
    (finish s source output).regs 4=read64 s.global (address s 12 source).toNat := by
  simp [finish,loaded,put,assign,advance,addressed]

theorem finish_address : address (finish s source output) 12 field=address s 12 field := by
  simp only [address,wide,finish_frame.2.2.2.1,finish_frame.2.2.2.2.1]

end PtxTorchLean.Poisson.PTX.VectorCopy
