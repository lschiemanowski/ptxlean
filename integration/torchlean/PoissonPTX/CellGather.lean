import PoissonPTX.IndexedMemory
import PoissonPTX.SharedStore

namespace PtxTorchLean.Poisson.PTX.CellGather
open Indexed

/-- Connectivity is a u32 array; the source and shared plane are binary64. -/
def code (width : Nat) (cells source : Word) : List Indexed.Instr :=
  [.mad32 13 15 (BitVec.ofNat 32 (width*width)) 14,
   .wide4 1 13,.data (.add64 2 (.reg 0) (.reg 1)),
   .data (.add64 2 (.reg 2) (.imm cells)),.load32 18 2,
   .data (.wide8 1 (.reg 18)),.data (.add64 2 (.reg 0) (.reg 1)),
   .data (.add64 2 (.reg 2) (.imm source)),.data (.load64 .global 11 (.reg 2)),
   .data (.wide8 1 (.reg 14)),.data (.add64 2 (.reg 3) (.reg 1)),
   .data (.store64 .shared (.offset 2 0) (.reg 11))]

def index (s : State) (width : Nat) : BitVec 32 :=
  Kernel.u32 (s.regs 15)*BitVec.ofNat 32 (width*width)+Kernel.u32 (s.regs 14)

def connectivityAddress (s : State) (width : Nat) (cells : Word) : Word :=
  address32 (s.regs 0) (index s width) cells

def node (s : State) (width : Nat) (cells : Word) : BitVec 32 :=
  read32 s.global (connectivityAddress s width cells).toNat

def sourceAddress (s : State) (width : Nat) (cells source : Word) : Word :=
  address64 (s.regs 0) (node s width cells) source

def value (s : State) (width : Nat) (cells source : Word) : Word :=
  read64 s.global (sourceAddress s width cells source).toNat

def destination (s : State) : Word :=
  s.regs 3+BitVec.ofNat 64 ((Kernel.u32 (s.regs 14)).toNat*8)

/-- A snapshot-level safety condition on actual load/store addresses. The
layout theorem derives it from allocated arrays and valid connectivity. -/
def Valid (s : State) (width : Nat) (cells source : Word) : Prop :=
  Valid32 s.globalStart s.globalBytes (connectivityAddress s width cells).toNat ∧
  Valid64 s.globalStart s.globalBytes (sourceAddress s width cells source).toNat ∧
  Valid64 s.sharedStart s.sharedBytes (destination s).toNat

/-- Full fetched effects, including scratch registers and the original bits. -/
def finish (s : State) (width : Nat) (cells source : Word) : State :=
  let r := Function.update s.regs 13 ((index s width).setWidth 64)
  let r := Function.update r 18 ((node s width cells).setWidth 64)
  let r := Function.update r 11 (value s width cells source)
  let r := Function.update r 1 (BitVec.ofNat 64 ((Kernel.u32 (s.regs 14)).toNat*8))
  let r := Function.update r 2 (destination s)
  {s with pc:=s.pc+12,regs:=r, shared:=write64 s.shared (destination s).toNat (value s width cells source)}

theorem execution (valid : Valid s width cells source) :
    Indexed.run (code width cells source) s=some (finish s width cells source) := by
  obtain ⟨conn,load,store⟩ := valid
  have low (v : BitVec 32) : v.toNat%4294967296=v.toNat := Nat.mod_eq_of_lt v.isLt
  have wide4 (x : Nat) : (x%4294967296*4)%18446744073709551616=x%4294967296*4 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  have wide8 (x : Nat) : (x%4294967296*8)%18446744073709551616=x%4294967296*8 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  simp [connectivityAddress,sourceAddress,destination,address32,address64,index,node,Kernel.u32,wide4,wide8,Nat.add_assoc] at conn load store
  simp [code,Indexed.run,Indexed.eval,Indexed.mad,Indexed.wide,PTX.eval,
    connectivityAddress,sourceAddress,destination,address32,address64,index,node,value,
    Kernel.u32,finish,assign,advance,put,Operand.eval,State.start,State.bytes,State.memory,
    wide4,wide8,low,Nat.add_assoc,conn,load,store]
  funext r
  by_cases one : r=1 <;> by_cases two : r=2 <;> simp [Function.update,one,two]

theorem correct (run : Indexed.Block (code width cells source) s t)
    (valid : Valid s width cells source) : t=finish s width cells source := by
  have executed := Indexed.run_complete run (by simp [code,Indexed.noFP,PTX.noFP])
  rw [execution valid] at executed
  exact (Option.some.inj executed).symm

/-- The local gather is a bit copy, including signed zero and NaN payloads. -/
theorem stored (run : Indexed.Block (code width cells source) s t)
    (valid : Valid s width cells source) :
    read64 t.shared (destination s).toNat=value s width cells source ∧ t.global=s.global := by
  rw [correct run valid]
  exact ⟨read64_write64 _ _ _,rfl⟩

theorem registers (run : Indexed.Block (code width cells source) s t)
    (valid : Valid s width cells source)
    (untouched : r≠1 ∧ r≠2 ∧ r≠11 ∧ r≠13 ∧ r≠18) : t.regs r=s.regs r := by
  rw [correct run valid]
  simp [finish,Function.update,untouched]

theorem fetched_correct (pre suffix : List Indexed.Instr) (pc : s.pc=pre.length)
    (run : Indexed.Runs (pre++code width cells source++suffix) s t)
    (done : t.pc=pre.length+(code width cells source).length)
    (valid : Valid s width cells source) : t=finish s width cells source :=
  correct (Indexed.fetched_block pre _ suffix run pc done) valid

theorem fetched_exists (pre suffix : List Indexed.Instr) (pc : s.pc=pre.length)
    (valid : Valid s width cells source) :
    ∃ t, Indexed.Runs (pre++code width cells source++suffix) s t ∧ t.pc=pre.length+12 := by
  have block := Indexed.run_sound (execution valid)
  exact ⟨finish s width cells source,Indexed.block_fetched block pre suffix pc,
    by simp [finish,pc]⟩

end PtxTorchLean.Poisson.PTX.CellGather
