import PoissonPTX.IndexedBlocks

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Cursor/end use registers 19/20; existing address, index, value and
accumulator registers retain their generated PTX meanings. -/
def lookupCode (entries element : Word) : List Indexed.Instr :=
  [.wide4 1 19,.data (.add64 2 (.reg 0) (.reg 1)),
   .data (.add64 2 (.reg 2) (.imm entries)),.load32 13 2,
   .data (.wide8 1 (.reg 13)),.data (.add64 2 (.reg 0) (.reg 1)),
   .data (.add64 2 (.reg 2) (.imm element)),.data (.load64 .global 4 (.reg 2))]

def indexAddress (s : State) (entries : Word) : Word := address32 (s.regs 0) (Kernel.u32 (s.regs 19)) entries
def index (s : State) (entries : Word) : BitVec 32 := read32 s.global (indexAddress s entries).toNat
def valueAddress (s : State) (entries element : Word) : Word := address64 (s.regs 0) (index s entries) element
def value (s : State) (entries element : Word) : Word := read64 s.global (valueAddress s entries element).toNat

def Valid (s : State) (entries element : Word) : Prop :=
  Valid32 s.globalStart s.globalBytes (indexAddress s entries).toNat ∧
  Valid64 s.globalStart s.globalBytes (valueAddress s entries element).toNat

def loaded (s : State) (entries element : Word) : State :=
  let r := Function.update s.regs 13 ((index s entries).setWidth 64)
  let r := Function.update r 1 (BitVec.ofNat 64 ((index s entries).toNat*8))
  let r := Function.update r 2 (valueAddress s entries element)
  let r := Function.update r 4 (value s entries element)
  {s with pc:=s.pc+8,regs:=r}

theorem lookup_execution (valid : Valid s entries element) :
    Indexed.run (lookupCode entries element) s=some (loaded s entries element) := by
  obtain ⟨vi,vv⟩ := valid
  have low (v : BitVec 32) : v.toNat%4294967296=v.toNat := Nat.mod_eq_of_lt v.isLt
  have wide4 (x : Nat) : (x%4294967296*4)%18446744073709551616=x%4294967296*4 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  have wide8 (x : Nat) : (x%4294967296*8)%18446744073709551616=x%4294967296*8 := by
    apply Nat.mod_eq_of_lt; have := Nat.mod_lt x (by decide : 0<4294967296); omega
  simp [indexAddress,valueAddress,address32,address64,index,Kernel.u32,wide4,wide8,Nat.add_assoc] at vi vv
  simp [lookupCode,Indexed.run,Indexed.eval,Indexed.wide,PTX.eval,indexAddress,valueAddress,
    address32,address64,index,value,Kernel.u32,loaded,assign,advance,Operand.eval,State.start,
    State.bytes,State.memory,wide4,wide8,low,Nat.add_assoc,vi,vv]
  funext r
  by_cases one : r=1 <;> by_cases two : r=2 <;> simp [Function.update,one,two]

theorem lookup_correct (run : Indexed.Block (lookupCode entries element) s t)
    (valid : Valid s entries element) : t=loaded s entries element := by
  have executed := Indexed.run_complete run (by simp [lookupCode,Indexed.noFP,PTX.noFP])
  rw [lookup_execution valid] at executed
  exact (Option.some.inj executed).symm

/-- Loop body: dereference one cell-entry index, add one binary64 contribution,
and advance the unsigned cursor. -/
def body (entries element : Word) : List Indexed.Instr := lookupCode entries element++[
  .data (.fp .add 8 (.reg 8) (.reg 4)),.data (.add32 19 (.reg 19) (.imm 1))]

/-- Preserve all initial memory, allocation and stable addressing information. -/
def Stable (s t : State) : Prop :=
  t.global=s.global ∧ t.shared=s.shared ∧ t.globalStart=s.globalStart ∧ t.globalBytes=s.globalBytes ∧
  t.sharedStart=s.sharedStart ∧ t.sharedBytes=s.sharedBytes ∧ t.regs 0=s.regs 0 ∧ t.regs 20=s.regs 20

theorem body_correct (run : Indexed.Block (body entries element) s t) (valid : Valid s entries element) :
    decode (t.regs 8)=decode (s.regs 8)+decode (value s entries element) ∧
    t.regs 19=add32 (s.regs 19) 1 ∧ Stable s t := by
  obtain ⟨middle,loads,rest⟩ := Indexed.split (lookupCode entries element) _ run
  have same := lookup_correct loads valid
  subst middle
  cases rest with | cons add rest =>
    cases add with | data add =>
      cases add with | fp allowed =>
        cases rest with | cons increment rest =>
          cases increment with | data increment =>
            cases increment
            cases rest
            simpa [Stable,loaded,assign,advance,Operand.eval,FP.Result,FP.apply] using allowed

theorem body_exists (s : State) (valid : Valid s entries element) :
    ∃ t, Indexed.Block (body entries element) s t := by
  let ready := loaded s entries element
  obtain ⟨word,allowed⟩ := FP.result_exists .add (ready.regs 8) (ready.regs 4)
  let added := assign ready 8 word
  refine ⟨assign added 19 (add32 (added.regs 19) 1),Indexed.append
    (Indexed.run_sound (lookup_execution valid)) ?_⟩
  exact .cons (.data (.fp allowed)) (.cons (.data .add32) .nil)

end PtxTorchLean.Poisson.PTX.Assembly
