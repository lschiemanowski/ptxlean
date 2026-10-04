import PoissonPTX.DotInputFootprint

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

theorem input_load_site
    (fetch : (DotInput.inputProgram count left right scratch)[pc]?=
      some (.data (.data (.load64 sp dst addr)))) :
    sp=.global ∧ addr=.reg 2 ∧ (pc=11 ∨ pc=15) := by
  have small : pc<20 := by
    have h := (List.getElem?_eq_some_iff.mp fetch).1
    simpa only [DotInput.input_length] using h
  interval_cases pc <;>
    simp [DotInput.inputProgram,Flow.OperandWindow.program,Flow.OperandWindow.header,
      DotInput.setupCode,DotInput.body,loadCode,addressCode] at fetch
  all_goals obtain ⟨rfl,rfl,rfl⟩ := fetch; simp

theorem input_load_shape
    (actual : Flow.Observed.Eval ctx i s t (some access) index)
    (safe : inputSafe i=true) :
    ∃ dst addr, i=.data (.data (.load64 .global dst addr)) ∧
      access=⟨.global,⟨s.core.pc,false,(addr.eval s.core).toNat,access.data.value⟩⟩ ∧ index=none := by
  cases actual with
  | data one =>
    cases one with
    | data one =>
      cases one with
      | @load sp dst addr s value valid =>
        cases sp <;> simp_all [inputSafe]
      | store => cases safe

theorem input_no_index (actual : Flow.Observed.Eval ctx i s t access index)
    (safe : inputSafe i=true) : index=none := by
  cases actual with
  | data one => cases one <;> simp_all [inputSafe]
  | simple => rfl

/-- Modular address arithmetic agrees with the actual array element address
under explicit nonwrapping field bounds. -/
theorem input_address_exact (bounded : count<2^30) (inside : DotInput.cursor s<count)
    (room : (s.regs 0).toNat+off.toNat+count*8≤2^64) :
    (address s 12 off).toNat=(s.regs 0).toNat+DotInput.cursor s*8+off.toNat := by
  have wideBound : DotInput.cursor s*8<2^64 := by omega
  have baseBound : (s.regs 0).toNat+DotInput.cursor s*8<2^64 := by omega
  have totalBound : (s.regs 0).toNat+DotInput.cursor s*8+off.toNat<2^64 := by omega
  have cursorEq : (s.regs 12).toNat%2^32=DotInput.cursor s := by
    simp [DotInput.cursor,Kernel.u32,BitVec.toNat_setWidth]
  simp only [address,wide,cursorEq,BitVec.toNat_add,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt wideBound,Nat.mod_eq_of_lt baseBound,Nat.mod_eq_of_lt totalBound]

def InputWord (base : Word) (count : Nat) (left right : Word) (a : Access) : Prop :=
  a.space=.global ∧ a.data.store=false ∧ ∃ off∈[left,right], ∃ k<count,
    a.data.address=base.toNat+k*8+off.toNat

theorem input_access
    (fetch : (DotInput.inputProgram count left right scratch)[s.core.pc]?=some i)
    (actual : Flow.Observed.Eval ctx i s t (some a) index)
    (bounded : count<2^30) (ready : InputReady count left right s)
    (base : 2≤s.core.pc → s.core.regs 0=ctx.arena)
    (room : ∀ off∈[left,right], ctx.arena.toNat+off.toNat+count*8≤2^64) :
    InputWord ctx.arena count left right a := by
  obtain ⟨dst,addr,opcode,shape,_⟩ := input_load_shape actual (input_safe (List.mem_of_getElem? fetch))
  rw [opcode] at fetch
  obtain ⟨_,addressOperand,locationCase⟩ := input_load_site fetch
  subst addr
  have inside : DotInput.cursor s.core<count := ready.2.1 (by omega) (by omega)
  have baseReg := base (by omega)
  have location off (member : off∈[left,right]) := input_address_exact bounded inside
    (by rw [baseReg]; exact room off member)
  have observedAddress : a.data.address=(s.core.regs 2).toNat :=
    congrArg (fun access : Access => access.data.address) shape
  refine ⟨by rw [shape],by rw [shape],?_⟩
  rcases locationCase with first | second
  · refine ⟨left,by simp,DotInput.cursor s.core,inside,?_⟩
    have prepared := ready.2.2.2.2.1 first
    rw [observedAddress,prepared]
    simpa only [baseReg] using location left (by simp)
  · refine ⟨right,by simp,DotInput.cursor s.core,inside,?_⟩
    have prepared := ready.2.2.2.2.2 second
    rw [observedAddress,prepared]
    simpa only [baseReg] using location right (by simp)

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
