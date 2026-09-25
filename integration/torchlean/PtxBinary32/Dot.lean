import PtxBinary32.Total
import PtxBinary32Error

/-! A fetched left-to-right dot-product loop in the isolated word arena.
The instruction count and postcondition hold for every floating-point choice. -/
namespace Ptx.Scalar.Dot
open Mixed

/-- The order of the multiply/add results is part of the specification. -/
inductive Fold : List (Word × Word) → Word → Word → Prop
  | nil : Fold [] acc acc
  | cons : Ptx.Binary32.Error.AffineResults x.1 x.2 acc product next →
      Fold xs next out → Fold (x::xs) acc out

def pointer (i : Nat) : Address := BitVec.ofNat 64 (4*i)
def initI : Scalar.Instr := .plain (.mov32 4 (.imm 0))
def test : Scalar.Instr := .plain (.setp .eq 0 (.reg 3) (.imm 0))
def done : Scalar.Instr := ⟨.pred 0 true, .bra 11⟩
def load (i : Nat) : Scalar.Instr := .plain (.load i (.reg i))
def multiply : Scalar.Binary32.Instr := ⟨.always,.mul,2,.reg 0,.reg 1⟩
def addition : Scalar.Binary32.Instr := ⟨.always,.add,4,.reg 2,.reg 4⟩
def increment (i : Nat) : Scalar.Instr := .plain (.add64 i (.reg i) (.imm 4))
def decrement : Scalar.Instr := .plain (.bin32 .sub 3 (.reg 3) (.imm 1))
def back : Scalar.Instr := .plain (.bra 1)
def store : Scalar.Instr := .plain (.store (.reg 2) (.reg 4))
def exit : Scalar.Instr := .plain .exit

def program : List Mixed.Instr :=
  [.scalar initI,.scalar test,.scalar done,.scalar (load 0),.scalar (load 1),
   .binary32 multiply,.binary32 addition,.scalar (increment 0),.scalar (increment 1),
   .scalar decrement,.scalar back,.scalar store,.scalar exit]

/-- Concrete input values in two contiguous slices of one supplied allocation. -/
def Stored (memory : List Word) (left right : Nat) (xs : List (Word × Word)) : Prop :=
  ∀ i x, xs[i]? = some x → memory[left+i]? = some x.1 ∧ memory[right+i]? = some x.2

structure Bounds (memory : List Word) (left right : Nat) (xs : List (Word × Word)) : Prop where
  count : xs.length < 2^32
  leftExtent : left+xs.length ≤ memory.length
  rightExtent : right+xs.length ≤ memory.length
  leftPointer : 4*(left+xs.length) < 2^64
  rightPointer : 4*(right+xs.length) < 2^64

def Post (xs : List (Word × Word)) (acc : Word) (memory : List Word) (output : Nat)
    (final : State) : Prop :=
  ∃ out, Fold xs acc out ∧ final.memory = memory.set output out

/-- Launch arguments and initId storage are supplied; r4 need not be initId. -/
def initial (s : State) (left right output count : Nat) : State :=
  {s with
    pc := 0,
    addrs := update (update (update s.addrs 0 (pointer left)) 1 (pointer right)) 2 (pointer output),
    regs := update s.regs 3 (BitVec.ofNat 32 count)}

private theorem pointer_index (memory : List Word) (i : Nat)
    (bound : i < memory.length) (noWrap : 4*i < 2^64) :
    addressIndex memory (pointer i) = .ok i := by
  have hn : 4*i < 18446744073709551616 := noWrap
  simp [addressIndex,pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,bound]

private theorem stored_tail (stored : Stored memory left right (x::xs)) :
    Stored memory (left+1) (right+1) xs := by
  intro i y hy
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using stored (i+1) y hy

private theorem bounds_tail (bounds : Bounds memory left right (x::xs)) :
    Bounds memory (left+1) (right+1) xs := by
  rcases bounds with ⟨hc,hl,hr,hpl,hpr⟩
  simp only [List.length_cons] at *
  constructor <;> omega

/-- A certificate for the remaining loop, including all arithmetic choices. -/
theorem total_loop (xs : List (Word × Word)) (s : State) (left right : Nat) (acc : Word)
    (pc : s.pc = 1) (count : s.regs 3 = BitVec.ofNat 32 xs.length)
    (accumulator : s.regs 4 = acc)
    (lp : s.addrs 0 = pointer left) (rp : s.addrs 1 = pointer right)
    (output : ValidAddress s.memory (s.addrs 2))
    (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs) :
    Total target program (Post xs acc s.memory ((s.addrs 2).toNat/4)) (10*xs.length+4) s := by
  induction xs generalizing s left right acc with
  | nil =>
    let s1 := {s with pc := 2,preds := update s.preds 0 true}
    let s2 := {s1 with pc := 11}
    let s3 := {s2 with pc := 12,memory := s.memory.set ((s.addrs 2).toNat/4) acc}
    have hi := addressIndex_ok_iff.mpr (And.intro output rfl)
    apply Total.scalar_next (i := test) (event := Scalar.occurrence s test true) (next := s1) (by simp [program,pc])
    · simp [Scalar.eval,test,Instr.plain,Guard.eval,Operand32.eval,Compare.eval,s1,count,pc]
    apply Total.scalar_next (event := Scalar.occurrence s1 done true) (next := s2) (by rfl)
    · simp [Scalar.eval,done,Guard.eval,s2,s1,update]
    apply Total.scalar_next (event := Scalar.occurrence s2 store true (some ⟨.store,s.addrs 2,acc⟩)) (next := s3) (by rfl)
    · simp [Scalar.eval,store,Instr.plain,Guard.eval,Operand32.eval,Operand64.eval,
        s3,s2,s1,hi,accumulator]
    apply Total.scalar_halt (by rfl) (show Scalar.eval none exit s3 = .halted s3 (Scalar.occurrence s3 exit true) from rfl)
    exact ⟨acc,.nil,rfl⟩
  | cons x xs ih =>
    let s1 := {s with pc := 2,preds := update s.preds 0 false}
    let s2 := {s1 with pc := 3}
    let s3 := {s2 with pc := 4,regs := update s.regs 0 x.1}
    let s4 := {s3 with pc := 5,regs := update s3.regs 1 x.2}
    have nonzero : (BitVec.ofNat 32 (xs.length+1) : Word) ≠ 0 := by
      intro h
      have ht := congrArg BitVec.toNat h
      have hc : xs.length+1 < 4294967296 := bounds.count
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc] at ht
    have noCount : (s.regs 3 == 0#32) = false := by
      rw [count]; exact beq_eq_false_iff_ne.mpr nonzero
    have hl : addressIndex s.memory (s.addrs 0) = .ok left := by
      rw [lp]; apply pointer_index <;> have := bounds.leftExtent <;> have := bounds.leftPointer <;> simp only [List.length_cons] at * <;> omega
    have hr : addressIndex s.memory (s.addrs 1) = .ok right := by
      rw [rp]; apply pointer_index <;> have := bounds.rightExtent <;> have := bounds.rightPointer <;> simp only [List.length_cons] at * <;> omega
    have values := stored 0 x (by rfl)
    simp only [Nat.add_zero] at values
    have leftValue : s.memory[left]! = x.1 := by simp [List.getElem!_eq_getElem?_getD,values.1]
    have rightValue : s.memory[right]! = x.2 := by simp [List.getElem!_eq_getElem?_getD,values.2]
    change Total target program _ ((10*xs.length+4)+10) s
    apply Total.scalar_next (i := test) (event := Scalar.occurrence s test true) (next := s1) (by simp [program,pc])
    · simp [Scalar.eval,test,Instr.plain,Guard.eval,Operand32.eval,Compare.eval,s1,noCount,pc]
    apply Total.scalar_next (event := Scalar.occurrence s1 done false) (next := s2) (by rfl)
    · simp [Scalar.eval,done,Guard.eval,s2,s1,update]
    apply Total.scalar_next (event := Scalar.occurrence s2 (load 0) true (some ⟨.load,s.addrs 0,x.1⟩)) (next := s3) (by rfl)
    · simp [Scalar.eval,load,Instr.plain,Guard.eval,Operand64.eval,s3,s2,s1,hl,leftValue]
    apply Total.scalar_next (event := Scalar.occurrence s3 (load 1) true (some ⟨.load,s.addrs 1,x.2⟩)) (next := s4) (by rfl)
    · simp [Scalar.eval,load,Instr.plain,Guard.eval,Operand64.eval,s4,s3,s2,s1,hr,rightValue]
    apply Total.binary32 (by rfl) (by rfl)
    intro product hp
    let s5 := {s4 with pc := 6,regs := update s4.regs 2 product}
    change Total target program _ ((10*xs.length+4)+5) s5
    apply Total.binary32 (by rfl) (by rfl)
    intro next hn
    let s6 := {s5 with pc := 7,regs := update s5.regs 4 next}
    let s7 := {s6 with pc := 8,addrs := update s.addrs 0 (pointer (left+1))}
    let s8 := {s7 with pc := 9,addrs := update s7.addrs 1 (pointer (right+1))}
    let s9 := {s8 with pc := 10,regs := update s8.regs 3 (BitVec.ofNat 32 xs.length)}
    let s10 := {s9 with pc := 1}
    have pl : pointer left+4#64 = pointer (left+1) := by simp [pointer,Nat.mul_add,BitVec.ofNat_add]
    have pr : pointer right+4#64 = pointer (right+1) := by simp [pointer,Nat.mul_add,BitVec.ofNat_add]
    have ct : (BitVec.ofNat 32 (xs.length+1) : Word)-1#32 = BitVec.ofNat 32 xs.length := by
      simpa using BitVec.ofNat_sub_ofNat_of_le (w := 32) (xs.length+1) 1 (by decide) (by omega)
    change Total target program _ ((10*xs.length+4)+4) s6
    apply Total.scalar_next (event := Scalar.occurrence s6 (increment 0) true) (next := s7) (by rfl)
    · simp [Scalar.eval,increment,Instr.plain,Guard.eval,Operand64.eval,s7,s6,s5,s4,s3,s2,s1,lp,pl]
    apply Total.scalar_next (event := Scalar.occurrence s7 (increment 1) true) (next := s8) (by rfl)
    · simp [Scalar.eval,increment,Instr.plain,Guard.eval,Operand64.eval,s8,s7,s6,s5,s4,s3,s2,s1,rp,pr,update]
    apply Total.scalar_next (event := Scalar.occurrence s8 (decrement) true) (next := s9) (by rfl)
    · simp [Scalar.eval,decrement,Instr.plain,Guard.eval,Operand32.eval,BinOp.eval,
        s9,s8,s7,s6,s5,s4,s3,s2,s1,update,count,ct]
    apply Total.scalar_next (event := Scalar.occurrence s9 (back) true) (next := s10) (by rfl)
    · rfl
    have hp' : Ptx.Binary32.Results .mul x.1 x.2 product := by
      simpa [multiply,Operand32.eval,s4,s3,update] using hp
    have hn' : Ptx.Binary32.Results .add product acc next := by
      simpa [addition,Operand32.eval,s5,s4,s3,update,accumulator] using hn
    have tail := ih s10 (left+1) (right+1) next rfl
      (by simp [s10,s9,update]) (by simp [s10,s9,s8,s7,s6,update])
      (by simp [s10,s9,s8,s7,update]) (by simp [s10,s9,s8,update])
      (by simpa [s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,update] using output)
      (bounds_tail bounds) (stored_tail stored)
    apply tail.mono
    rintro final ⟨out,fold,memory⟩
    exact ⟨out,.cons ⟨hp',hn'⟩ fold,by simpa [s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,update] using memory⟩

/-- The kernel initIs positive zero itself before entering the loop. -/
theorem total (s : State) (left right output : Nat) (xs : List (Word × Word))
    (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64) :
    Total target program (Post xs 0 s.memory output) (10*xs.length+5)
      (initial s left right output xs.length) := by
  let entry := initial s left right output xs.length
  let first := {entry with pc := 1,regs := update entry.regs 4 0}
  apply Total.scalar_next (next := first) (by rfl)
  · rfl
  have valid : ValidAddress s.memory (pointer output) := by
    exact (addressIndex_ok_iff.mp (pointer_index _ _ outBound outPointer)).1
  have loop := total_loop (target := target) xs first left right 0 rfl
    (by simp [first,entry,initial,update]) (by simp [first,update])
    (by simp [first,entry,initial,update]) (by simp [first,entry,initial,update])
    (by simpa [first,entry,initial,update] using valid) bounds stored
  have hn : 4*output < 18446744073709551616 := outPointer
  simpa [first,entry,initial,update,pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn] using loop

theorem execution_exists (eligible : Eligible target)
    (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64) :
    ∃ final events, Run target program (initial s left right output xs.length) final .halted events ∧
      events.length = 10*xs.length+5 ∧ Post xs 0 s.memory output final :=
  (total s left right output xs bounds stored outBound outPointer).exists_run eligible

theorem correct (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64)
    (run : Run target program (initial s left right output xs.length) final status events) :
    status = .halted ∧ events.length = 10*xs.length+5 ∧ Post xs 0 s.memory output final :=
  (total s left right output xs bounds stored outBound outPointer).correct run

theorem prefix_termination (eligible : Eligible target)
    (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64)
    (path : Path (Advances target program) (initial s left right output xs.length) events middle) :
    events.length < 10*xs.length+5 ∧
      ∃ final rest, Run target program middle final .halted rest ∧
        rest.length = 10*xs.length+5-events.length ∧ Post xs 0 s.memory output final := by
  obtain ⟨bound,tail⟩ := (total s left right output xs bounds stored outBound outPointer).prefix path
  exact ⟨bound,tail.exists_run eligible⟩

theorem no_infinite_execution (bounds : Bounds s.memory left right xs)
    (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64) :
    ¬ ∃ (states : Nat → State) (events : Nat → Mixed.Event),
      states 0 = initial s left right output xs.length ∧
      ∀ k, Advances target program (states k) (events k) (states (k+1)) :=
  (total s left right output xs bounds stored outBound outPointer).no_infinite

theorem memory_safe
    (path : Path (Advances target program) (initial s left right output count) events middle)
    (member : event ∈ events) (access : event.memory = some effect) :
    ValidAddress s.memory effect.address := path.memory_safe member access

theorem other_memory (bounds : Bounds s.memory left right xs) (stored : Stored s.memory left right xs)
    (outBound : output < s.memory.length) (outPointer : 4*output < 2^64)
    (run : Run target program (initial s left right output xs.length) final status events)
    (other : index ≠ output) : final.memory[index]? = s.memory[index]? := by
  obtain ⟨_,_,value,_,memory⟩ := correct bounds stored outBound outPointer run
  rw [memory]
  exact List.getElem?_set_ne (Ne.symm other)

end Ptx.Scalar.Dot
