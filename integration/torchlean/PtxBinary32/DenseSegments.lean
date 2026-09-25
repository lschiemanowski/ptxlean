import PtxBinary32.DenseAddress
import PtxBinary32.ParallelSegment

namespace Ptx.Scalar.Parallel.Dense

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private theorem update_shadow (f : Nat → α) (i : Nat) (a b : α) :
    Scalar.update (Scalar.update f i a) i b = Scalar.update f i b := by
  funext j
  by_cases h : j=i <;> simp [Scalar.update,h]

def afterPointer (state : Parallel.State n) (thread : Fin n) (destination index : Nat) : Parallel.State n :=
  setLane state thread {state.lanes thread with scalar :=
    {(state.lanes thread).scalar with pc := (state.lanes thread).scalar.pc+3, addrs := Scalar.update (state.lanes thread).scalar.addrs destination (bytePointer index),memory := []}}

theorem pointer_execution (cfg : Config n) (state : Parallel.State n) (thread : Fin n)
    (destination source index : Nat)
    (operand : (state.lanes thread).scalar.regs source = BitVec.ofNat 32 index)
    (fits : index < 2^32) :
    SegmentRegular cfg thread (pointer destination source) state ∧
    (segmentReference cfg thread (pointer destination source) state).1 = afterPointer state thread destination index := by
  have arithmetic := pointer_arithmetic index fits
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits] at arithmetic
  simp [SegmentRegular,segmentReference,pointer,scalar,Reference.dispatch,scalarStep,
    Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
    Scalar.Operand64.eval,setLane,arena,operand,Scalar.update,Function.update,
    afterPointer,update_shadow,arithmetic,show index % 4294967296 = index from Nat.mod_eq_of_lt fits,
    Nat.add_assoc]

def afterSetup (s : Shape) (state : Parallel.State s.threads) (t : Fin s.threads) : Parallel.State s.threads :=
  let r := t.val / s.width
  let c := t.val % s.width
  let old := (state.lanes t).scalar
  let regs := Scalar.update (Scalar.update (Scalar.update (Scalar.update (Scalar.update old.regs
    1 (BitVec.ofNat 32 c)) 2 (BitVec.ofNat 32 r)) 3 (BitVec.ofNat 32 (r*s.columns+c+s.weightBase))) 4 0) 5 0
  setLane state t {state.lanes t with scalar := {old with pc := old.pc+8,regs := regs,preds := Scalar.update old.preds 0 (decide (c<s.columns)),memory := []}}

theorem setup_execution (s : Shape) (b : Bounds s) (state : Parallel.State s.threads) (t : Fin s.threads)
    (tid : (state.lanes t).scalar.regs 0 = BitVec.ofNat 32 t.val) :
    SegmentRegular (config s b) t ((products s).take 8) state ∧
    (segmentReference (config s b) t ((products s).take 8) state).1 = afterSetup s state t := by
  have coords := decoded_coordinates s b t
  have hc := congrArg (BitVec.ofNat 32) coords.1
  have hr := congrArg (BitVec.ofNat 32) coords.2
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at hc hr
  simp only [Scalar.BinOp.eval,BitVec.toNat_ofNat] at hc hr
  have df : s.depth < 4294967296 := by have := b.depth; omega
  have shift : (BitVec.ofNat 32 t.val >>> s.depth) = BitVec.ofNat 32 (t.val / s.width) := by
    simpa [Nat.mod_eq_of_lt df,b.depth] using hr
  have cf : t.val % s.width < 4294967296 := by
    have := (coordinates s t).2.1; have := width_fits s b; omega
  have nf : s.columns < 4294967296 := by
    have padded : s.columns ≤ s.width := s.padded; have := width_fits s b; omega
  simp [SegmentRegular,segmentReference,products,pointer,scalar,word,Reference.dispatch,scalarStep,
    Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,
    Scalar.Operand64.eval,setLane,arena,tid,Scalar.update,Function.update,
    afterSetup,update_shadow,hc,shift,Nat.mod_eq_of_lt df,b.depth,Scalar.BinOp.eval,Scalar.Compare.eval,
    ← BitVec.ofNat_mul,← BitVec.ofNat_add,Nat.mod_eq_of_lt cf,Nat.mod_eq_of_lt nf,
    Shape.weightBase,Nat.add_assoc]

def afterLoad (state : Parallel.State n) (t : Fin n) (space : Space) (destination index : Nat) : Parallel.State n :=
  let old := (state.lanes t).scalar
  let value := (arena state (some space))[index]!
  setLane state t {state.lanes t with scalar := {old with pc := old.pc+1,regs := if old.preds 0 then Scalar.update old.regs destination value else old.regs,memory := arena state (some space)}}

theorem guarded_load_execution (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (space : Space) (destination address index : Nat)
    (valid : (state.lanes t).scalar.preds 0 = true →
      Scalar.addressIndex (arena state (some space)) ((state.lanes t).scalar.addrs address) = .ok index) :
    SegmentRegular cfg t [guarded space (.load destination (.reg address))] state ∧
    (segmentReference cfg t [guarded space (.load destination (.reg address))] state).1 =
      afterLoad state t space destination index := by
  cases h : (state.lanes t).scalar.preds 0
  · cases space <;> simp [SegmentRegular,segmentReference,guarded,Reference.dispatch,scalarStep,
      Scalar.eval,Scalar.Guard.eval,Scalar.Operand64.eval,setLane,arena,h,afterLoad]
  · have address := valid h
    cases space <;> simp [SegmentRegular,segmentReference,guarded,Reference.dispatch,scalarStep,
      Scalar.eval,Scalar.Guard.eval,Scalar.Operand64.eval,setLane,arena,h,afterLoad] at address ⊢
    all_goals simp [address]

def afterStore (state : Parallel.State n) (t : Fin n) (space : Space) (source index : Nat) : Parallel.State n :=
  let old := (state.lanes t).scalar
  let memory := if old.preds 0 then (arena state (some space)).set index (old.regs source) else arena state (some space)
  let next := setLane state t {state.lanes t with scalar := {old with pc := old.pc+1,memory := memory}}
  match space with | .global => {next with global := memory} | .shared => {next with shared := memory}

theorem guarded_store_execution (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (space : Space) (source address index : Nat)
    (valid : (state.lanes t).scalar.preds 0 = true →
      Scalar.addressIndex (arena state (some space)) ((state.lanes t).scalar.addrs address) = .ok index) :
    SegmentRegular cfg t [guarded space (.store (.reg address) (.reg source))] state ∧
    (segmentReference cfg t [guarded space (.store (.reg address) (.reg source))] state).1 =
      afterStore state t space source index := by
  cases h : (state.lanes t).scalar.preds 0
  · cases space <;> simp [SegmentRegular,segmentReference,guarded,Reference.dispatch,scalarStep,
      Scalar.eval,Scalar.Guard.eval,Scalar.Operand64.eval,Scalar.Operand32.eval,setLane,arena,h,afterStore]
  · have address := valid h
    cases space <;> simp [SegmentRegular,segmentReference,guarded,Reference.dispatch,scalarStep,
      Scalar.eval,Scalar.Guard.eval,Scalar.Operand64.eval,Scalar.Operand32.eval,setLane,arena,h,afterStore] at address ⊢
    all_goals simp [address]

theorem binary32_regular (cfg : Config n) (state : Parallel.State n) (t : Fin n)
    (instruction : Scalar.Binary32.Instr) : SegmentRegular cfg t [.binary32 instruction] state := by
  cases h : instruction.guard.eval (state.lanes t).scalar <;>
    simp [SegmentRegular,Reference.dispatch,Reference.binary32,h,setLane]

end Ptx.Scalar.Parallel.Dense
