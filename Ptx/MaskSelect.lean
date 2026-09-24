import Ptx.ReviewedPure

/-! Load two words, mask the first, select a fallback, store, and exit. -/
namespace Ptx.Scalar.MaskSelect

open PureKernel

def answer (x y mask : Word) : Word := if (x &&& mask) == 0 then y else x &&& mask

def loadX : Scalar.Instr := .plain (.load 0 (.imm 0))
def loadY : Scalar.Instr := .plain (.load 1 (.imm 4))
def maskI (mask : Word) : Bitwise32.Instr := ⟨.always, .bitAnd, 0, .reg 0, .imm mask⟩
def compareI : Scalar.Instr := .plain (.setp .eq 0 (.reg 0) (.imm 0))
def selectI : Select32.Instr := ⟨.always, 2, .reg 1, .reg 0, 0⟩
def storeI : Scalar.Instr := .plain (.store (.imm 8) (.reg 2))
def exitI : Scalar.Instr := .plain .exit

def program (mask : Word) : List ReviewedPure.Instr :=
  [.scalar loadX, .scalar loadY, ReviewedPure.bitwise (maskI mask), .scalar compareI,
   ReviewedPure.select selectI, .scalar storeI, .scalar exitI]

/-- The caller supplies all other register banks; only PC and the input layout are fixed. -/
def initial (s : State) (x y old : Word) (tail : List Word) : State :=
  {s with pc := 0, memory := x :: y :: old :: tail}
def s1 (s : State) (x y old : Word) (tail : List Word) : State :=
  {initial s x y old tail with pc := 1, regs := update s.regs 0 x}
def s2 (s : State) (x y old : Word) (tail : List Word) : State :=
  {s1 s x y old tail with pc := 2, regs := update (s1 s x y old tail).regs 1 y}
def s3 (s : State) (x y old mask : Word) (tail : List Word) : State :=
  Pure32.write (s2 s x y old tail) 0 (x &&& mask)
def s4 (s : State) (x y old mask : Word) (tail : List Word) : State :=
  {s3 s x y old mask tail with pc := 4, preds := update s.preds 0 ((x &&& mask) == 0)}
def s5 (s : State) (x y old mask : Word) (tail : List Word) : State :=
  Pure32.write (s4 s x y old mask tail) 2 (answer x y mask)
def finalState (s : State) (x y old mask : Word) (tail : List Word) : State :=
  {s5 s x y old mask tail with pc := 6, memory := x :: y :: answer x y mask :: tail}

def trace (s : State) (x y old mask : Word) (tail : List Word) : List ReviewedPure.Event :=
  [.scalar (Scalar.occurrence (initial s x y old tail) loadX true (some ⟨.load,0,x⟩)),
   .scalar (Scalar.occurrence (s1 s x y old tail) loadY true (some ⟨.load,4,y⟩)),
   .pure .bitwise (Bitwise32.occurrence (s2 s x y old tail) (maskI mask) true),
   .scalar (Scalar.occurrence (s3 s x y old mask tail) compareI true),
   .pure .select (Select32.occurrence (s4 s x y old mask tail) selectI true),
   .scalar (Scalar.occurrence (s5 s x y old mask tail) storeI true (some ⟨.store,8,answer x y mask⟩)),
   .scalar (Scalar.occurrence (finalState s x y old mask tail) exitI true)]

private theorem scalar_dispatch (eligible : Eligible target)
    (fetch : p[s.pc]? = some (.scalar i : ReviewedPure.Instr))
    (evaluated : Scalar.eval none i s = .next next event) :
    Dispatch target p s (.next next (.scalar event)) := by
  apply (dispatch_fetch eligible fetch (by trivial)).mpr
  exact eval_scalar_iff.mpr (by simp [evaluated, liftScalar])

/-- An explicit finite execution, independent of the correctness theorem. -/
theorem execution (s : State) (x y old mask : Word) (tail : List Word)
    (eligible : Eligible target) :
    Run target (program mask) (initial s x y old tail)
      (finalState s x y old mask tail) .halted (trace s x y old mask tail) := by
  apply Run.next (next := s1 s x y old tail)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, loadX, Scalar.Instr.plain, Guard.eval, Operand64.eval,
      addressIndex, initial, s1, Scalar.occurrence]
  apply Run.next (next := s2 s x y old tail)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, loadY, Scalar.Instr.plain, Guard.eval, Operand64.eval,
      addressIndex, initial, s1, s2, Scalar.occurrence]
  apply Run.next (next := s3 s x y old mask tail)
  · apply (dispatch_pure_iff eligible (by rfl)).mpr
    constructor
    · exact ⟨eligible.1, by have := eligible.2; omega⟩
    · apply (Bitwise32.eval_true_iff (maskI mask) _ _ _ (by rfl)).mpr
      exact ⟨by simp [s3, Bitwise32.result, Bitwise32.compute, maskI, Operand32.eval, s2, s1, update], rfl⟩
  apply Run.next (next := s4 s x y old mask tail)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, compareI, Scalar.Instr.plain, Guard.eval, Operand32.eval,
      Compare.eval, s4, s3, s2, s1, initial, Pure32.write, update]
  apply Run.next (next := s5 s x y old mask tail)
  · apply (dispatch_pure_iff eligible (by rfl)).mpr
    constructor
    · exact ⟨eligible.1, by have := eligible.2; omega⟩
    · apply (Select32.eval_true_iff selectI _ _ _ (by rfl)).mpr
      exact ⟨by simp [s5, Select32.result, Select32.compute, selectI, Operand32.eval,
        s4, s3, s2, s1, initial, Pure32.write, update, answer], rfl⟩
  apply Run.next (next := finalState s x y old mask tail)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, storeI, Scalar.Instr.plain, Guard.eval, Operand64.eval, Operand32.eval,
      addressIndex, finalState, s5, s4, s3, s2, s1, initial, Pure32.write, update]
  apply Run.halted
  apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
  exact eval_scalar_iff.mpr rfl

theorem execution_exists (s : State) (x y old mask : Word) (tail : List Word)
    (eligible : Eligible target) :
    ∃ final events, Run target (program mask) (initial s x y old tail) final .halted events :=
  ⟨_,_,execution s x y old mask tail eligible⟩

/-- Every completed run, including a purported failure, agrees with the witness. -/
theorem correct (eligible : Eligible target)
    (run : Run target (program mask) (initial s x y old tail) final status events) :
    status = .halted ∧ final.memory = x :: y :: answer x y mask :: tail ∧
      events = trace s x y old mask tail := by
  obtain ⟨rfl,rfl,rfl⟩ := Run.deterministic ReviewedPure.functional run
    (execution s x y old mask tail eligible)
  exact ⟨rfl,rfl,rfl⟩

theorem memory_safe
    (run : Run target (program mask) (initial s x y old tail) final status events)
    (member : event ∈ events) (effect : event.memory = some memory) :
    ValidAddress (x :: y :: old :: tail) memory.address :=
  Run.memory_safe run member effect

theorem output_correct (eligible : Eligible target)
    (run : Run target (program mask) (initial s x y old tail) final status events) :
    final.memory[2]? = some (answer x y mask) := by
  rw [(correct eligible run).2.1]
  rfl

theorem other_memory (eligible : Eligible target)
    (run : Run target (program mask) (initial s x y old tail) final status events)
    (different : index ≠ 2) :
    final.memory[index]? = (initial s x y old tail).memory[index]? := by
  rw [(correct eligible run).2.1]
  cases index with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => contradiction
      | succ n => rfl

example : answer 0x1234 99 0xff = 0x34 := by decide
example : answer 0x100 99 0xff = 99 := by decide

end Ptx.Scalar.MaskSelect
