import Ptx.ReviewedPure

/-! Register 0 is rotated in place using the runtime count in register 1, then exit. -/
namespace Ptx.Scalar.FunnelRotation
open PureKernel

def answer (left : Bool) (x count : Word) : Word :=
  if left then x.rotateLeft count.toNat else x.rotateRight count.toNat

theorem compute_rotation (left : Bool) (x count : Word) :
    Shf32.compute (if left then .leftWrap else .rightWrap) x x count = answer left x count := by
  cases left <;> simp [answer, Shf32.compute_leftWrap, Shf32.compute_rightWrap,
    BitVec.rotateLeft_def, BitVec.rotateRight_def, BitVec.or_comm]

def rotateI (left : Bool) : Shf32.Instr :=
  ⟨.always, if left then .leftWrap else .rightWrap, 0, .reg 0, .reg 0, .reg 1⟩
def exitI : Scalar.Instr := .plain .exit

def program (left : Bool) : List ReviewedPure.Instr :=
  [ReviewedPure.shf (rotateI left), .scalar exitI]

def initial (s : State) : State := {s with pc := 0}

/-- An executable specialization of this two-instruction program, using the leaf computation. -/
def execute (left : Bool) (s : State) : State :=
  Pure32.write (initial s) 0 (Shf32.result (rotateI left) (initial s))

def trace (left : Bool) (s : State) : List ReviewedPure.Event :=
  [.pure .shf (Shf32.occurrence (initial s) (rotateI left) true),
   .scalar (Scalar.occurrence (execute left s) exitI true)]

theorem execute_value (left : Bool) (s : State) :
    (execute left s).regs 0 = answer left (s.regs 0) (s.regs 1) := by
  simp [execute, Pure32.write, update, Shf32.result, rotateI, Operand32.eval,
    initial, compute_rotation]

/-- Includes a real exit, not merely a finite prefix or fuel exhaustion. -/
theorem execution (left : Bool) (s : State) (eligible : Eligible target) :
    Run target (program left) (initial s) (execute left s) .halted (trace left s) := by
  apply Run.next (next := execute left s)
  · apply (dispatch_pure_iff eligible (by rfl)).mpr
    constructor
    · exact ⟨eligible.1, by have := eligible.2; omega⟩
    · exact (Shf32.eval_true_iff (rotateI left) _ _ _ (by rfl)).mpr ⟨rfl, rfl⟩
  · apply Run.halted
    apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
    exact eval_scalar_iff.mpr rfl

theorem execution_exists (left : Bool) (s : State) (eligible : Eligible target) :
    ∃ final events, Run target (program left) (initial s) final .halted events :=
  ⟨_, _, execution left s eligible⟩

/-- Covers every completed run, including purported fault or unsupported outcomes. -/
theorem correct (eligible : Eligible target)
    (run : Run target (program left) (initial s) final status events) :
    status = .halted ∧ final.regs 0 = answer left (s.regs 0) (s.regs 1) ∧
      final = execute left s ∧ events = trace left s := by
  obtain ⟨rfl, rfl, rfl⟩ := Run.deterministic ReviewedPure.functional run (execution left s eligible)
  exact ⟨rfl, execute_value left s, rfl, rfl⟩

theorem frame (eligible : Eligible target)
    (run : Run target (program left) (initial s) final status events) :
    final.memory = s.memory ∧ final.addrs = s.addrs ∧ final.preds = s.preds ∧
      final.pc = 1 ∧ ∀ r, r ≠ 0 → final.regs r = s.regs r := by
  rw [(correct eligible run).2.2.1]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro r different
  simp [execute, Pure32.write, initial, update, different]

theorem no_memory_access (eligible : Eligible target)
    (run : Run target (program left) (initial s) final status events)
    (member : event ∈ events) : event.memory = none := by
  rw [(correct eligible run).2.2.2] at member
  simp [trace] at member
  rcases member with rfl | rfl <;> rfl

/-- Repeating the input is an actual double register read before the in-place write. -/
theorem repeated_reads (left : Bool) (s : State) :
    (Shf32.occurrence (initial s) (rotateI left) true).reads = [.word 0, .word 0, .word 1] := by
  rfl
end Ptx.Scalar.FunnelRotation
