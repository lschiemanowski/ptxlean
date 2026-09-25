import PtxBinary32.ParallelBarrier
import PtxBinary32.ParallelReference

/-! Composable straight-line segments built from actual mixed dispatches.
The program-counter, live-thread and unchanged-barrier obligations are checked
at every instruction. Compiling a segment into a fetched run requires its exact
slice in the common program and an initially runnable thread. -/
namespace Ptx.Scalar.Parallel

inductive Segment (cfg : Config n) (thread : Fin n) :
    List Instr → State n → List (Event n) → State n → Prop where
  | nil : Segment cfg thread [] s [] s
  | cons : Dispatch cfg candidate thread i s out →
      (out.state.lanes thread).scalar.pc = (s.lanes thread).scalar.pc+1 →
      (out.state.lanes thread).halted = (s.lanes thread).halted →
      out.state.barrier = s.barrier →
      Segment cfg thread rest out.state events final →
      Segment cfg thread (i::rest) s (out.events++events) final

def Fetches (program : List Instr) (pc : Nat) (code : List Instr) : Prop :=
  ∀ k, k < code.length → program[pc+k]? = code[k]?

theorem fetches_head (fetch : Fetches program pc (i::code)) : program[pc]? = some i := by
  simpa using fetch 0 (by simp)

theorem fetches_tail (fetch : Fetches program pc (i::code)) : Fetches program (pc+1) code := by
  intro k hk
  have h := fetch (k+1) (by simpa using Nat.succ_lt_succ hk)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem Segment.frame (segment : Segment cfg thread code s events final) :
    (final.lanes thread).scalar.pc = (s.lanes thread).scalar.pc+code.length ∧
    (final.lanes thread).halted = (s.lanes thread).halted ∧ final.barrier=s.barrier := by
  induction segment with
  | nil => exact ⟨by simp,rfl,rfl⟩
  | cons _ pc live barrier _ ih =>
    refine ⟨?_,ih.2.1.trans live,ih.2.2.trans barrier⟩
    simp only [List.length_cons]
    omega

theorem Segment.compile (segment : Segment cfg thread code s events final)
    (fetch : Fetches program (s.lanes thread).scalar.pc code)
    (live : (s.lanes thread).halted = false) (fresh : s.barrier.arrived thread = false)
    (eligible : Mixed.Eligible cfg.target) : Runs cfg program s events final := by
  induction segment with
  | nil => exact .nil
  | @cons candidate i current out restCode restEvents last dispatch pc halted barrier rest ih =>
    have step : Step cfg program candidate thread current out := by
      refine ⟨eligible,?_⟩
      simp only [live,fresh,Bool.false_eq_true,↓reduceIte,fetches_head fetch]
      exact dispatch
    apply Runs.cons step
    apply ih
    · rw [pc]; exact fetches_tail fetch
    · exact halted.trans live
    · simpa [barrier] using fresh

theorem Segment.append (first : Segment cfg thread a s left middle)
    (second : Segment cfg thread b middle right final) :
    Segment cfg thread (a++b) s (left++right) final := by
  induction first with
  | nil => exact second
  | cons dispatch pc live barrier _ ih =>
    simpa [List.append_assoc] using Segment.cons dispatch pc live barrier (ih second)

/-- The deterministic witness evaluator retains instruction events. -/
def segmentReference (cfg : Config n) (thread : Fin n) : List Instr → State n → State n × List (Event n)
  | [],s => (s,[])
  | i::rest,s =>
    let out := Reference.dispatch cfg thread i s
    let tail := segmentReference cfg thread rest out.state
    (tail.1,out.events++tail.2)

/-- This check contains no desired memory value or output predicate. Each
concrete segment must prove it, including the absence of faults or branches. -/
def SegmentRegular (cfg : Config n) (thread : Fin n) : List Instr → State n → Prop
  | [],_ => True
  | i::rest,s =>
    let out := Reference.dispatch cfg thread i s
    out.status = .advanced ∧
    (out.state.lanes thread).scalar.pc = (s.lanes thread).scalar.pc+1 ∧
    (out.state.lanes thread).halted = (s.lanes thread).halted ∧
    out.state.barrier = s.barrier ∧ SegmentRegular cfg thread rest out.state

theorem segmentReference_sound (regular : SegmentRegular cfg thread code s) :
    Segment cfg thread code s (segmentReference cfg thread code s).2 (segmentReference cfg thread code s).1 := by
  induction code generalizing s with
  | nil => exact .nil
  | cons i rest ih =>
    exact .cons (Reference.dispatch_sound cfg thread i s) regular.2.1 regular.2.2.1 regular.2.2.2.1
      (ih regular.2.2.2.2)

theorem segmentReference_append (cfg : Config n) (thread : Fin n) (a b : List Instr) (s : State n) :
    segmentReference cfg thread (a++b) s =
      let first := segmentReference cfg thread a s
      let second := segmentReference cfg thread b first.1
      (second.1,first.2++second.2) := by
  induction a generalizing s with
  | nil => simp [segmentReference]
  | cons i a ih => simp [segmentReference,ih,List.append_assoc]

theorem segmentRegular_append (cfg : Config n) (thread : Fin n) (a b : List Instr) (s : State n) :
    SegmentRegular cfg thread (a++b) s ↔
      SegmentRegular cfg thread a s ∧ SegmentRegular cfg thread b (segmentReference cfg thread a s).1 := by
  induction a generalizing s with
  | nil => simp [SegmentRegular,segmentReference]
  | cons i a ih => simp [SegmentRegular,segmentReference,ih,and_assoc]

theorem fetches_slice (before code after : List Instr) :
    Fetches (before++code++after) before.length code := by
  intro k hk
  simp [List.getElem?_append,hk]

/-- Segment evidence that retains concrete-array loads. -/
inductive ConcreteSegment (cfg : Config n) (thread : Fin n) :
    List Instr → State n → List (Event n) → State n → Prop where
  | nil : ConcreteSegment cfg thread [] s [] s
  | cons : Dispatch cfg none thread i s out →
      (out.state.lanes thread).scalar.pc = (s.lanes thread).scalar.pc+1 →
      (out.state.lanes thread).halted = (s.lanes thread).halted →
      out.state.barrier = s.barrier →
      ConcreteSegment cfg thread rest out.state events final →
      ConcreteSegment cfg thread (i::rest) s (out.events++events) final

theorem ConcreteSegment.toSegment (segment : ConcreteSegment cfg thread code s events final) :
    Segment cfg thread code s events final := by
  induction segment with
  | nil => exact .nil
  | cons dispatch pc live barrier _ ih => exact .cons dispatch pc live barrier ih

theorem ConcreteSegment.frame (segment : ConcreteSegment cfg thread code s events final) :
    (final.lanes thread).scalar.pc = (s.lanes thread).scalar.pc+code.length ∧
    (final.lanes thread).halted = (s.lanes thread).halted ∧ final.barrier=s.barrier := segment.toSegment.frame

theorem ConcreteSegment.append (first : ConcreteSegment cfg thread a s left middle)
    (second : ConcreteSegment cfg thread b middle right final) :
    ConcreteSegment cfg thread (a++b) s (left++right) final := by
  induction first with
  | nil => exact second
  | cons dispatch pc live barrier _ ih =>
    simpa [List.append_assoc] using ConcreteSegment.cons dispatch pc live barrier (ih second)

theorem ConcreteSegment.compile (segment : ConcreteSegment cfg thread code s events final)
    (fetch : Fetches program (s.lanes thread).scalar.pc code)
    (live : (s.lanes thread).halted = false) (fresh : s.barrier.arrived thread = false)
    (eligible : Mixed.Eligible cfg.target) : ConcreteRuns cfg program s events final := by
  induction segment with
  | nil => exact .nil
  | @cons i current out restCode restEvents last dispatch pc halted barrier rest ih =>
    have step : Step cfg program none thread current out := by
      refine ⟨eligible,?_⟩
      simp only [live,fresh,Bool.false_eq_true,ite_false,fetches_head fetch]
      exact dispatch
    apply ConcreteRuns.cons step
    apply ih
    · rw [pc]; exact fetches_tail fetch
    · exact halted.trans live
    · simpa [barrier] using fresh

theorem segmentReference_concrete (regular : SegmentRegular cfg thread code s) :
    ConcreteSegment cfg thread code s (segmentReference cfg thread code s).2 (segmentReference cfg thread code s).1 := by
  induction code generalizing s with
  | nil => exact .nil
  | cons i rest ih =>
    exact .cons (Reference.dispatch_sound cfg thread i s) regular.2.1 regular.2.2.1 regular.2.2.2.1
      (ih regular.2.2.2.2)

end Ptx.Scalar.Parallel
