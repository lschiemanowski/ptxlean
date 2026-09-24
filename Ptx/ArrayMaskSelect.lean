import Ptx.MaskSelect
import Ptx.PureKernelRules

/-! A bounded, in-place array loop over the reviewed instruction catalog. -/
namespace Ptx.Scalar.ArrayMaskSelect

open PureKernel

def transform (mask fallback : Word) (xs : List Word) : List Word :=
  xs.map (fun x => MaskSelect.answer x fallback mask)

def pointer (index : Nat) : Address := BitVec.ofNat 64 (4 * index)

def testI : Scalar.Instr := .plain (.setp .eq 1 (.reg 3) (.imm 0))
def doneI : Scalar.Instr := ⟨.pred 1 true, .bra 10⟩
def loadI : Scalar.Instr := .plain (.load 0 (.reg 0))
def selectI (fallback : Word) : Select32.Instr := ⟨.always, 0, .imm fallback, .reg 0, 0⟩
def storeI : Scalar.Instr := .plain (.store (.reg 0) (.reg 0))
def incrementI : Scalar.Instr := .plain (.add64 0 (.reg 0) (.imm 4))
def decrementI : Scalar.Instr := .plain (.bin32 .sub 3 (.reg 3) (.imm 1))
def backI : Scalar.Instr := .plain (.bra 0)

def program (mask fallback : Word) : List ReviewedPure.Instr :=
  [.scalar testI, .scalar doneI, .scalar loadI,
   ReviewedPure.bitwise (MaskSelect.maskI mask), .scalar MaskSelect.compareI,
   ReviewedPure.select (selectI fallback), .scalar storeI, .scalar incrementI,
   .scalar decrementI, .scalar backI, .scalar MaskSelect.exitI]

/-- Host-side initial-state contract, not a modeled PTX launch ABI. -/
def initial (s : State) (front xs tail : List Word) : State :=
  {s with
    pc := 0
    memory := front ++ xs ++ tail
    addrs := update s.addrs 0 (pointer front.length),
    regs := update s.regs 3 (BitVec.ofNat 32 xs.length)}

/-- The final one-past address is also representable, even for an empty array. -/
def Bounds (front xs : List Word) : Prop :=
  xs.length < 2^32 ∧ 4 * (front.length + xs.length) < 2^64

private theorem pointer_index (memory : List Word) (index : Nat)
    (bound : index < memory.length) (noWrap : 4 * index < 2^64) :
    addressIndex memory (pointer index) = .ok index := by
  simp [addressIndex, pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap, bound]

private theorem scalar_dispatch (eligible : Eligible target)
    (fetch : p[s.pc]? = some (.scalar i : ReviewedPure.Instr))
    (evaluated : Scalar.eval none i s = .next next event) :
    Dispatch target p s (.next next (.scalar event)) := by
  apply (dispatch_fetch eligible fetch (by trivial)).mpr
  exact eval_scalar_iff.mpr (by simp [evaluated, liftScalar])

private theorem nonzero_count (xs : List Word) (bound : xs.length + 1 < 2^32) :
    ((BitVec.ofNat 32 (xs.length + 1) : Word) == 0) = false := by
  have hn : (BitVec.ofNat 32 (xs.length + 1) : Word) ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at this
  exact beq_eq_false_iff_ne.mpr hn

/-- Ten actual instruction transitions transform the next word and restore the loop invariant. -/
theorem iteration (s : State) (front xs tail : List Word) (x mask fallback : Word)
    (eligible : Eligible target) (bounds : Bounds front (x :: xs)) :
    ∃ next events,
      Path (Advances target (program mask fallback)) (initial s front (x :: xs) tail)
        events (initial next (front ++ [MaskSelect.answer x fallback mask]) xs tail) ∧
      events.length = 10 := by
  let s0 := initial s front (x :: xs) tail
  let s1 := {s0 with pc := 1, preds := update s0.preds 1 false}
  let s2 := {s1 with pc := 2}
  let s3 := {s2 with pc := 3, regs := update s2.regs 0 x}
  let s4 := Pure32.write s3 0 (x &&& mask)
  let s5 := {s4 with pc := 5, preds := update s4.preds 0 ((x &&& mask) == 0)}
  let s6 := Pure32.write s5 0 (MaskSelect.answer x fallback mask)
  let s7 := {s6 with pc := 7, memory := front ++ MaskSelect.answer x fallback mask :: xs ++ tail}
  let s8 := {s7 with pc := 8, addrs := update s7.addrs 0 (pointer (front.length + 1))}
  let s9 := {s8 with pc := 9, regs := update s8.regs 3 (BitVec.ofNat 32 xs.length)}
  let s10 := {s9 with pc := 0}
  have hn := nonzero_count xs (by have := bounds.1; simpa using this)
  have hi : addressIndex (front ++ (x :: xs) ++ tail) (pointer front.length) = .ok front.length :=
    pointer_index _ _ (by simp) (by have := bounds.2; simp at this; omega)
  have write : (front ++ (x :: xs) ++ tail).set front.length (MaskSelect.answer x fallback mask) =
      front ++ MaskSelect.answer x fallback mask :: xs ++ tail := by
    simp [List.append_assoc, List.set_append_right]
  simp only [List.append_assoc, List.cons_append] at hi write
  change (BitVec.ofNat 32 (xs.length + 1) == 0#32) = false at hn
  have ptr : pointer front.length + 4#64 = pointer (front.length + 1) := by
    simp [pointer, Nat.mul_add, BitVec.ofNat_add]
  have count : (BitVec.ofNat 32 (xs.length + 1) : Word) - 1#32 = BitVec.ofNat 32 xs.length := by
    simpa using (BitVec.ofNat_sub_ofNat_of_le (w := 32) (xs.length + 1) 1 (by decide) (by omega))
  have boundary : s10 = initial s10 (front ++ [MaskSelect.answer x fallback mask]) xs tail := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, initial,
      Pure32.write, List.append_assoc]
    constructor <;> funext index <;> simp +contextual [update]
  refine ⟨s10,
    [.scalar (Scalar.occurrence s0 testI true),
     .scalar (Scalar.occurrence s1 doneI false),
     .scalar (Scalar.occurrence s2 loadI true (some ⟨.load, pointer front.length, x⟩)),
     .pure .bitwise (Bitwise32.occurrence s3 (MaskSelect.maskI mask) true),
     .scalar (Scalar.occurrence s4 MaskSelect.compareI true),
     .pure .select (Select32.occurrence s5 (selectI fallback) true),
     .scalar (Scalar.occurrence s6 storeI true (some ⟨.store, pointer front.length, MaskSelect.answer x fallback mask⟩)),
     .scalar (Scalar.occurrence s7 incrementI true),
     .scalar (Scalar.occurrence s8 decrementI true),
     .scalar (Scalar.occurrence s9 backI true)], ?_, rfl⟩
  rw [← boundary]
  apply Mixed.Path.cons (next := s1)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, testI, Scalar.Instr.plain, Guard.eval, Operand32.eval, Compare.eval,
      s1, s0, initial, update, hn]
  apply Mixed.Path.cons (next := s2)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, doneI, Guard.eval, s2, s1, update]
  apply Mixed.Path.cons (next := s3)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, loadI, Scalar.Instr.plain, Guard.eval, Operand64.eval,
      s3, s2, s1, s0, initial, update, hi]
  apply Mixed.Path.cons (next := s4)
  · apply (dispatch_pure_iff eligible (by rfl)).mpr
    constructor
    · exact ⟨eligible.1, by have := eligible.2; omega⟩
    · apply (Bitwise32.eval_true_iff (MaskSelect.maskI mask) _ _ _ (by rfl)).mpr
      exact ⟨by simp [s4, Bitwise32.result, Bitwise32.compute, MaskSelect.maskI,
        Operand32.eval, s3, update], rfl⟩
  apply Mixed.Path.cons (next := s5)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, MaskSelect.compareI, Scalar.Instr.plain, Guard.eval, Operand32.eval,
      Compare.eval, s5, s4, s3, Pure32.write, update]
  apply Mixed.Path.cons (next := s6)
  · apply (dispatch_pure_iff eligible (by rfl)).mpr
    constructor
    · exact ⟨eligible.1, by have := eligible.2; omega⟩
    · apply (Select32.eval_true_iff (selectI fallback) _ _ _ (by rfl)).mpr
      exact ⟨by simp [s6, Select32.result, Select32.compute, selectI, Operand32.eval,
        s5, s4, Pure32.write, update, MaskSelect.answer], rfl⟩
  apply Mixed.Path.cons (next := s7)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, storeI, Scalar.Instr.plain, Guard.eval, Operand64.eval, Operand32.eval,
      s7, s6, s5, s4, s3, s2, s1, s0, initial, Pure32.write, update, hi, write]
  apply Mixed.Path.cons (next := s8)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, incrementI, Scalar.Instr.plain, Guard.eval, Operand64.eval,
      s8, s7, s6, s5, s4, s3, s2, s1, s0, initial, Pure32.write, update, ptr]
  apply Mixed.Path.cons (next := s9)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, decrementI, Scalar.Instr.plain, Guard.eval, Operand32.eval, BinOp.eval,
      s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, initial, Pure32.write, update, count]
  apply Mixed.Path.cons (next := s10)
  · apply scalar_dispatch eligible (by rfl)
    rfl
  exact .nil

/-- With zero remaining words, test, branch to exit and halt without touching memory. -/
theorem empty_execution (s : State) (front tail : List Word) (mask fallback : Word)
    (eligible : Eligible target) :
    ∃ final events, Run target (program mask fallback) (initial s front [] tail)
      final .halted events ∧ final.memory = front ++ tail ∧ events.length = 3 := by
  let s0 := initial s front [] tail
  let s1 := {s0 with pc := 1, preds := update s0.preds 1 true}
  let s2 := {s1 with pc := 10}
  refine ⟨s2, [.scalar (Scalar.occurrence s0 testI true),
    .scalar (Scalar.occurrence s1 doneI true),
    .scalar (Scalar.occurrence s2 MaskSelect.exitI true)], ?_, by simp [s2, s1, s0, initial], rfl⟩
  apply Run.next (next := s1)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, testI, Scalar.Instr.plain, Guard.eval, Operand32.eval, Compare.eval,
      s1, s0, initial, update]
  apply Run.next (next := s2)
  · apply scalar_dispatch eligible (by rfl)
    simp [Scalar.eval, doneI, Guard.eval, s2, s1, update]
  apply Run.halted
  apply (dispatch_fetch eligible (by rfl) (by trivial)).mpr
  exact eval_scalar_iff.mpr rfl

/-- List induction constructs the run; correctness of its output is not an assumption. -/
theorem execution (s : State) (front xs tail : List Word) (mask fallback : Word)
    (eligible : Eligible target) (bounds : Bounds front xs) :
    ∃ final events, Run target (program mask fallback) (initial s front xs tail)
      final .halted events ∧ final.memory = front ++ transform mask fallback xs ++ tail ∧
      events.length = 10 * xs.length + 3 := by
  induction xs generalizing s front with
  | nil => simpa [transform] using empty_execution s front tail mask fallback eligible
  | cons x xs ih =>
    obtain ⟨next, events, path, len⟩ := iteration s front xs tail x mask fallback eligible bounds
    have nextBounds : Bounds (front ++ [MaskSelect.answer x fallback mask]) xs := by
      rcases bounds with ⟨count, address⟩
      simp only [Bounds, List.length_append, List.length_singleton]
      simp only [List.length_cons] at count address
      constructor <;> omega
    obtain ⟨final, rest, run, memory, length⟩ := ih next _ nextBounds
    refine ⟨final, events ++ rest, run.prepend path, ?_, ?_⟩
    · simpa [transform, List.append_assoc] using memory
    · simp [len, length]; omega

/-- All completed executions, including alleged failures, have the exact specified result. -/
theorem correct (eligible : Eligible target) (bounds : Bounds front xs)
    (run : Run target (program mask fallback) (initial s front xs tail) final status events) :
    status = .halted ∧ final.memory = front ++ transform mask fallback xs ++ tail ∧
      events.length = 10 * xs.length + 3 := by
  obtain ⟨witness, trace, hw, hm, hl⟩ := execution s front xs tail mask fallback eligible bounds
  obtain ⟨rfl, rfl, rfl⟩ := Run.deterministic ReviewedPure.functional run hw
  exact ⟨rfl, hm, hl⟩

/-- Every advancing prefix is short and can finish successfully; no fairness premise is used. -/
theorem prefix_termination (eligible : Eligible target) (bounds : Bounds front xs)
    (path : Path (Advances target (program mask fallback)) (initial s front xs tail) events middle) :
    events.length ≤ 10 * xs.length + 2 ∧
      ∃ final rest, Run target (program mask fallback) middle final .halted rest ∧
        final.memory = front ++ transform mask fallback xs ++ tail := by
  obtain ⟨final, trace, run, hm, hl⟩ := execution s front xs tail mask fallback eligible bounds
  obtain ⟨rest, hr, _, bound⟩ := run.complete_prefix ReviewedPure.functional path
  exact ⟨by omega, final, rest, hr, hm⟩

theorem no_infinite_execution (eligible : Eligible target) (bounds : Bounds front xs) :
    ¬ ∃ (states : Nat → State) (events : Nat → ReviewedPure.Event),
      states 0 = initial s front xs tail ∧
      ∀ n, Advances target (program mask fallback) (states n) (events n) (states (n+1)) := by
  obtain ⟨_, _, run, _, _⟩ := execution s front xs tail mask fallback eligible bounds
  exact run.no_infinite_advances ReviewedPure.functional

/-- Access validity holds for finite prefixes too, without presupposing completion. -/
theorem memory_safe
    (path : Path (Advances target (program mask fallback)) (initial s front xs tail) events middle)
    (member : event ∈ events) (memory : event.memory = some effect) :
    ValidAddress (front ++ xs ++ tail) effect.address :=
  path_memory_safe path member memory

theorem completed_memory_safe
    (run : Run target (program mask fallback) (initial s front xs tail) final status events)
    (member : event ∈ events) (memory : event.memory = some effect) :
    ValidAddress (front ++ xs ++ tail) effect.address :=
  Run.memory_safe run member memory

/-- Includes both surrounding allocated words and indices beyond the arena. -/
theorem other_memory (eligible : Eligible target) (bounds : Bounds front xs)
    (run : Run target (program mask fallback) (initial s front xs tail) final status events)
    (outside : index < front.length ∨ front.length + xs.length ≤ index) :
    final.memory[index]? = (initial s front xs tail).memory[index]? := by
  rw [(correct eligible bounds run).2.1]
  change (front ++ transform mask fallback xs ++ tail)[index]? = (front ++ xs ++ tail)[index]?
  rcases outside with before | after
  · simp only [List.append_assoc, List.getElem?_append_left before]
  · rw [List.getElem?_append_right (by simpa [transform] using after),
      List.getElem?_append_right (by simpa using after)]
    simp [transform]

end Ptx.Scalar.ArrayMaskSelect
