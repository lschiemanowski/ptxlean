import Ptx.ScalarEnvironment
import Ptx.ScalarMemoryWitness

/-! Vector addition with one shared word allocation and instruction-level
interleavings. `advance` has a checked correspondence to the scalar interpreter;
its cursor 5 means the exit at PC 4 has executed. This scheduler is a constructive
execution discipline, not a replacement for PTX weak memory. -/
namespace Ptx.Scalar.SharedVector

structure State (n : Nat) where
  memory : List Word
  cursor : Fin n → Nat
  regs : Fin n → Nat → Word

/-- The allocation uses three interleaved words per lane: left, right, output. -/
def left (lane : Fin n) : Nat := 3 * lane.val
def right (lane : Fin n) : Nat := 3 * lane.val + 1
def output (lane : Fin n) : Nat := 3 * lane.val + 2

def pointer (index : Nat) : Address := BitVec.ofNat 64 (4 * index)

def program (lane : Fin n) : List Instr := [
  .plain (.load 0 (.imm (pointer (left lane)))),
  .plain (.load 1 (.imm (pointer (right lane)))),
  .plain (.bin32 .add 2 (.reg 0) (.reg 1)),
  .plain (.store (.imm (pointer (output lane))) (.reg 2)),
  .plain .exit]

def replace (f : Fin n → α) (lane : Fin n) (value : α) : Fin n → α :=
  fun other => if other = lane then value else f other

@[simp] theorem replace_same : replace f lane value lane = value := by simp [replace]
@[simp] theorem replace_other (h : other ≠ lane) : replace f lane value other = f other := by
  simp [replace,h]

def install (s : State n) (lane : Fin n) (cursor : Nat)
    (registers : Nat → Word) (memory : List Word) : State n :=
  ⟨memory, replace s.cursor lane cursor, replace s.regs lane registers⟩

/-- Exactly one instruction of one lane is scheduled. Completed lanes stutter. -/
def advance (lane : Fin n) (s : State n) : State n :=
  match s.cursor lane with
  | 0 => install s lane 1 (update (s.regs lane) 0 s.memory[left lane]!) s.memory
  | 1 => install s lane 2 (update (s.regs lane) 1 s.memory[right lane]!) s.memory
  | 2 => install s lane 3 (update (s.regs lane) 2 (s.regs lane 0 + s.regs lane 1)) s.memory
  | 3 => install s lane 4 (s.regs lane) (s.memory.set (output lane) (s.regs lane 2))
  | 4 => install s lane 5 (s.regs lane) s.memory
  | _ => s

def execute : List (Fin n) → State n → State n
  | [], s => s
  | lane :: schedule, s => execute schedule (advance lane s)

def initial (memory : List Word) (registers : Fin n → Nat → Word) : State n :=
  ⟨memory, fun _ => 0, registers⟩

def sum (memory : List Word) (lane : Fin n) : Word := memory[left lane]! + memory[right lane]!

/-- The invariant uses original inputs, not the desired final-memory equality. -/
structure Invariant (memory : List Word) (s : State n) : Prop where
  length : s.memory.length = memory.length
  cursor : ∀ lane, s.cursor lane ≤ 5
  inputs : ∀ lane : Fin n, s.memory[left lane]! = memory[left lane]! ∧
    s.memory[right lane]! = memory[right lane]!
  first : ∀ lane, 1 ≤ s.cursor lane → s.regs lane 0 = memory[left lane]!
  second : ∀ lane, 2 ≤ s.cursor lane → s.regs lane 1 = memory[right lane]!
  added : ∀ lane, 3 ≤ s.cursor lane → s.regs lane 2 = sum memory lane
  stored : ∀ lane, 4 ≤ s.cursor lane → s.memory[output lane]! = sum memory lane

@[simp] theorem initial_invariant (memory : List Word) (registers : Fin n → Nat → Word) :
    Invariant memory (initial memory registers) := by
  constructor <;> simp [initial]

theorem output_ne_left (a b : Fin n) : output a ≠ left b := by simp [output,left]; omega
theorem output_ne_right (a b : Fin n) : output a ≠ right b := by simp [output,right]; omega
theorem output_injective (a b : Fin n) (h : output a = output b) : a = b := by
  apply Fin.ext; simp [output] at h; omega

@[simp] theorem get_set_other (memory : List Word) (i j : Nat) (value : Word) (h : i ≠ j) :
    (memory.set i value)[j]! = memory[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

@[simp] theorem get_set_same (memory : List Word) (i : Nat) (value : Word) (h : i < memory.length) :
    (memory.set i value)[i]! = value := by
  simp [h]

/-- Advancing a lane preserves another lane's register state and cursor. -/
theorem advance_other (s : State n) (lane other : Fin n) (h : other ≠ lane) :
    (advance lane s).cursor other = s.cursor other ∧
    (advance lane s).regs other = s.regs other := by
  unfold advance
  split <;> simp [install,replace,h]

/-- Only the designated output can be written, regardless of the loaded values. -/
theorem advance_frame (s : State n) (lane : Fin n) (index : Nat)
    (apart : output lane ≠ index) :
    (advance lane s).memory[index]? = s.memory[index]? := by
  unfold advance
  split <;> simp [install,List.getElem?_set_ne apart]

/-- The shared allocation, rather than a family of independent private memories,
is updated here. Output uniqueness and input/output separation discharge interference. -/
theorem advance_invariant (memory : List Word) (s : State n) (lane : Fin n)
    (extent : 3 * n ≤ memory.length) (valid : Invariant memory s) :
    Invariant memory (advance lane s) := by
  have cases : s.cursor lane = 0 ∨ s.cursor lane = 1 ∨ s.cursor lane = 2 ∨
      s.cursor lane = 3 ∨ s.cursor lane = 4 ∨ s.cursor lane = 5 := by
    have := valid.cursor lane; omega
  have bound : output lane < s.memory.length := by
    have := lane.isLt
    rw [valid.length]
    simp [output]; omega
  have inputs := valid.inputs
  have first := valid.first
  have second := valid.second
  have added := valid.added
  have stored := valid.stored
  have different (a b : Fin n) (h : b ≠ a) : output a ≠ output b := by
    intro eq; exact h (output_injective a b eq).symm
  rcases cases with h | h | h | h | h | h
  all_goals simp only [advance,h]
  all_goals try exact valid
  all_goals constructor
  all_goals try simpa only [install, List.length_set] using valid.length
  all_goals intro other
  all_goals by_cases same : other = lane
  all_goals try subst other
  all_goals simp only [install,replace_same]
  all_goals try simp only [replace_other same]
  all_goals first
    | exact valid.cursor _
    | exact valid.inputs _
    | exact valid.first _
    | exact valid.second _
    | exact valid.added _
    | exact valid.stored _
    | (simp_all [update, sum, output_ne_left, output_ne_right])
  all_goals first
    | (apply first; omega)
    | (apply second; omega)
    | (apply added; omega)
    | (apply stored; omega)
    | (rw [first lane (by omega), second lane (by omega)])
    | (simpa [bound] using stored lane (by omega))

/-- Arbitrary finite schedules preserve the shared-memory invariant. -/
theorem execute_invariant (memory : List Word) (s : State n)
    (extent : 3 * n ≤ memory.length) (valid : Invariant memory s) (schedule : List (Fin n)) :
    Invariant memory (execute schedule s) := by
  induction schedule generalizing s with
  | nil => exact valid
  | cons lane schedule ih => exact ih _ (advance_invariant memory s lane extent valid)

/-- Preservation covers every word not designated as an output, including tails. -/
theorem execute_frame (s : State n) (schedule : List (Fin n)) (index : Nat)
    (apart : ∀ lane : Fin n, output lane ≠ index) :
    (execute schedule s).memory[index]? = s.memory[index]? := by
  induction schedule generalizing s with
  | nil => rfl
  | cons lane schedule ih =>
    exact (ih _).trans (advance_frame s lane index (apart lane))

def Complete (s : State n) : Prop := ∀ lane, s.cursor lane = 5

/-- Correctness for every completed mathematical advance schedule.
`execute_faithful` additionally supplies the pointer-width contract required to
interpret each transition as a scalar instruction. -/
theorem completed_correct (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3 * n ≤ memory.length) (schedule : List (Fin n))
    (completed : Complete (execute schedule (initial memory registers))) :
    ∀ lane : Fin n, (execute schedule (initial memory registers)).memory[output lane]! = sum memory lane := by
  intro lane
  exact (execute_invariant memory _ extent (initial_invariant ..) schedule).stored lane
    (by rw [completed lane]; decide)

/-- Scalar state used at one scheduled instruction. Auxiliary initial register
files are arbitrary: this program neither reads nor changes them. -/
def view (s : State n) (lane : Fin n) (addresses : Nat → Address)
    (predicates : Nat → Bool) : Scalar.State :=
  ⟨s.cursor lane, s.regs lane, addresses, predicates, s.memory⟩

def effect (s : State n) (lane : Fin n) : Option MemoryEffect :=
  match s.cursor lane with
  | 0 => some ⟨.load,pointer (left lane),s.memory[left lane]!⟩
  | 1 => some ⟨.load,pointer (right lane),s.memory[right lane]!⟩
  | 3 => some ⟨.store,pointer (output lane),s.regs lane 2⟩
  | _ => none

theorem pointer_index (memory : List Word) (index : Nat)
    (bound : index < memory.length) (noWrap : 4 * index < 2^64) :
    addressIndex memory (pointer index) = .ok index := by
  simp [addressIndex,pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt noWrap,bound]

/-- Each active scheduler transition is the actual next scalar instruction,
including its emitted effect. Bounds prevent the address representation wrapping. -/
theorem advance_is_scalar_step (s : State n) (lane : Fin n)
    (extent : 3 * n ≤ s.memory.length) (noWrap : 12 * n < 2^64)
    (active : s.cursor lane < 4) (addresses predicates) :
    ∃ event, step (program lane) (view s lane addresses predicates) =
      .next (view (advance lane s) lane addresses predicates) event ∧
      event.memory = effect s lane := by
  have inleft : left lane < s.memory.length := by have := lane.isLt; simp [left]; omega
  have inright : right lane < s.memory.length := by have := lane.isLt; simp [right]; omega
  have inout : output lane < s.memory.length := by have := lane.isLt; simp [output]; omega
  have l := pointer_index s.memory (left lane) inleft (by have := lane.isLt; simp [left]; omega)
  have r := pointer_index s.memory (right lane) inright (by have := lane.isLt; simp [right]; omega)
  have o := pointer_index s.memory (output lane) inout (by have := lane.isLt; simp [output]; omega)
  have cases : s.cursor lane = 0 ∨ s.cursor lane = 1 ∨ s.cursor lane = 2 ∨ s.cursor lane = 3 := by omega
  rcases cases with h | h | h | h <;>
    simp [step,stepWith,view,program,eval,Instr.plain,Guard.eval,Operand32.eval,
      Operand64.eval,BinOp.eval,h,l,r,o,advance,install,effect,occurrence]

/-- Exit is explicitly executed; cursor 5 is the scheduler's completed marker. -/
theorem exit_is_scalar_step (s : State n) (lane : Fin n)
    (atExit : s.cursor lane = 4) (addresses predicates) :
    ∃ event, step (program lane) (view s lane addresses predicates) =
      .halted (view s lane addresses predicates) event ∧ event.memory = none ∧
      (advance lane s).cursor lane = 5 := by
  simp [step,stepWith,view,program,eval,Instr.plain,Guard.eval,atExit,advance,install,occurrence]

/-- Every generated memory effect is a checked aligned four-byte scalar access. -/
theorem scheduled_access_safe (s : State n) (lane : Fin n)
    (extent : 3 * n ≤ s.memory.length) (noWrap : 12 * n < 2^64)
    (active : s.cursor lane < 4) (memoryEffect : MemoryEffect)
    (emits : effect s lane = some memoryEffect) :
    ValidAddress s.memory memoryEffect.address := by
  obtain ⟨event,transition,memory⟩ := advance_is_scalar_step s lane extent noWrap active
    (fun _ => 0) (fun _ => false)
  exact step_memory_safe transition (memory.trans emits)

theorem cursor_advance (s : State n) (chosen lane : Fin n)
    (bounded : ∀ i, s.cursor i ≤ 5) :
    (advance chosen s).cursor lane =
      if lane = chosen then min (s.cursor lane + 1) 5 else s.cursor lane := by
  by_cases same : lane = chosen
  · subst lane
    have cases : s.cursor chosen = 0 ∨ s.cursor chosen = 1 ∨ s.cursor chosen = 2 ∨
      s.cursor chosen = 3 ∨ s.cursor chosen = 4 ∨ s.cursor chosen = 5 := by have := bounded chosen; omega
    rcases cases with h | h | h | h | h | h <;> simp [advance,install,h]
  · simp only [if_neg same]
    exact (advance_other s chosen lane same).1

theorem execute_cursor (s : State n) (schedule : List (Fin n)) (lane : Fin n)
    (bounded : ∀ i, s.cursor i ≤ 5) :
    (execute schedule s).cursor lane = min (s.cursor lane + schedule.count lane) 5 := by
  induction schedule generalizing s with
  | nil => simp [execute,Nat.min_eq_left (bounded lane)]
  | cons chosen schedule ih =>
    have nextBound : ∀ i, (advance chosen s).cursor i ≤ 5 := by
      intro i
      rw [cursor_advance s chosen i bounded]
      split
      · exact Nat.min_le_right _ _
      · exact bounded i
    rw [execute, ih _ nextBound, cursor_advance s chosen lane bounded]
    by_cases same : lane = chosen
    · subst lane; simp only [ite_true,List.count_cons_self]; omega
    · simp [same,Ne.symm same]

/-- Five rounds, each scheduling every lane once. Empty launches complete vacuously. -/
def schedule (n : Nat) : List (Fin n) :=
  let round := List.finRange n
  round ++ round ++ round ++ round ++ round

theorem schedule_length : (schedule n).length = 5 * n := by simp [schedule]; omega

theorem schedule_complete (memory : List Word) (registers : Fin n → Nat → Word) :
    Complete (execute (schedule n) (initial memory registers)) := by
  intro lane
  rw [execute_cursor _ _ _ (by simp [initial])]
  have positive : 0 < (List.finRange n).count lane := List.count_pos_iff.mpr (List.mem_finRange lane)
  simp only [initial,schedule,List.count_append]
  omega

/-- A step is justified by the scalar interpreter, or is stuttering of a thread
whose explicit exit has already executed. Other threads remain governed by `advance`. -/
def FaithfulStep (s : State n) (lane : Fin n) : Prop :=
  (s.cursor lane < 4 ∧ ∃ event,
    step (program lane) (view s lane (fun _ => 0) (fun _ => false)) =
      .next (view (advance lane s) lane (fun _ => 0) (fun _ => false)) event ∧
      event.memory = effect s lane) ∨
  (s.cursor lane = 4 ∧ ∃ event,
    step (program lane) (view s lane (fun _ => 0) (fun _ => false)) =
      .halted (view s lane (fun _ => 0) (fun _ => false)) event ∧
      event.memory = none ∧ (advance lane s).cursor lane = 5) ∨
  (s.cursor lane = 5 ∧ advance lane s = s)

inductive Execution : List (Fin n) → State n → State n → Prop where
  | nil : Execution [] s s
  | cons {dispatches : List (Fin n)} : FaithfulStep s lane → Execution dispatches (advance lane s) final →
      Execution (lane :: dispatches) s final

theorem faithful_step (s : State n) (lane : Fin n) (extent : 3 * n ≤ s.memory.length)
    (noWrap : 12 * n < 2^64) (bounded : s.cursor lane ≤ 5) : FaithfulStep s lane := by
  by_cases active : s.cursor lane < 4
  · exact Or.inl ⟨active,advance_is_scalar_step s lane extent noWrap active _ _⟩
  by_cases exiting : s.cursor lane = 4
  · exact Or.inr (Or.inl ⟨exiting,exit_is_scalar_step s lane exiting _ _⟩)
  have done : s.cursor lane = 5 := by omega
  exact Or.inr (Or.inr ⟨done,by simp [advance,done]⟩)

/-- All prefixes use real, nonfaulting scalar instructions under the allocation
and pointer-width contract. The final state may still contain unfinished lanes. -/
theorem execute_faithful (memory : List Word) (s : State n) (schedule : List (Fin n))
    (extent : 3 * n ≤ memory.length) (noWrap : 12 * n < 2^64)
    (valid : Invariant memory s) : Execution schedule s (execute schedule s) := by
  induction schedule generalizing s with
  | nil => exact .nil
  | cons lane schedule ih =>
    apply Execution.cons
    · exact faithful_step s lane (by rw [valid.length]; exact extent) noWrap (valid.cursor lane)
    · exact ih _ (advance_invariant memory s lane extent valid)

/-- A complete execution over one shared allocation, with all results and the
untouched-memory frame. This is existence, not unrestricted scheduler progress. -/
theorem completed_execution_exists (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3 * n ≤ memory.length) (noWrap : 12 * n < 2^64) :
    ∃ (dispatches : List (Fin n)) (final : State n),
      dispatches.length = 5 * n ∧ Execution dispatches (initial memory registers) final ∧
      Complete final ∧ (∀ lane : Fin n, final.memory[output lane]! = sum memory lane) ∧
      (∀ index, (∀ lane : Fin n, output lane ≠ index) → final.memory[index]? = memory[index]?) := by
  refine ⟨schedule n, execute (schedule n) (initial memory registers), schedule_length,
    execute_faithful memory _ _ extent noWrap (initial_invariant ..), schedule_complete memory registers,
    completed_correct memory registers extent _ (schedule_complete memory registers), ?_⟩
  exact fun index apart => execute_frame _ _ index apart

/-- A memory label is extracted from the same effect justified by scalar stepping. -/
def emitted (s : State n) (lane : Fin n) : Option Ptx.Occurrence :=
  (effect s lane).map (MemoryWitness.label lane.val (s.cursor lane))

def trace : List (Fin n) → State n → List Ptx.Occurrence
  | [], _ => []
  | lane :: rest, s => (emitted s lane).toList ++ trace rest (advance lane s)

/-- Expected remaining memory labels, in the lane's own execution order. -/
def remaining (memory : List Word) (lane : Fin n) (cursor : Nat) : List Ptx.Occurrence :=
  let a : Ptx.Occurrence := ⟨some lane.val,0,⟨.load .relaxed,left lane,memory[left lane]!⟩⟩
  let b : Ptx.Occurrence := ⟨some lane.val,1,⟨.load .relaxed,right lane,memory[right lane]!⟩⟩
  let c : Ptx.Occurrence := ⟨some lane.val,3,⟨.store .relaxed,output lane,sum memory lane⟩⟩
  match cursor with
  | 0 => [a,b,c]
  | 1 => [b,c]
  | 2 | 3 => [c]
  | _ => []

def laneTrace (lane : Fin n) (events : List Ptx.Occurrence) : List Ptx.Occurrence :=
  events.filter (fun e => e.thread == some lane.val)

theorem emitted_canonical (memory : List Word) (s : State n) (lane : Fin n)
    (valid : Invariant memory s) (noWrap : 12 * n < 2^64) :
    (emitted s lane).toList ++ remaining memory lane ((advance lane s).cursor lane) =
      remaining memory lane (s.cursor lane) := by
  have lp : (pointer (left lane)).toNat = 4 * left lane := by
    simp only [pointer,BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt; have := lane.isLt; simp [left]; omega
  have rp : (pointer (right lane)).toNat = 4 * right lane := by
    simp only [pointer,BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt; have := lane.isLt; simp [right]; omega
  have op : (pointer (output lane)).toNat = 4 * output lane := by
    simp only [pointer,BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt; have := lane.isLt; simp [output]; omega
  have cases : s.cursor lane = 0 ∨ s.cursor lane = 1 ∨ s.cursor lane = 2 ∨
      s.cursor lane = 3 ∨ s.cursor lane = 4 ∨ s.cursor lane = 5 := by have := valid.cursor lane; omega
  rcases cases with h | h | h | h | h | h
  all_goals simp [emitted,effect,advance,install,remaining,MemoryWitness.label,h,lp,rp,op,
    (valid.inputs lane).1,(valid.inputs lane).2]
  exact valid.added lane (by omega)

theorem emitted_thread (s : State n) (lane : Fin n) (event : Ptx.Occurrence)
    (member : event ∈ (emitted s lane).toList) : event.thread = some lane.val := by
  unfold emitted effect at member
  split at member <;> simp_all [MemoryWitness.label]

theorem filter_emitted (s : State n) (chosen lane : Fin n) :
    laneTrace lane (emitted s chosen).toList =
      if lane = chosen then (emitted s chosen).toList else [] := by
  by_cases same : lane = chosen
  · subst lane
    simp only [laneTrace,ite_true]
    apply List.filter_eq_self.mpr
    intro event member
    simp [emitted_thread s chosen event member]
  · simp only [laneTrace,if_neg same]
    apply List.filter_eq_nil_iff.mpr
    intro event member
    have distinct : chosen.val ≠ lane.val := by
      intro he; exact same (Fin.ext he).symm
    simp [emitted_thread s chosen event member,distinct]

/-- Telescoping trace correspondence holds for every finite instruction schedule. -/
theorem trace_correspondence (memory : List Word) (s : State n) (dispatches : List (Fin n))
    (extent : 3 * n ≤ memory.length) (noWrap : 12 * n < 2^64)
    (valid : Invariant memory s) (lane : Fin n) :
    laneTrace lane (trace dispatches s) ++ remaining memory lane ((execute dispatches s).cursor lane) =
      remaining memory lane (s.cursor lane) := by
  induction dispatches generalizing s with
  | nil => simp [trace,execute,laneTrace]
  | cons chosen rest ih =>
    have nextValid := advance_invariant memory s chosen extent valid
    simp only [trace,execute,laneTrace,List.filter_append,List.append_assoc]
    change laneTrace lane (emitted s chosen).toList ++
      (laneTrace lane (trace rest (advance chosen s)) ++ _) = _
    rw [ih _ nextValid,filter_emitted]
    by_cases same : lane = chosen
    · subst lane
      simpa using emitted_canonical memory s chosen valid noWrap
    · rw [if_neg same]
      simpa only [List.nil_append] using congrArg (remaining memory lane) (advance_other s chosen lane same).1

/-- Every completed shared execution supplies exactly these actual per-thread
memory events; their enumeration is independent of the interleaving schedule. -/
theorem completed_trace (memory : List Word) (registers : Fin n → Nat → Word)
    (dispatches : List (Fin n)) (extent : 3 * n ≤ memory.length)
    (noWrap : 12 * n < 2^64) (completed : Complete (execute dispatches (initial memory registers)))
    (lane : Fin n) :
    laneTrace lane (trace dispatches (initial memory registers)) = remaining memory lane 0 := by
  have h := trace_correspondence memory (initial memory registers) dispatches extent noWrap
    (initial_invariant ..) lane
  rw [completed lane] at h
  simpa only [remaining,List.append_nil,initial] using h

/-- The scheduler never emits an unchecked memory label. -/
theorem emitted_access_safe (s : State n) (lane : Fin n)
    (extent : 3 * n ≤ s.memory.length) (noWrap : 12 * n < 2^64)
    (event : Ptx.Occurrence) (member : event ∈ (emitted s lane).toList) :
    AccessSafe s.memory.length event.effect := by
  have existsEffect : ∃ e, effect s lane = some e ∧ MemoryWitness.label lane.val (s.cursor lane) e = event := by
    simpa [emitted] using member
  obtain ⟨e,he,rfl⟩ := existsEffect
  have active : s.cursor lane < 4 := by
    unfold effect at he
    split at he <;> simp_all <;> omega
  have safe := scheduled_access_safe s lane extent noWrap active e he
  apply access_safe_of_index_lt
  exact safe.2

/-- Every memory label of every finite interleaving is aligned and in the one
shared allocation, even if some threads have not yet exited. -/
theorem trace_access_safe (memory : List Word) (s : State n) (dispatches : List (Fin n))
    (extent : 3 * n ≤ memory.length) (noWrap : 12 * n < 2^64)
    (valid : Invariant memory s) (event : Ptx.Occurrence)
    (member : event ∈ trace dispatches s) : AccessSafe memory.length event.effect := by
  induction dispatches generalizing s with
  | nil => simp [trace] at member
  | cons lane rest ih =>
    simp only [trace,List.mem_append] at member
    rcases member with head | tail
    · rw [← valid.length]
      exact emitted_access_safe s lane (by rw [valid.length]; exact extent) noWrap event head
    · exact ih _ (advance_invariant memory s lane extent valid) tail

end Ptx.Scalar.SharedVector
