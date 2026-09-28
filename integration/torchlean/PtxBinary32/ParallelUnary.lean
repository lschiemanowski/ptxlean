import PtxBinary32.SoftmaxMemory
import Ptx.SharedReductionControl
import Ptx.ScalarRules

/-! A barrier-free parallel adapter for independent elementwise passes. The
single arena uses the existing checked scalar accesses. Candidate reads and
all permitted arithmetic results remain free; memory admission is separate.
No total executable exponential evaluator is asserted. -/
namespace Ptx.Scalar.ParallelUnary

abbrev Instr := SoftmaxMemory.Instr

structure Lane where
  scalar : Scalar.State
  halted : Bool

structure State (n : Nat) where
  lanes : Fin n → Lane
  global : List Word

inductive Event (n : Nat) where
  | scalar (thread : Fin n) (event : Scalar.Occurrence)
  | binary (thread : Fin n) (event : Scalar.Binary32.Occurrence)
  | exponential (thread : Fin n) (event : Scalar.Exponential.Occurrence)
  | reciprocal (thread : Fin n) (event : Scalar.Reciprocal.Occurrence)

def Event.thread : Event n → Fin n
  | .scalar t _ | .binary t _ | .exponential t _ | .reciprocal t _ => t

def Event.pc : Event n → Nat
  | .scalar _ e => e.pc
  | .binary _ e => e.pc
  | .exponential _ e => e.pc
  | .reciprocal _ e => e.pc

def Event.instruction : Event n → Instr
  | .scalar _ e => .scalar e.instruction
  | .binary _ e => .binary e.instruction
  | .exponential _ e => .exponential e.instruction
  | .reciprocal _ e => .reciprocal e.instruction

def Event.memory : Event n → Option Scalar.MemoryEffect
  | .scalar _ e => e.memory
  | _ => none

def setLane (s : State n) (thread : Fin n) (lane : Lane) : State n :=
  {s with lanes := Function.update s.lanes thread lane}

def input (s : State n) (thread : Fin n) : Scalar.State :=
  {(s.lanes thread).scalar with memory := s.global}

def install (s : State n) (thread : Fin n) (next : Scalar.State) (halted : Bool) : State n :=
  ⟨Function.update s.lanes thread ⟨next,halted⟩,next.memory⟩

/-- The successful instruction relation has no branch for unsupported positive
finite exponential arguments. Such arguments are outside the provider's scope,
not PTX undefined behavior. -/
inductive Exec (candidate : Option Word) (thread : Fin n) : Instr → State n → State n → Event n → Prop
  | scalarNext {i s next event} (eval : Scalar.eval candidate i (input s thread)=.next next event) :
      Exec candidate thread (.scalar i) s (install s thread next (s.lanes thread).halted) (.scalar thread event)
  | scalarHalted {i s next event} (eval : Scalar.eval candidate i (input s thread)=.halted next event) :
      Exec candidate thread (.scalar i) s (install s thread next true) (.scalar thread event)
  | binary {i s next event} (eval : Scalar.Binary32.Eval i (s.lanes thread).scalar next event) :
      Exec candidate thread (.binary i) s (setLane s thread ⟨next,(s.lanes thread).halted⟩) (.binary thread event)
  | exponential {i s next event} (eval : Scalar.Exponential.Eval i (s.lanes thread).scalar next event) :
      Exec candidate thread (.exponential i) s (setLane s thread ⟨next,(s.lanes thread).halted⟩) (.exponential thread event)
  | reciprocal {i s next event} (eval : Scalar.Reciprocal.Eval i (s.lanes thread).scalar next event) :
      Exec candidate thread (.reciprocal i) s (setLane s thread ⟨next,(s.lanes thread).halted⟩) (.reciprocal thread event)

/-- This adapter retains the selected PTX 9.4 / SM 7.0-or-newer target domain. -/
def Supported (target : Target) : Prop := target.isa=94 ∧ 70≤target.sm

def Step (target : Target) (program : List Instr) (candidate : Option Word) (thread : Fin n)
    (s t : State n) (event : Event n) : Prop :=
  Supported target ∧ (s.lanes thread).halted=false ∧
    ∃i, program[(s.lanes thread).scalar.pc]?=some i ∧ Exec candidate thread i s t event

inductive Runs {n : Nat} (target : Target) (program : List Instr) : State n → List (Event n) → State n → Prop
  | nil : Runs target program s [] s
  | cons : Step target program candidate thread s middle event → Runs target program middle rest final →
      Runs target program s (event::rest) final

/-- Concrete reads are used only to build a separate existence witness. -/
inductive ConcreteRuns {n : Nat} (target : Target) (program : List Instr) : State n → List (Event n) → State n → Prop
  | nil : ConcreteRuns target program s [] s
  | cons : Step target program none thread s middle event → ConcreteRuns target program middle rest final →
      ConcreteRuns target program s (event::rest) final

variable {n : Nat} {s t middle final : State n} {selected : Fin n} {events : List (Event n)}

theorem ConcreteRuns.toRuns (run : ConcreteRuns target program s events final) :
    Runs target program s events final := by
  induction run with
  | nil => exact .nil
  | cons step _ ih => exact .cons step ih

theorem Runs.append (a : Runs target program s left middle) (b : Runs target program middle right final) :
    Runs target program s (left++right) final := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

theorem ConcreteRuns.append (a : ConcreteRuns target program s left middle)
    (b : ConcreteRuns target program middle right final) : ConcreteRuns target program s (left++right) final := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

theorem exec_other (exec : Exec candidate selected i s t event) (other : Fin n) (different : other≠selected) :
    t.lanes other=s.lanes other := by
  cases exec <;> simp [setLane,install,Function.update,different]

theorem step_other (step : Step target program candidate selected s t event) (other : Fin n) (different : other≠selected) :
    t.lanes other=s.lanes other := by
  obtain ⟨_,_,_,_,exec⟩ := step
  exact exec_other exec other different

theorem exec_length (exec : Exec candidate selected i s t event) : t.global.length=s.global.length := by
  cases exec with
  | scalarNext h => exact Scalar.eval_memory_length h
  | scalarHalted h => exact congrArg (fun x : Scalar.State => x.memory.length) (Scalar.eval_halted h).1
  | binary _ | exponential _ | reciprocal _ => rfl

theorem step_length (step : Step target program candidate selected s t event) : t.global.length=s.global.length := by
  obtain ⟨_,_,_,_,exec⟩ := step
  exact exec_length exec

theorem runs_length (run : Runs target program s events final) : final.global.length=s.global.length := by
  induction run with
  | nil => rfl
  | cons step _ ih => exact ih.trans (step_length step)

theorem exec_memory_safe (exec : Exec candidate selected i s t event)
    (emitted : event.memory=some effect) : Scalar.ValidAddress s.global effect.address := by
  cases exec with
  | scalarNext h => exact Scalar.eval_memory_safe h emitted
  | scalarHalted h => simp [Event.memory,(Scalar.eval_halted h).2] at emitted
  | binary _ | exponential _ | reciprocal _ => simp [Event.memory] at emitted

theorem step_memory_safe (step : Step target program candidate selected s t event)
    (emitted : event.memory=some effect) : Scalar.ValidAddress s.global effect.address := by
  obtain ⟨_,_,_,_,exec⟩ := step
  exact exec_memory_safe exec emitted

theorem runs_memory_safe (run : Runs target program s events final)
    (member : event∈events) (emitted : event.memory=some effect) : Scalar.ValidAddress s.global effect.address := by
  induction run with
  | nil => simp at member
  | cons step rest ih =>
    cases member with
    | head => exact step_memory_safe step emitted
    | tail _ member => simpa only [Scalar.ValidAddress,step_length step] using ih member

theorem scalar_next_origin (h : Scalar.eval candidate i old=.next next event) :
    event.instruction=i ∧ event.pc=old.pc := by
  cases i with
  | mk guard op =>
    cases op <;> cases hg : guard.eval old <;> simp only [Scalar.eval,hg,↓reduceIte] at h
    all_goals first
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj h; exact ⟨rfl,rfl⟩)
      | contradiction
      | (split at h <;> first | contradiction | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj h; exact ⟨rfl,rfl⟩))

theorem scalar_halted_origin (h : Scalar.eval candidate i old=.halted next event) :
    event.instruction=i ∧ event.pc=old.pc := by
  cases i with
  | mk guard op =>
    cases op <;> cases hg : guard.eval old <;> simp only [Scalar.eval,hg,↓reduceIte] at h
    all_goals first
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.halted.inj h; exact ⟨rfl,rfl⟩)
      | contradiction
      | (split at h <;> contradiction)

theorem exec_origin (exec : Exec candidate selected i s t event) :
    event.thread=selected ∧ event.pc=(s.lanes selected).scalar.pc ∧ event.instruction=i := by
  cases exec with
  | scalarNext h => exact ⟨rfl,(scalar_next_origin h).2,congrArg SoftmaxMemory.Instr.scalar (scalar_next_origin h).1⟩
  | scalarHalted h => exact ⟨rfl,(scalar_halted_origin h).2,congrArg SoftmaxMemory.Instr.scalar (scalar_halted_origin h).1⟩
  | binary h => cases h <;> exact ⟨rfl,rfl,rfl⟩
  | exponential h => cases h <;> exact ⟨rfl,rfl,rfl⟩
  | reciprocal h => cases h <;> exact ⟨rfl,rfl,rfl⟩

theorem step_origin (step : Step target program candidate selected s t event) :
    event.thread=selected ∧ event.pc=(s.lanes selected).scalar.pc ∧
    program[event.pc]?=some event.instruction := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  obtain ⟨thread,pc,instr⟩ := exec_origin exec
  exact ⟨thread,pc,by rw [pc,instr]; exact fetch⟩

theorem runs_fetch (run : Runs target program s events final) (member : event∈events) :
    program[event.pc]?=some event.instruction := by
  induction run with
  | nil => simp at member
  | cons step _ ih => cases member with
    | head => exact (step_origin step).2.2
    | tail _ member => exact ih member

/-- Actual scalar effects expose their fetched instruction, predicate and
memory direction. Arithmetic events never become fabricated memory labels. -/
theorem step_memory_origin (step : Step target program candidate selected s t (.scalar thread occ))
    (memory : occ.memory=some effect) :
    thread=selected ∧ occ.pc=(s.lanes selected).scalar.pc ∧
    program[occ.pc]?=some (.scalar occ.instruction) ∧ occ.executed=true ∧
    Scalar.SharedReduction.Machine.Control.memoryKind occ.instruction.op=some effect.kind := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  cases exec with
  | scalarNext h =>
    have origin := Scalar.SharedReduction.Machine.Control.eval_effect_origin _ _ _ _ _ _ h memory
    exact ⟨rfl,origin.2.1,by rw [origin.1,origin.2.1]; exact fetch,origin.2.2.1,origin.1 ▸ origin.2.2.2⟩
  | scalarHalted h => simp [(Scalar.eval_halted h).2] at memory

/-- Global memory can change only at an actual emitted store. -/
theorem step_frame (step : Step target program candidate selected s t event) (index : Nat)
    (untouched : ∀effect, event.memory=some effect → effect.kind=.store → effect.address.toNat/4≠index) :
    t.global[index]?=s.global[index]? := by
  obtain ⟨_,_,_,_,exec⟩ := step
  cases exec with
  | scalarNext h =>
    apply Scalar.Rules.eval_frame h
    rintro ⟨effect,memory,store,eq⟩
    exact untouched effect memory store eq
  | scalarHalted h => exact congrArg (fun x : Scalar.State => x.memory[index]?) (Scalar.eval_halted h).1
  | binary _ | exponential _ | reciprocal _ => rfl

theorem runs_frame (run : Runs target program s events final) (index : Nat)
    (untouched : ∀event∈events, ∀effect, event.memory=some effect → effect.kind=.store → effect.address.toNat/4≠index) :
    final.global[index]?=s.global[index]? := by
  induction run with
  | nil => rfl
  | cons step _ ih =>
    exact (ih (fun event member => untouched event (List.mem_cons_of_mem _ member))).trans
      (step_frame step index (untouched _ (by simp)))

/-- Enabled exponential steps cannot escape the existing partial provider's
operand domain; unsupported finite positive inputs do not acquire a fake result. -/
theorem exec_exponential_supported (exec : Exec candidate selected (.exponential i) s t event)
    (enabled : i.guard.eval (s.lanes selected).scalar=true) :
    Ptx.Binary32.Exponential.Supported (i.source.eval (s.lanes selected).scalar) := by
  cases exec with
  | exponential h =>
    obtain disabled | supported := (Scalar.Exponential.eval_exists_iff i _).mp ⟨_,_,h⟩
    · simp [enabled] at disabled
    · exact supported

end Ptx.Scalar.ParallelUnary
