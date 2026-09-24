import Ptx.Scalar
import Ptx.Environment

/-! Mechanism for total pure instruction families on the existing scalar state.
A family and its target predicate require separate PTX source review. Syntactic
operand metadata is not a PTX dependency or no-thin-air relation. -/
namespace Ptx.Scalar.Pure32

/-- Polarity matches `Guard.pred`: false selects the negated register value.
Immediate/polarity forms are generic mechanisms, not promises of PTX text legality. -/
inductive OperandPred where
  | reg (index : Nat) (positive : Bool)
  | imm (value : Bool)
  deriving DecidableEq, Repr

def OperandPred.eval (s : State) : OperandPred → Bool
  | .reg index positive => s.preds index == positive
  | .imm value => value

def OperandPred.reads : OperandPred → List Register
  | .reg index _ => [.predicate index]
  | .imm _ => []

@[simp] theorem predicate_positive (s : State) (index : Nat) :
    OperandPred.eval s (.reg index true) = s.preds index := by simp [OperandPred.eval]

@[simp] theorem predicate_negative (s : State) (index : Nat) :
    OperandPred.eval s (.reg index false) = !s.preds index := by simp [OperandPred.eval]

/-- Finite arities and nonempty relations; no determinism or PTX fidelity is
implied by this structure. Unsupported targets are excluded at fetched steps. -/
structure Family (Operation : Type) where
  wordArity : Operation → Nat
  predicateArity : Operation → Nat
  Results : (op : Operation) → (Fin (wordArity op) → Word) →
    (Fin (predicateArity op) → Bool) → Word → Prop
  inhabited : ∀ op words predicates, ∃ value, Results op words predicates value
  Supported : Target → Operation → Prop

/-- Package a total computation as a single-result family. The supplied function
and target predicate still need their own instruction source justification. -/
def Family.ofFunction (wordArity predicateArity : Operation → Nat)
    (compute : (op : Operation) → (Fin (wordArity op) → Word) →
      (Fin (predicateArity op) → Bool) → Word)
    (supported : Target → Operation → Prop) : Family Operation where
  wordArity := wordArity
  predicateArity := predicateArity
  Results := fun op words predicates value => value = compute op words predicates
  inhabited := fun op words predicates => ⟨compute op words predicates, rfl⟩
  Supported := supported

theorem Family.ofFunction_results (wordArity predicateArity : Operation → Nat)
    (compute : (op : Operation) → (Fin (wordArity op) → Word) →
      (Fin (predicateArity op) → Bool) → Word)
    (supported : Target → Operation → Prop) (op : Operation)
    (words : Fin (wordArity op) → Word) (predicates : Fin (predicateArity op) → Bool) (value : Word) :
    (Family.ofFunction wordArity predicateArity compute supported).Results op words predicates value ↔
      value = compute op words predicates := Iff.rfl

variable {Operation : Type} {family : Family Operation}

structure Instr (family : Family Operation) where
  guard : Guard := .always
  operation : Operation
  destination : Nat
  words : Fin (family.wordArity operation) → Operand32
  predicates : Fin (family.predicateArity operation) → OperandPred

def Instr.wordValues (i : Instr family) (s : State) :
    Fin (family.wordArity i.operation) → Word := fun index => (i.words index).eval s

def Instr.predicateValues (i : Instr family) (s : State) :
    Fin (family.predicateArity i.operation) → Bool := fun index => (i.predicates index).eval s

/-- Ordered syntactic operands, preserving repeats and including every branch's
inputs in a selecting operation. This is not semantic dependency metadata. -/
def Instr.sourceReads (i : Instr family) : List Register :=
  (List.ofFn i.words).flatMap Operand32.reads ++
    (List.ofFn i.predicates).flatMap OperandPred.reads

theorem Instr.sourceReads_word (i : Instr family) (index : Fin (family.wordArity i.operation))
    (register : Nat) (source : i.words index = .reg register) :
    .word register ∈ i.sourceReads := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨i.words index, List.mem_ofFn.mpr ⟨index, rfl⟩, by simp [source, Operand32.reads]⟩

theorem Instr.sourceReads_predicate (i : Instr family)
    (index : Fin (family.predicateArity i.operation)) (register : Nat) (positive : Bool)
    (source : i.predicates index = .reg register positive) : .predicate register ∈ i.sourceReads := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨i.predicates index, List.mem_ofFn.mpr ⟨index, rfl⟩,
    by simp [source, OperandPred.reads]⟩

structure Occurrence (family : Family Operation) where
  pc : Nat
  instruction : Instr family
  executed : Bool
  reads : List Register
  writes : List Register
  memory : Option MemoryEffect

def occurrence (s : State) (i : Instr family) (executed : Bool) : Occurrence family :=
  ⟨s.pc, i, executed, i.guard.reads ++ (if executed then i.sourceReads else []),
    (if executed then [.word i.destination] else []), none⟩

def write (s : State) (destination : Nat) (value : Word) : State :=
  {s with pc := s.pc + 1, regs := update s.regs destination value}

inductive Eval (i : Instr family) : State → State → Occurrence family → Prop
  | skipped {s} (disabled : i.guard.eval s = false) :
      Eval i s {s with pc := s.pc + 1} (occurrence s i false)
  | executed {s value} (enabled : i.guard.eval s = true)
      (result : family.Results i.operation (i.wordValues s) (i.predicateValues s) value) :
      Eval i s (write s i.destination value) (occurrence s i true)

/-- Successful admission only: unsupported operations have no step even under a
false guard. This does not specify the hardware's invalid-instruction behavior. -/
def Step (target : Target) (program : List (Instr family))
    (s next : State) (event : Occurrence family) : Prop :=
  ∃ i, program[s.pc]? = some i ∧ family.Supported target i.operation ∧ Eval i s next event

variable {i : Instr family} {s next : State} {event : Occurrence family}
  {target : Target} {program : List (Instr family)}

theorem eval_true_iff (i : Instr family) (s next : State) (event : Occurrence family)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      family.Results i.operation (i.wordValues s) (i.predicateValues s) value ∧
      next = write s i.destination value ∧ event = occurrence s i true := by
  constructor
  · intro h
    cases h with
    | skipped disabled => simp [enabled] at disabled
    | executed _ result => exact ⟨_, result, rfl, rfl⟩
  · rintro ⟨value, result, rfl, rfl⟩
    exact .executed enabled result

theorem eval_false_iff (i : Instr family) (s next : State) (event : Occurrence family)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc + 1} ∧ event = occurrence s i false := by
  constructor
  · intro h
    cases h with
    | skipped _ => exact ⟨rfl, rfl⟩
    | executed enabled _ => simp [disabled] at enabled
  · rintro ⟨rfl, rfl⟩
    exact .skipped disabled

theorem eval_destination (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    family.Results i.operation (i.wordValues s) (i.predicateValues s) (next.regs i.destination) := by
  cases evaluated with
  | skipped disabled => simp [enabled] at disabled
  | executed _ result => simpa [write] using result

theorem eval_frame (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds := by
  cases evaluated <;> simp [write]

theorem eval_other (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other := by
  cases evaluated <;> simp [write, update, different]

theorem eval_event (evaluated : Eval i s next event) :
    event = occurrence s i (i.guard.eval s) := by
  cases evaluated with
  | skipped disabled => simp [disabled]
  | executed enabled _ => simp [enabled]

theorem eval_reads (evaluated : Eval i s next event) :
    event.reads = i.guard.reads ++ (if i.guard.eval s then i.sourceReads else []) := by
  rw [eval_event evaluated]; rfl

theorem eval_writes (evaluated : Eval i s next event) :
    event.writes = if i.guard.eval s then [.word i.destination] else [] := by
  rw [eval_event evaluated]; rfl

theorem eval_no_memory (evaluated : Eval i s next event) : event.memory = none := by
  rw [eval_event evaluated]; rfl

/-- Input evaluation is in the pre-state, including a source/destination alias. -/
theorem eval_alias_read (evaluated : Eval i s next event) (enabled : i.guard.eval s = true)
    (index : Fin (family.wordArity i.operation)) (alias : i.words index = .reg i.destination) :
    i.wordValues s index = s.regs i.destination ∧
      family.Results i.operation (i.wordValues s) (i.predicateValues s) (next.regs i.destination) := by
  exact ⟨by simp [Instr.wordValues, alias, Operand32.eval], eval_destination evaluated enabled⟩

theorem repeated_word_values (i : Instr family) (s : State)
    (a b : Fin (family.wordArity i.operation)) (same : i.words a = i.words b) :
    i.wordValues s a = i.wordValues s b := by simp [Instr.wordValues, same]

theorem eval_positive_guard (i : Instr family) (s : State) (index : Nat) (value : Word)
    (guard : i.guard = .pred index true) (predicate : s.preds index = true)
    (result : family.Results i.operation (i.wordValues s) (i.predicateValues s) value) :
    Eval i s (write s i.destination value) (occurrence s i true) :=
  .executed (by simp [guard, Guard.eval, predicate]) result

theorem eval_negative_guard (i : Instr family) (s : State) (index : Nat) (value : Word)
    (guard : i.guard = .pred index false) (predicate : s.preds index = false)
    (result : family.Results i.operation (i.wordValues s) (i.predicateValues s) value) :
    Eval i s (write s i.destination value) (occurrence s i true) :=
  .executed (by simp [guard, Guard.eval, predicate]) result

theorem skip_positive_guard (i : Instr family) (s : State) (index : Nat)
    (guard : i.guard = .pred index true) (predicate : s.preds index = false) :
    Eval i s {s with pc := s.pc + 1} (occurrence s i false) :=
  .skipped (by simp [guard, Guard.eval, predicate])

theorem skip_negative_guard (i : Instr family) (s : State) (index : Nat)
    (guard : i.guard = .pred index false) (predicate : s.preds index = true) :
    Eval i s {s with pc := s.pc + 1} (occurrence s i false) :=
  .skipped (by simp [guard, Guard.eval, predicate])

theorem eval_exists (i : Instr family) (s : State) : ∃ next event, Eval i s next event := by
  cases enabled : i.guard.eval s with
  | false => exact ⟨_, _, .skipped enabled⟩
  | true =>
    obtain ⟨value, result⟩ := family.inhabited i.operation (i.wordValues s) (i.predicateValues s)
    exact ⟨_, _, .executed enabled result⟩

/-- Determinism is conditional; relational families may permit several outputs. -/
theorem eval_deterministic
    (functional : ∀ words predicates a b,
      family.Results i.operation words predicates a →
      family.Results i.operation words predicates b → a = b)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂ := by
  cases left with
  | skipped disabled =>
    cases right with
    | skipped _ => exact ⟨rfl,rfl⟩
    | executed enabled _ => simp [disabled] at enabled
  | executed enabled result₁ =>
    cases right with
    | skipped disabled => simp [enabled] at disabled
    | executed _ result₂ =>
      have same := functional _ _ _ _ result₁ result₂
      cases same
      exact ⟨rfl,rfl⟩

/-- Distinct permitted results stay distinct transitions; the shared mechanism
does not select one value from a nondeterministic relation. -/
theorem eval_preserves_choices (enabled : i.guard.eval s = true)
    (left : family.Results i.operation (i.wordValues s) (i.predicateValues s) a)
    (right : family.Results i.operation (i.wordValues s) (i.predicateValues s) b)
    (different : a ≠ b) :
    Eval i s (write s i.destination a) (occurrence s i true) ∧
    Eval i s (write s i.destination b) (occurrence s i true) ∧
    write s i.destination a ≠ write s i.destination b := by
  refine ⟨.executed enabled left, .executed enabled right, ?_⟩
  intro equal
  have same := congrArg (fun state => state.regs i.destination) equal
  exact different (by simpa [write] using same)

theorem step_origin (stepped : Step target program s next event) :
    ∃ i, program[s.pc]? = some i ∧ family.Supported target i.operation ∧
      event.pc = s.pc ∧ event.instruction = i ∧ Eval i s next event := by
  obtain ⟨i, fetched, supported, evaluated⟩ := stepped
  refine ⟨i, fetched, supported, ?_, ?_, evaluated⟩
  · rw [eval_event evaluated]; rfl
  · rw [eval_event evaluated]; rfl

theorem step_iff_of_fetch (fetch : program[s.pc]? = some i) :
    Step target program s next event ↔ family.Supported target i.operation ∧ Eval i s next event := by
  constructor
  · rintro ⟨found, fetched, supported, evaluated⟩
    have same : found = i := Option.some.inj (fetched.symm.trans fetch)
    subst found
    exact ⟨supported, evaluated⟩
  · rintro ⟨supported, evaluated⟩
    exact ⟨i, fetch, supported, evaluated⟩

theorem step_frame (stepped : Step target program s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds := by
  obtain ⟨_, _, _, evaluated⟩ := stepped
  exact eval_frame evaluated

theorem step_false_iff (fetch : program[s.pc]? = some i) (disabled : i.guard.eval s = false) :
    Step target program s next event ↔ family.Supported target i.operation ∧
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false := by
  rw [step_iff_of_fetch fetch, eval_false_iff i s next event disabled]

theorem step_exists (i : Instr family) (fetch : program[s.pc]? = some i)
    (supported : family.Supported target i.operation) : ∃ next event, Step target program s next event := by
  obtain ⟨next, event, evaluated⟩ := eval_exists i s
  exact ⟨next, event, i, fetch, supported, evaluated⟩

theorem step_no_fetch (missing : program[s.pc]? = none) : ¬ Step target program s next event := by
  rintro ⟨i, fetched, _⟩
  rw [missing] at fetched
  contradiction

theorem step_unsupported (fetch : program[s.pc]? = some i)
    (unsupported : ¬ family.Supported target i.operation) : ¬ Step target program s next event := by
  intro stepped
  exact unsupported ((step_iff_of_fetch fetch).mp stepped).1

/-- A record naming another instruction cannot be accepted as this fetched step. -/
theorem step_wrong_instruction (fetch : program[s.pc]? = some i)
    (different : event.instruction ≠ i) : ¬ Step target program s next event := by
  intro stepped
  have evaluated := ((step_iff_of_fetch fetch).mp stepped).2
  exact different (by rw [eval_event evaluated]; rfl)

theorem step_wrong_pc (different : event.pc ≠ s.pc) : ¬ Step target program s next event := by
  intro stepped
  obtain ⟨_, _, _, pc, _⟩ := step_origin stepped
  exact different pc

end Ptx.Scalar.Pure32
