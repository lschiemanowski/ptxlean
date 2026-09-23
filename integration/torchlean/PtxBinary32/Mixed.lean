import PtxBinary32.Instructions
import Ptx.ScalarRules

/-! Tagged scalar/FP finite execution over the original scalar state. Concrete
arena reads are a restricted sequential discipline, not general concurrent PTX
admission. Exit, incomplete advancing paths and failed dispatches are distinct. -/
namespace Ptx.Scalar.Mixed

inductive Instr where
  | scalar (instruction : Scalar.Instr)
  | binary32 (instruction : Scalar.Binary32.Instr)
  deriving DecidableEq, Repr

inductive Event where
  | scalar (event : Scalar.Occurrence)
  | binary32 (event : Scalar.Binary32.Occurrence)
  deriving DecidableEq, Repr

def Event.memory : Event → Option MemoryEffect
  | .scalar event => event.memory
  | .binary32 event => event.memory

def Event.pc : Event → Nat
  | .scalar event => event.pc
  | .binary32 event => event.pc

def Event.instruction : Event → Instr
  | .scalar event => .scalar event.instruction
  | .binary32 event => .binary32 event.instruction

inductive Outcome where
  | next (state : State) (event : Event)
  | halted (state : State) (event : Event)
  | fault (reason : Scalar.Fault)
  | unsupported (spelling : String)

def liftScalar : Scalar.StepResult → Outcome
  | .next state event => .next state (.scalar event)
  | .halted state event => .halted state (.scalar event)
  | .fault reason => .fault reason
  | .unsupported spelling => .unsupported spelling

inductive Eval : Instr → State → Outcome → Prop
  | scalar : Eval (.scalar i) s (liftScalar (Scalar.eval none i s))
  | binary32 : Scalar.Binary32.Eval i s next event →
      Eval (.binary32 i) s (.next next (.binary32 event))

/-- Scoped relaxed global loads/stores require sm_70, although FP needs only sm_20.
This numeric feature slice does not validate full target spellings. -/
def Eligible (target : Ptx.Target) : Prop := target.isa = 94 ∧ 70 ≤ target.sm

def Dispatch (target : Ptx.Target) (program : List Instr)
    (s : State) (outcome : Outcome) : Prop :=
  Eligible target ∧ match program[s.pc]? with
    | none => outcome = .fault (.invalidPC s.pc)
    | some i => Eval i s outcome

theorem eligible_binary32 (h : Eligible target) : Scalar.Binary32.SupportedTarget target :=
  ⟨h.1, by have := h.2; omega⟩

theorem eval_scalar_iff : Eval (.scalar i) s outcome ↔
    outcome = liftScalar (Scalar.eval none i s) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .scalar

theorem eval_binary32_iff : Eval (.binary32 i) s outcome ↔
    ∃ next event, Scalar.Binary32.Eval i s next event ∧
      outcome = .next next (.binary32 event) := by
  constructor
  · intro h; cases h with | binary32 h => exact ⟨_, _, h, rfl⟩
  · rintro ⟨next, event, h, rfl⟩; exact .binary32 h

theorem dispatch_fetch (fetch : program[s.pc]? = some i) :
    Dispatch target program s outcome ↔ Eligible target ∧ Eval i s outcome := by
  simp [Dispatch, fetch]

theorem dispatch_missing (fetch : program[s.pc]? = none) :
    Dispatch target program s outcome ↔
      Eligible target ∧ outcome = .fault (.invalidPC s.pc) := by
  simp [Dispatch, fetch]

theorem dispatch_exists (target : Ptx.Target) (program : List Instr) (s : State)
    (eligible : Eligible target) : ∃ outcome, Dispatch target program s outcome := by
  cases fetch : program[s.pc]? with
  | none => exact ⟨.fault (.invalidPC s.pc), by simp [Dispatch, fetch, eligible]⟩
  | some i =>
    cases i with
    | scalar i => exact ⟨_, (dispatch_fetch fetch).2 ⟨eligible, .scalar⟩⟩
    | binary32 i =>
      obtain ⟨next, event, h⟩ := Scalar.Binary32.eval_exists i s
      exact ⟨_, (dispatch_fetch fetch).2 ⟨eligible, .binary32 h⟩⟩

/-- A finite advancing prefix has no implicit exit or fuel interpretation. -/
inductive Path (advance : S → E → S → Prop) : S → List E → S → Prop where
  | nil : Path advance s [] s
  | cons : advance s event next → Path advance next rest final →
      Path advance s (event :: rest) final

def Advances (target : Ptx.Target) (program : List Instr)
    (s : State) (event : Event) (next : State) : Prop :=
  Dispatch target program s (.next next event)

theorem Path.append (first : Path advance s xs middle) (second : Path advance middle ys final) :
    Path advance s (xs ++ ys) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => exact .cons step (ih second)

theorem Path.invariant (property : S → Prop)
    (preserved : ∀ s event next, property s → advance s event next → property next)
    (path : Path advance s trace final) (initial : property s) : property final := by
  induction path with
  | nil => exact initial
  | cons step _ ih => exact ih (preserved _ _ _ initial step)

theorem Path.event_origin (path : Path advance s trace final) (member : event ∈ trace) :
    ∃ before after, advance before event after := by
  induction path with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, _, step⟩
    · exact ih member

/-- A run ends in a real terminal dispatch; there is no exhausted constructor. -/
inductive Run (target : Ptx.Target) (program : List Instr) :
    State → State → Scalar.Stop → List Event → Prop where
  | next : Dispatch target program s (.next next event) →
      Run target program next final status rest →
      Run target program s final status (event :: rest)
  | halted : Dispatch target program s (.halted final event) →
      Run target program s final .halted [event]
  | fault : Dispatch target program s (.fault reason) →
      Run target program s s (.fault reason) []
  | unsupported : Dispatch target program s (.unsupported spelling) →
      Run target program s s (.unsupported spelling) []

theorem Run.not_exhausted (run : Run target program s final status trace) :
    status ≠ .exhausted := by
  induction run <;> simp_all

private theorem scalar_event_origin
    (h : Scalar.eval override i s = .next next event ∨
      Scalar.eval override i s = .halted next event) :
    event.pc = s.pc ∧ event.instruction = i := by
  cases i with
  | mk guard op =>
    cases op <;> cases hg : guard.eval s <;>
      simp only [Scalar.eval, hg, ↓reduceIte] at h
    all_goals first
      | (rcases h with h | h <;> cases h <;> exact ⟨rfl, rfl⟩)
      | (split at h <;> rcases h with h | h <;> cases h <;> exact ⟨rfl, rfl⟩)

theorem scalar_next_iff : Eval (.scalar i) s (.next next event) ↔
    ∃ scalarEvent, Scalar.eval none i s = .next next scalarEvent ∧ event = .scalar scalarEvent := by
  rw [eval_scalar_iff]
  cases h : Scalar.eval none i s <;> simp [liftScalar, eq_comm]

theorem scalar_halted_iff : Eval (.scalar i) s (.halted final event) ↔
    ∃ scalarEvent, Scalar.eval none i s = .halted final scalarEvent ∧ event = .scalar scalarEvent := by
  rw [eval_scalar_iff]
  cases h : Scalar.eval none i s <;> simp [liftScalar, eq_comm]

/-- Event fields are consequences of the fetched step, not an independent label. -/
theorem eval_event_origin (h : Eval i s (.next next event) ∨ Eval i s (.halted next event)) :
    event.pc = s.pc ∧ event.instruction = i := by
  cases i with
  | scalar i =>
    rcases h with h | h
    · obtain ⟨se, hs, rfl⟩ := scalar_next_iff.mp h
      have h := scalar_event_origin (Or.inl hs)
      exact ⟨h.1, congrArg Instr.scalar h.2⟩
    · obtain ⟨se, hs, rfl⟩ := scalar_halted_iff.mp h
      have h := scalar_event_origin (Or.inr hs)
      exact ⟨h.1, congrArg Instr.scalar h.2⟩
  | binary32 i =>
    rcases h with h | h
    · obtain ⟨ns, ev, he, eq⟩ := eval_binary32_iff.mp h
      cases eq
      rw [Scalar.Binary32.eval_event _ _ _ _ he]
      exact ⟨rfl, rfl⟩
    · obtain ⟨ns, ev, he, eq⟩ := eval_binary32_iff.mp h
      cases eq

theorem dispatch_event_origin
    (h : Dispatch target program s (.next next event) ∨
      Dispatch target program s (.halted next event)) :
    event.pc = s.pc ∧ program[s.pc]? = some event.instruction := by
  rcases h with h | h
  all_goals
    rcases h with ⟨_, h⟩
    cases fetch : program[s.pc]? with
    | none => simp [fetch] at h
    | some i =>
      simp only [fetch] at h
      have origin := eval_event_origin (by first | exact Or.inl h | exact Or.inr h)
      exact ⟨origin.1, by simpa only [origin.2] using fetch⟩

theorem eval_next_safe (h : Eval i s (.next next event)) :
    next.memory.length = s.memory.length ∧
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_next_iff.mp h
    exact ⟨Scalar.eval_memory_length hs, fun _ he => Scalar.eval_memory_safe hs he⟩
  | binary32 i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_binary32_iff.mp h
    cases eq
    refine ⟨congrArg List.length (Scalar.Binary32.eval_frame _ _ _ _ he).2.1, ?_⟩
    rw [Scalar.Binary32.eval_event _ _ _ _ he]
    intro effect hm
    cases hm

theorem eval_halted (h : Eval i s (.halted final event)) :
    final = s ∧ event.memory = none := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_halted_iff.mp h
    exact Scalar.eval_halted hs
  | binary32 i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_binary32_iff.mp h
    cases eq

theorem dispatch_next_safe (h : Dispatch target program s (.next next event)) :
    next.memory.length = s.memory.length ∧
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address := by
  rcases h with ⟨_, h⟩
  cases fetch : program[s.pc]? with
  | none => simp [fetch] at h
  | some i => exact eval_next_safe (by simpa [fetch] using h)

theorem dispatch_halted (h : Dispatch target program s (.halted final event)) :
    final = s ∧ event.memory = none := by
  rcases h with ⟨_, h⟩
  cases fetch : program[s.pc]? with
  | none => simp [fetch] at h
  | some i => exact eval_halted (by simpa [fetch] using h)

theorem Path.memory_length (path : Path (Advances target program) s trace final) :
    final.memory.length = s.memory.length := by
  induction path with
  | nil => rfl
  | cons step _ ih => exact ih.trans (dispatch_next_safe step).1

theorem Path.memory_safe (path : Path (Advances target program) s trace final)
    (member : event ∈ trace) (memory : event.memory = some effect) :
    ValidAddress s.memory effect.address := by
  induction path with
  | nil => simp at member
  | cons step _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact (dispatch_next_safe step).2 _ memory
    · have safe := ih member
      simpa only [ValidAddress, (dispatch_next_safe step).1] using safe

theorem Run.memory_length (run : Run target program s final status trace) :
    final.memory.length = s.memory.length := by
  induction run with
  | next step _ ih => exact ih.trans (dispatch_next_safe step).1
  | halted step => rw [(dispatch_halted step).1]
  | fault _ | unsupported _ => rfl

theorem Run.memory_safe (run : Run target program s final status trace)
    (member : event ∈ trace) (memory : event.memory = some effect) :
    ValidAddress s.memory effect.address := by
  induction run with
  | next step _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact (dispatch_next_safe step).2 _ memory
    · have safe := ih member
      simpa only [ValidAddress, (dispatch_next_safe step).1] using safe
  | halted step =>
    have := List.mem_singleton.mp member
    subst event
    rw [(dispatch_halted step).2] at memory
    contradiction
  | fault _ | unsupported _ => simp at member

def StoresTo (event : Event) (index : Nat) : Prop :=
  ∃ effect, event.memory = some effect ∧ effect.kind = .store ∧ effect.address.toNat / 4 = index

theorem eval_frame (step : Eval i s (.next next event))
    (untouched : ¬ StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_next_iff.mp step
    exact Scalar.Rules.eval_frame hs untouched
  | binary32 i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_binary32_iff.mp step
    cases eq
    rw [(Scalar.Binary32.eval_frame _ _ _ _ he).2.1]

theorem dispatch_frame (step : Dispatch target program s (.next next event))
    (untouched : ¬ StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  rcases step with ⟨_, h⟩
  cases fetch : program[s.pc]? with
  | none => simp [fetch] at h
  | some i => exact eval_frame (by simpa [fetch] using h) untouched

theorem Path.frame (path : Path (Advances target program) s trace final)
    (untouched : ∀ event ∈ trace, ¬ StoresTo event index) :
    final.memory[index]? = s.memory[index]? := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
    exact (ih (fun e h => untouched e (List.mem_cons_of_mem _ h))).trans
      (dispatch_frame step (untouched _ (by simp)))

theorem Run.frame (run : Run target program s final status trace)
    (untouched : ∀ event ∈ trace, ¬ StoresTo event index) :
    final.memory[index]? = s.memory[index]? := by
  induction run with
  | next step _ ih =>
    exact (ih (fun e h => untouched e (List.mem_cons_of_mem _ h))).trans
      (dispatch_frame step (untouched _ (by simp)))
  | halted step => rw [(dispatch_halted step).1]
  | fault _ | unsupported _ => rfl

theorem Run.unfold : Run target program s final status trace ↔
    (∃ next event rest, Dispatch target program s (.next next event) ∧
      Run target program next final status rest ∧ trace = event :: rest) ∨
    (∃ event, Dispatch target program s (.halted final event) ∧ status = .halted ∧ trace = [event]) ∨
    (∃ reason, Dispatch target program s (.fault reason) ∧ final = s ∧
      status = .fault reason ∧ trace = []) ∨
    (∃ spelling, Dispatch target program s (.unsupported spelling) ∧ final = s ∧
      status = .unsupported spelling ∧ trace = []) := by
  constructor
  · intro run
    cases run with
    | next h tail => exact .inl ⟨_, _, _, h, tail, rfl⟩
    | halted h => exact .inr (.inl ⟨_, h, rfl, rfl⟩)
    | fault h => exact .inr (.inr (.inl ⟨_, h, rfl, rfl, rfl⟩))
    | unsupported h => exact .inr (.inr (.inr ⟨_, h, rfl, rfl, rfl⟩))
  · rintro (⟨next, event, rest, h, tail, rfl⟩ | ⟨event, h, rfl, rfl⟩ |
      ⟨reason, h, rfl, rfl, rfl⟩ | ⟨spelling, h, rfl, rfl, rfl⟩)
    · exact .next h tail
    · exact .halted h
    · exact .fault h
    · exact .unsupported h

theorem Run.scalar_next_iff {s next final : State} (eligible : Eligible target)
    (fetch : program[s.pc]? = some (.scalar i))
    (evaluated : Scalar.eval none i s = .next next event) :
    Run target program s final status trace ↔
      ∃ rest, Run target program next final status rest ∧ trace = Event.scalar event :: rest := by
  rw [Run.unfold]
  simp [Dispatch, fetch, eligible, eval_scalar_iff, evaluated, liftScalar]

theorem Run.scalar_halted_iff (eligible : Eligible target)
    (fetch : program[s.pc]? = some (.scalar i))
    (evaluated : Scalar.eval none i s = .halted s event) :
    Run target program s final status trace ↔
      final = s ∧ status = .halted ∧ trace = [Event.scalar event] := by
  rw [Run.unfold]
  simp [Dispatch, fetch, eligible, eval_scalar_iff, evaluated, liftScalar, eq_comm]

theorem Run.binary32_iff (eligible : Eligible target)
    (fetch : program[s.pc]? = some (.binary32 i)) (enabled : i.guard.eval s = true) :
    Run target program s final status trace ↔
      ∃ value, Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value ∧
      ∃ rest, Run target program
        {s with pc := s.pc + 1, regs := Scalar.update s.regs i.destination value}
        final status rest ∧ trace = Event.binary32 (Scalar.Binary32.occurrence s i true) :: rest := by
  rw [Run.unfold]
  simp only [Dispatch, fetch, eligible, true_and, eval_binary32_iff]
  simp_rw [Scalar.Binary32.eval_true_iff i s _ _ enabled]
  constructor
  · rintro (⟨ns, ev, rest, ⟨ns', ev', ⟨value, hv, rfl, rfl⟩, eq⟩, tail, ht⟩ | h | h | h)
    · cases eq
      exact ⟨value, hv, rest, tail, ht⟩
    all_goals rcases h with ⟨x, ⟨ns, ev, he, eq⟩, _⟩; cases eq
  · rintro ⟨value, hv, rest, tail, ht⟩
    exact .inl ⟨_, _, rest, ⟨_, _, ⟨value, hv, rfl, rfl⟩, rfl⟩, tail, ht⟩

end Ptx.Scalar.Mixed
