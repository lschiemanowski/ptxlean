import Ptx.Pure32
import Ptx.ExecutionPath

/-! Single-thread arena execution with a catalog of independently specified pure
families. Unsupported targets are explicit boundary outcomes, not PTX results. -/
namespace Ptx.Scalar.PureKernel

structure Catalog (Kind : Type) where
  Operation : Kind → Type
  family : (kind : Kind) → Pure32.Family (Operation kind)

inductive Instr (catalog : Catalog Kind) where
  | scalar (instruction : Scalar.Instr)
  | pure (kind : Kind) (instruction : Pure32.Instr (catalog.family kind))

inductive Event (catalog : Catalog Kind) where
  | scalar (event : Scalar.Occurrence)
  | pure (kind : Kind) (event : Pure32.Occurrence (catalog.family kind))

variable {Kind : Type} {catalog : Catalog Kind}

def Event.memory : Event catalog → Option MemoryEffect
  | .scalar e => e.memory
  | .pure _ e => e.memory

def Event.pc : Event catalog → Nat
  | .scalar e => e.pc
  | .pure _ e => e.pc

def Event.instruction : Event catalog → Instr catalog
  | .scalar e => .scalar e.instruction
  | .pure k e => .pure k e.instruction

inductive Outcome (catalog : Catalog Kind) where
  | next (state : State) (event : Event catalog)
  | halted (state : State) (event : Event catalog)
  | fault (reason : Scalar.Fault)
  | unsupported (spelling : String)

def liftScalar : Scalar.StepResult → Outcome catalog
  | .next s e => .next s (.scalar e)
  | .halted s e => .halted s (.scalar e)
  | .fault reason => .fault reason
  | .unsupported spelling => .unsupported spelling

inductive Eval : Instr catalog → State → Outcome catalog → Prop
  | scalar : Eval (.scalar i) s (liftScalar (Scalar.eval none i s))
  | pure {kind : Kind} {i : Pure32.Instr (catalog.family kind)}
      {event : Pure32.Occurrence (catalog.family kind)} : Pure32.Eval i s next event →
      Eval (.pure kind i) s (.next next (.pure kind event))

def Eligible (target : Ptx.Target) : Prop := target.isa = 94 ∧ 70 ≤ target.sm

def Instr.Supported (target : Ptx.Target) : Instr catalog → Prop
  | .scalar _ => True
  | .pure kind i => (catalog.family kind).Supported target i.operation

noncomputable def Dispatch (target : Ptx.Target) (program : List (Instr catalog))
    (s : State) (outcome : Outcome catalog) : Prop := by
  classical
  exact if Eligible target then
    match program[s.pc]? with
    | none => outcome = .fault (.invalidPC s.pc)
    | some i => if i.Supported target then Eval i s outcome
        else outcome = .unsupported "pure family target"
    else outcome = .unsupported "kernel target"

theorem eval_scalar_iff : Eval (.scalar i : Instr catalog) s outcome ↔
    outcome = liftScalar (Scalar.eval none i s) := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .scalar

theorem eval_pure_iff : Eval (.pure kind i : Instr catalog) s outcome ↔
    ∃ next event, Pure32.Eval i s next event ∧ outcome = .next next (.pure kind event) := by
  constructor
  · intro h; cases h with | pure h => exact ⟨_,_,h,rfl⟩
  · rintro ⟨_,_,h,rfl⟩; exact .pure h

theorem dispatch_fetch (eligible : Eligible target)
    (fetch : program[s.pc]? = some i) (supported : i.Supported target) :
    Dispatch target program s outcome ↔ Eval i s outcome := by
  classical
  simp [Dispatch, eligible, fetch, supported]

theorem dispatch_unsupported (fetch : program[s.pc]? = some i)
    (unsupported : ¬ i.Supported target) (eligible : Eligible target) :
    Dispatch target program s outcome ↔ outcome = .unsupported "pure family target" := by
  classical
  simp [Dispatch, eligible, fetch, unsupported]

theorem dispatch_ineligible (unsupported : ¬ Eligible target) :
    Dispatch target program s outcome ↔ outcome = .unsupported "kernel target" := by
  classical
  simp [Dispatch, unsupported]

theorem dispatch_exists (target : Ptx.Target) (program : List (Instr catalog)) (s : State) :
    ∃ outcome, Dispatch target program s outcome := by
  classical
  by_cases ht : Eligible target
  · cases fetch : program[s.pc]? with
    | none => exact ⟨.fault (.invalidPC s.pc), by simp [Dispatch, ht, fetch]⟩
    | some i =>
      by_cases hi : i.Supported target
      · cases i with
        | scalar i => exact ⟨_, (dispatch_fetch ht fetch hi).mpr .scalar⟩
        | pure k i =>
          obtain ⟨next,event,he⟩ := Pure32.eval_exists i s
          exact ⟨_, (dispatch_fetch ht fetch hi).mpr (.pure he)⟩
      · exact ⟨.unsupported "pure family target", by simp [Dispatch, ht, fetch, hi]⟩
  · exact ⟨.unsupported "kernel target", by simp [Dispatch, ht]⟩

theorem dispatch_success_eval
    (step : Dispatch target program s outcome)
    (success : (∃ next event, outcome = .next next event) ∨
      (∃ next event, outcome = .halted next event)) :
    ∃ i, program[s.pc]? = some i ∧ Eligible target ∧ i.Supported target ∧ Eval i s outcome := by
  classical
  unfold Dispatch at step
  split at step
  · rename_i eligible
    cases fetch : program[s.pc]? with
    | none =>
      simp only [fetch] at step
      rcases success with ⟨_,_,hs⟩ | ⟨_,_,hs⟩ <;> simp_all
    | some i =>
      simp only [fetch] at step
      split at step
      · exact ⟨i,rfl,eligible,by assumption,step⟩
      · rcases success with ⟨_,_,hs⟩ | ⟨_,_,hs⟩ <;> simp_all
  · rcases success with ⟨_,_,hs⟩ | ⟨_,_,hs⟩ <;> simp_all

abbrev Path := @Mixed.Path

def Advances (target : Ptx.Target) (program : List (Instr catalog))
    (s : State) (event : Event catalog) (next : State) : Prop :=
  Dispatch target program s (.next next event)

/-- A run ends in a real terminal dispatch; there is no exhausted constructor. -/
inductive Run (target : Ptx.Target) (program : List (Instr catalog)) :
    State → State → Scalar.Stop → List (Event catalog) → Prop where
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
  cases h : Scalar.eval none i s <;> simp [liftScalar, eq_comm] <;> grind

theorem scalar_halted_iff : Eval (.scalar i) s (.halted final event) ↔
    ∃ scalarEvent, Scalar.eval none i s = .halted final scalarEvent ∧ event = .scalar scalarEvent := by
  rw [eval_scalar_iff]
  cases h : Scalar.eval none i s <;> simp [liftScalar, eq_comm] <;> grind

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
  | pure kind i =>
    rcases h with h | h
    · obtain ⟨ns, ev, he, eq⟩ := eval_pure_iff.mp h
      cases eq
      rw [Pure32.eval_event he]
      exact ⟨rfl, rfl⟩
    · obtain ⟨ns, ev, he, eq⟩ := eval_pure_iff.mp h
      cases eq

theorem dispatch_event_origin
    (h : Dispatch target program s (.next next event) ∨
      Dispatch target program s (.halted next event)) :
    event.pc = s.pc ∧ program[s.pc]? = some event.instruction := by
  rcases h with h | h
  · obtain ⟨i,fetch,_,_,he⟩ := dispatch_success_eval h (.inl ⟨_,_,rfl⟩)
    have origin := eval_event_origin (Or.inl he)
    exact ⟨origin.1, by simpa [origin.2] using fetch⟩
  · obtain ⟨i,fetch,_,_,he⟩ := dispatch_success_eval h (.inr ⟨_,_,rfl⟩)
    have origin := eval_event_origin (Or.inr he)
    exact ⟨origin.1, by simpa [origin.2] using fetch⟩

theorem eval_next_safe (h : Eval i s (.next next event)) :
    next.memory.length = s.memory.length ∧
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_next_iff.mp h
    exact ⟨Scalar.eval_memory_length hs, fun _ he => Scalar.eval_memory_safe hs he⟩
  | pure kind i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_pure_iff.mp h
    cases eq
    refine ⟨congrArg List.length (Pure32.eval_frame he).2.1, ?_⟩
    rw [Pure32.eval_event he]
    intro effect hm
    cases hm

theorem eval_halted (h : Eval i s (.halted final event)) :
    final = s ∧ event.memory = none := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_halted_iff.mp h
    exact Scalar.eval_halted hs
  | pure kind i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_pure_iff.mp h
    cases eq

theorem dispatch_next_safe (h : Dispatch target program s (.next next event)) :
    next.memory.length = s.memory.length ∧
      ∀ effect, event.memory = some effect → ValidAddress s.memory effect.address := by
  obtain ⟨i,_,_,_,he⟩ := dispatch_success_eval h (.inl ⟨_,_,rfl⟩)
  exact eval_next_safe he

theorem dispatch_halted (h : Dispatch target program s (.halted final event)) :
    final = s ∧ event.memory = none := by
  obtain ⟨i,_,_,_,he⟩ := dispatch_success_eval h (.inr ⟨_,_,rfl⟩)
  exact eval_halted he

theorem path_memory_length (path : Path (Advances target program) s trace final) :
    final.memory.length = s.memory.length := by
  induction path with
  | nil => rfl
  | cons step _ ih => exact ih.trans (dispatch_next_safe step).1

theorem path_memory_safe (path : Path (Advances target program) s trace final)
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

def StoresTo (event : Event catalog) (index : Nat) : Prop :=
  ∃ effect, event.memory = some effect ∧ effect.kind = .store ∧ effect.address.toNat / 4 = index

theorem eval_frame (step : Eval i s (.next next event))
    (untouched : ¬ StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  cases i with
  | scalar i =>
    obtain ⟨se, hs, rfl⟩ := scalar_next_iff.mp step
    exact Scalar.Rules.eval_frame hs untouched
  | pure kind i =>
    obtain ⟨ns, ev, he, eq⟩ := eval_pure_iff.mp step
    cases eq
    rw [(Pure32.eval_frame he).2.1]

theorem dispatch_frame (step : Dispatch target program s (.next next event))
    (untouched : ¬ StoresTo event index) : next.memory[index]? = s.memory[index]? := by
  obtain ⟨i,_,_,_,he⟩ := dispatch_success_eval step (.inl ⟨_,_,rfl⟩)
  exact eval_frame he untouched

theorem path_frame (path : Path (Advances target program) s trace final)
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


theorem eval_pure_next_iff :
    Eval (.pure kind i : Instr catalog) s (.next next (.pure kind event)) ↔
      Pure32.Eval i s next event := by
  constructor
  · intro h; cases h with | pure h => exact h
  · exact Eval.pure

theorem dispatch_pure_iff (eligible : Eligible target)
    (fetch : program[s.pc]? = some (.pure kind i : Instr catalog)) :
    Dispatch target program s (.next next (.pure kind event)) ↔
      (catalog.family kind).Supported target i.operation ∧ Pure32.Eval i s next event := by
  classical
  by_cases h : (catalog.family kind).Supported target i.operation
  · simp [Dispatch, eligible, fetch, Instr.Supported, h, eval_pure_next_iff]
  · simp [Dispatch, eligible, fetch, Instr.Supported, h]

theorem dispatch_preserves_choices (eligible : Eligible target)
    (fetch : program[s.pc]? = some (.pure kind i : Instr catalog))
    (supported : (catalog.family kind).Supported target i.operation)
    (enabled : i.guard.eval s = true)
    (left : (catalog.family kind).Results i.operation (i.wordValues s) (i.predicateValues s) a)
    (right : (catalog.family kind).Results i.operation (i.wordValues s) (i.predicateValues s) b)
    (different : a ≠ b) :
    Dispatch target program s (.next (Pure32.write s i.destination a) (.pure kind (Pure32.occurrence s i true))) ∧
    Dispatch target program s (.next (Pure32.write s i.destination b) (.pure kind (Pure32.occurrence s i true))) ∧
    Pure32.write s i.destination a ≠ Pure32.write s i.destination b := by
  obtain ⟨ha,hb,ne⟩ := Pure32.eval_preserves_choices enabled left right different
  exact ⟨(dispatch_pure_iff eligible fetch).mpr ⟨supported,ha⟩,
    (dispatch_pure_iff eligible fetch).mpr ⟨supported,hb⟩, ne⟩

def Functional (catalog : Catalog Kind) : Prop :=
  ∀ kind op words predicates a b,
    (catalog.family kind).Results op words predicates a →
    (catalog.family kind).Results op words predicates b → a = b

theorem eval_deterministic (functional : Functional catalog) {i : Instr catalog}
    (left : Eval i s a) (right : Eval i s b) : a = b := by
  cases left with
  | scalar => cases right; rfl
  | @pure s next kind i event ha =>
    cases right with
    | pure hb =>
      obtain ⟨rfl,rfl⟩ := Pure32.eval_deterministic (family := catalog.family kind) (i := i) (functional kind i.operation) ha hb
      rfl

theorem dispatch_deterministic (functional : Functional catalog) {program : List (Instr catalog)}
    (left : Dispatch target program s a) (right : Dispatch target program s b) : a = b := by
  classical
  unfold Dispatch at left right
  split at left <;> simp_all only [↓reduceIte]
  · cases fetch : program[s.pc]? with
    | none => simp_all
    | some i =>
      simp only [fetch] at left right
      split at left
      · simp_all only [↓reduceIte]
        exact eval_deterministic functional left right
      · simp_all

theorem Run.deterministic (functional : Functional catalog) {program : List (Instr catalog)}
    (left : Run target program s final status trace)
    (right : Run target program s final₂ status₂ trace₂) :
    final = final₂ ∧ status = status₂ ∧ trace = trace₂ := by
  induction left generalizing final₂ status₂ trace₂ with
  | next step tail ih =>
    cases right with
    | next other rest =>
      have eq := dispatch_deterministic functional step other
      cases eq
      obtain ⟨rfl,rfl,rfl⟩ := ih rest
      exact ⟨rfl,rfl,rfl⟩
    | halted other | fault other | unsupported other =>
      have eq := dispatch_deterministic functional step other
      cases eq
  | halted step =>
    cases right with
    | next other rest | fault other | unsupported other =>
      have eq := dispatch_deterministic functional step other
      cases eq
    | halted other =>
      have eq := dispatch_deterministic functional step other
      cases eq
      exact ⟨rfl,rfl,rfl⟩
  | fault step =>
    cases right with
    | next other rest | halted other | unsupported other =>
      have eq := dispatch_deterministic functional step other
      cases eq
    | fault other =>
      have eq := dispatch_deterministic functional step other
      cases eq
      exact ⟨rfl,rfl,rfl⟩
  | unsupported step =>
    cases right with
    | next other rest | halted other | fault other =>
      have eq := dispatch_deterministic functional step other
      cases eq
    | unsupported other =>
      have eq := dispatch_deterministic functional step other
      cases eq
      exact ⟨rfl,rfl,rfl⟩

end Ptx.Scalar.PureKernel
