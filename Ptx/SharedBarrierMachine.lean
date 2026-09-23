import Ptx.Barrier
import Ptx.Language

/-! A deliberately small fetched instruction machine for one full-CTA barrier.
Only the typed shared-memory forms below are represented. Candidate reads and
concrete arena reads share access/control checks, but are different modes. -/
namespace Ptx.SharedBarrier

structure Config (n : Nat) where
  cta : Nat
  partner : Fin n → Fin n
  nonempty : 0 < n
  noWrap : 4*n < 2^32

inductive Instruction where
  | store (addressRegister sourceRegister : Nat)
  | sync (resource : Fin 16)
  | load (destinationRegister addressRegister : Nat)
  | exit
  deriving DecidableEq, Repr

/-- No predicate, branch, dynamic barrier resource or count is hidden here. -/
def program : List Instruction := [.store 0 0, .sync 0, .load 1 1, .exit]

inductive Token where
  | wordRegister (index : Nat)
  | sharedAddressRegister (index : Nat)
  | resource (value : Fin 16)
  deriving DecidableEq, Repr

def encode : Instruction → String × List Token
  | .store a s => ("st.relaxed.cta.shared.u32", [.sharedAddressRegister a, .wordRegister s])
  | .sync r => ("bar.sync", [.resource r])
  | .load d a => ("ld.relaxed.cta.shared.u32", [.wordRegister d, .sharedAddressRegister a])
  | .exit => ("exit", [])

def decode : String → List Token → Option Instruction
  | "st.relaxed.cta.shared.u32", [.sharedAddressRegister a, .wordRegister s] => some (.store a s)
  | "bar.sync", [.resource r] => some (.sync r)
  | "ld.relaxed.cta.shared.u32", [.wordRegister d, .sharedAddressRegister a] => some (.load d a)
  | "exit", [] => some .exit
  | _, _ => none

theorem decode_encode (instruction : Instruction) :
    decode (encode instruction).1 (encode instruction).2 = some instruction := by
  cases instruction <;> rfl

structure ThreadState where
  pc : Nat
  registers : Nat → Word
  addresses : Nat → Word
  halted : Bool

structure Arena (n : Nat) where
  owner : Nat
  words : Fin n → Word

structure State (n : Nat) where
  threads : Fin n → ThreadState
  arena : Arena n
  barrier : Barrier.State n

/-- Shared addresses are 32-bit byte offsets in this CTA's initialized arena. -/
def AccessSafe (n : Nat) (address : Word) : Prop :=
  address.toNat % 4 = 0 ∧ address.toNat / 4 < n

def accessIndex (n : Nat) (address : Word) : Option (Fin n) :=
  if _aligned : address.toNat % 4 = 0 then
    if bound : address.toNat / 4 < n then some ⟨address.toNat / 4, bound⟩ else none
  else none

theorem accessIndex_some (h : accessIndex n address = some index) :
    AccessSafe n address ∧ index.val = address.toNat / 4 := by
  unfold accessIndex at h
  split at h
  · split at h
    · cases h
      exact ⟨⟨by assumption, by assumption⟩, rfl⟩
    · contradiction
  · contradiction

def update (values : α → β) [DecidableEq α] (index : α) (value : β) : α → β :=
  fun other => if other = index then value else values other

inductive MemoryKind where
  | store | load
  deriving DecidableEq, Repr

/-- The kind selects exactly the explicit relaxed/CTA/shared/u32 instruction.
The owner is retained; a global instruction is never used as its source. -/
structure MemoryEvent (n : Nat) where
  kind : MemoryKind
  cta : Nat
  thread : Fin n
  pc : Nat
  address : Word
  value : Word
  deriving DecidableEq, Repr

inductive Event (n : Nat) where
  | memory (effect : MemoryEvent n)
  | barrier (effect : Barrier.Event n)
  | exited (thread : Fin n) (pc : Nat)
  deriving DecidableEq, Repr

inductive Outcome where
  | advanced | waiting | released | halted
  | wrongOwner | invalidAddress | invalidPC | wrongBarrierKey
  deriving DecidableEq, Repr

structure Result (n : Nat) where
  state : State n
  outcome : Outcome
  events : List (Event n)

def barrierConfig (config : Config n) : Barrier.Config n :=
  ⟨config.cta, 0, 1, config.nonempty⟩

/-- Key site and resource come from the actual fetched instruction/PC. -/
def barrierRequest (config : Config n) (state : State n) (thread : Fin n) (resource : Fin 16) :
    Barrier.Request n :=
  ⟨⟨config.cta, resource, state.barrier.generation, (state.threads thread).pc⟩, thread⟩

def advance (thread : ThreadState) : ThreadState := {thread with pc := thread.pc+1}

/-- The caller's fetch selects this operation. Barriers park at their own PC;
on release all participants advance. Reachability establishes they are all at
that same barrier, rather than assuming it as a release premise. -/
def dispatch (config : Config n) (override : Option Word) (thread : Fin n)
    (instruction : Instruction) (state : State n) : Result n :=
  let current := state.threads thread
  match instruction with
  | .store addressRegister sourceRegister =>
    if state.arena.owner = config.cta then
      match accessIndex n (current.addresses addressRegister) with
      | none => ⟨state, .invalidAddress, []⟩
      | some index =>
        ⟨{state with
            threads := update state.threads thread (advance current)
            arena := {state.arena with words := update state.arena.words index (current.registers sourceRegister)}},
         .advanced,
         [.memory ⟨.store, config.cta, thread, current.pc,
           current.addresses addressRegister, current.registers sourceRegister⟩]⟩
    else ⟨state, .wrongOwner, []⟩
  | .load destinationRegister addressRegister =>
    if state.arena.owner = config.cta then
      match accessIndex n (current.addresses addressRegister) with
      | none => ⟨state, .invalidAddress, []⟩
      | some index =>
        let value := override.getD (state.arena.words index)
        ⟨{state with threads := update state.threads thread {current with pc := current.pc+1, registers := update current.registers destinationRegister value}},
         .advanced,
         [.memory ⟨.load, config.cta, thread, current.pc, current.addresses addressRegister, value⟩]⟩
    else ⟨state, .wrongOwner, []⟩
  | .sync resource =>
    let result := Barrier.step (barrierConfig config) state.barrier (barrierRequest config state thread resource)
    match result.disposition with
    | .rejectedWrongKey => ⟨state, .wrongBarrierKey, []⟩
    | .waiting =>
      ⟨{state with barrier := result.state}, .waiting, result.events.map Event.barrier⟩
    | .released =>
      ⟨{state with threads := fun other => advance (state.threads other), barrier := result.state},
        .released, result.events.map Event.barrier⟩
  | .exit =>
    ⟨{state with threads := update state.threads thread {current with halted := true}},
      .halted, [.exited thread current.pc]⟩

instance (state : Barrier.State n) (thread : Fin n) : Decidable (Barrier.Waiting state thread) :=
  inferInstanceAs (Decidable (state.arrived thread = true))

/-- Waiting and halted threads cannot fetch a later instruction. -/
def stepWith (config : Config n) (override : Option Word) (thread : Fin n) (state : State n) : Result n :=
  if (state.threads thread).halted = true then ⟨state, .halted, []⟩
  else if Barrier.Waiting state.barrier thread then ⟨state, .waiting, []⟩
  else match program[(state.threads thread).pc]? with
    | none => ⟨state, .invalidPC, []⟩
    | some instruction => dispatch config override thread instruction state

def step (config : Config n) (thread : Fin n) (state : State n) : Result n :=
  stepWith config none thread state

theorem waiting_blocks (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (live : (state.threads thread).halted = false) (waiting : Barrier.Waiting state.barrier thread) :
    stepWith config override thread state = ⟨state, .waiting, []⟩ := by
  simp [stepWith, live, waiting]

theorem halted_blocks (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (halted : (state.threads thread).halted = true) :
    stepWith config override thread state = ⟨state, .halted, []⟩ := by
  simp [stepWith, halted]

theorem fetched_step (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (live : (state.threads thread).halted = false) (runnable : ¬Barrier.Waiting state.barrier thread)
    (fetch : program[(state.threads thread).pc]? = some instruction) :
    stepWith config override thread state = dispatch config override thread instruction state := by
  simp [stepWith, live, runnable, fetch]

/-- Every emitted effect comes from an actually fetched instruction at a live,
unblocked thread. The individual dispatch branches determine its full fields. -/
theorem event_origin (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (member : event ∈ (stepWith config override thread state).events) :
    ∃ instruction, (state.threads thread).halted = false ∧
      ¬Barrier.Waiting state.barrier thread ∧
      program[(state.threads thread).pc]? = some instruction ∧
      event ∈ (dispatch config override thread instruction state).events := by
  unfold stepWith at member
  split at member
  · simp at member
  · rename_i live
    split at member
    · simp at member
    · rename_i runnable
      split at member
      · simp at member
      · rename_i instruction fetch
        exact ⟨instruction, by simpa using live, runnable, fetch, member⟩

/-- No dispatch event is discarded by the outer fetched-step wrapper. -/
theorem event_complete (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (live : (state.threads thread).halted = false) (runnable : ¬Barrier.Waiting state.barrier thread)
    (fetch : program[(state.threads thread).pc]? = some instruction)
    (member : event ∈ (dispatch config override thread instruction state).events) :
    event ∈ (stepWith config override thread state).events := by
  rw [fetched_step config override thread state live runnable fetch]
  exact member

/-- Emitted shared accesses always passed ownership, alignment and full-word bounds. -/
theorem dispatch_memory_safe (config : Config n) (override : Option Word) (thread : Fin n)
    (instruction : Instruction) (state : State n) (effect : MemoryEvent n)
    (member : Event.memory effect ∈ (dispatch config override thread instruction state).events) :
    state.arena.owner = config.cta ∧ AccessSafe n effect.address ∧ effect.cta = config.cta ∧
      effect.thread = thread ∧ effect.pc = (state.threads thread).pc := by
  cases instruction with
  | store a s =>
    simp only [dispatch] at member
    split at member
    · rename_i owner
      split at member
      · simp at member
      · rename_i index indexed
        simp only [List.mem_singleton, Event.memory.injEq] at member
        subst effect
        exact ⟨owner, (accessIndex_some indexed).1, rfl, rfl, rfl⟩
    · simp at member
  | load d a =>
    simp only [dispatch] at member
    split at member
    · rename_i owner
      split at member
      · simp at member
      · rename_i index indexed
        simp only [List.mem_singleton, Event.memory.injEq] at member
        subst effect
        exact ⟨owner, (accessIndex_some indexed).1, rfl, rfl, rfl⟩
    · simp at member
  | sync resource =>
    simp only [dispatch] at member
    split at member <;> simp at member
  | exit => simp [dispatch] at member

theorem memory_safe (config : Config n) (override : Option Word) (thread : Fin n) (state : State n)
    (effect : MemoryEvent n) (member : Event.memory effect ∈ (stepWith config override thread state).events) :
    state.arena.owner = config.cta ∧ AccessSafe n effect.address ∧ effect.cta = config.cta ∧
      effect.thread = thread ∧ effect.pc = (state.threads thread).pc := by
  obtain ⟨instruction, _, _, _, source⟩ := event_origin _ _ _ _ member
  exact dispatch_memory_safe _ _ _ _ _ _ source

structure Execution (n : Nat) where
  state : State n
  trace : List (Event n)

def runWith (config : Config n) (reads : Fin n → Option Word) :
    State n → List (Fin n) → Execution n
  | state, [] => ⟨state, []⟩
  | state, thread :: rest =>
    let first := stepWith config (reads thread) thread state
    let remaining := runWith config reads first.state rest
    ⟨remaining.state, first.events ++ remaining.trace⟩

def run (config : Config n) : State n → List (Fin n) → Execution n :=
  runWith config (fun _ => none)

inductive Runs (config : Config n) (reads : Fin n → Option Word) :
    State n → List (Fin n) → Execution n → Prop where
  | nil : Runs config reads state [] ⟨state, []⟩
  | cons : Runs config reads (stepWith config (reads thread) thread state).state rest remaining →
      Runs config reads state (thread :: rest)
        ⟨remaining.state, (stepWith config (reads thread) thread state).events ++ remaining.trace⟩

theorem runWith_sound (config : Config n) (reads : Fin n → Option Word)
    (state : State n) (schedule : List (Fin n)) :
    Runs config reads state schedule (runWith config reads state schedule) := by
  induction schedule generalizing state with
  | nil => exact .nil
  | cons thread rest ih => exact .cons (ih _)

theorem runWith_append (config : Config n) (reads : Fin n → Option Word)
    (state : State n) (first second : List (Fin n)) :
    runWith config reads state (first ++ second) =
      let left := runWith config reads state first
      let right := runWith config reads left.state second
      ⟨right.state, left.trace ++ right.trace⟩ := by
  induction first generalizing state with
  | nil => simp [runWith]
  | cons thread rest ih => simp [runWith, ih, List.append_assoc]

end Ptx.SharedBarrier
