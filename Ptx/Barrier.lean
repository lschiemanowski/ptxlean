import Std

/-!
Full-CTA, no-exit barrier control protocol. Requests identify a common instruction
site, but this module does not fetch PTX instructions or prove that threads reach
that site. It provides no memory visibility or scheduler fairness semantics.
-/
namespace Ptx.Barrier

structure Key where
  cta : Nat
  resource : Fin 16
  generation : Nat
  site : Nat
  deriving DecidableEq, Repr

structure Config (n : Nat) where
  cta : Nat
  resource : Fin 16
  site : Nat
  nonempty : 0 < n

structure State (n : Nat) where
  generation : Nat
  arrived : Fin n → Bool

def reset (generation : Nat) : State n := ⟨generation, fun _ => false⟩
def initial : State n := reset 0

def key (config : Config n) (state : State n) : Key :=
  ⟨config.cta, config.resource, state.generation, config.site⟩

structure Request (n : Nat) where
  key : Key
  thread : Fin n
  deriving DecidableEq, Repr

inductive Event (n : Nat) where
  | arrival (key : Key) (thread : Fin n)
  | completion (key : Key)
  deriving DecidableEq, Repr

inductive Disposition where
  | waiting
  | released
  | rejectedWrongKey
  deriving DecidableEq, Repr

structure Result (n : Nat) where
  state : State n
  disposition : Disposition
  events : List (Event n)

/-- A set arrival bit is the protocol's waiting state. No separate runnable bit
can disagree with it. A future fetched-instruction layer must obey this block. -/
def Waiting (state : State n) (thread : Fin n) : Prop := state.arrived thread = true

def Runnable (state : State n) (thread : Fin n) : Prop := state.arrived thread = false

def Complete (state : State n) : Prop := ∀ thread, Waiting state thread

instance (state : State n) : Decidable (Complete state) := by
  unfold Complete Waiting
  infer_instance

def mark (state : State n) (thread : Fin n) : State n :=
  ⟨state.generation, fun other => if other = thread then true else state.arrived other⟩

/-- The completing arrival and the distinct completion event share one exact
key. Reuse is atomic at this protocol boundary: all waiting bits are cleared. -/
def step (config : Config n) (state : State n) (request : Request n) : Result n :=
  if request.key = key config state then
    if state.arrived request.thread = true then ⟨state, .waiting, []⟩
    else
      let next := mark state request.thread
      if Complete next then
        ⟨reset (state.generation + 1), .released,
          [.arrival request.key request.thread, .completion request.key]⟩
      else ⟨next, .waiting, [.arrival request.key request.thread]⟩
  else ⟨state, .rejectedWrongKey, []⟩

/-- Stable states never retain a completed generation: the last arrival resets it. -/
def Invariant (state : State n) : Prop := ¬Complete state

theorem reset_invariant (config : Config n) (generation : Nat) : Invariant (reset generation : State n) := by
  intro complete
  have h := complete ⟨0, config.nonempty⟩
  simp [Waiting, reset] at h

theorem initial_invariant (config : Config n) : Invariant (initial : State n) :=
  reset_invariant config 0

theorem mark_waiting (state : State n) (thread : Fin n) : Waiting (mark state thread) thread := by
  simp [Waiting, mark]

theorem mark_other (state : State n) (thread other : Fin n) (different : other ≠ thread) :
    (mark state thread).arrived other = state.arrived other := by simp [mark, different]

theorem mark_monotone (state : State n) (thread other : Fin n) (waiting : Waiting state other) :
    Waiting (mark state thread) other := by
  change state.arrived other = true at waiting
  by_cases h : other = thread <;> simp [Waiting, mark, h, waiting]

theorem missing_prevents_completion (state : State n) (thread : Fin n)
    (missing : Runnable state thread) : ¬Complete state := by
  intro complete
  change state.arrived thread = false at missing
  have h := complete thread
  simp [Waiting, missing] at h

theorem wrong_key_unchanged (config : Config n) (state : State n) (request : Request n)
    (wrong : request.key ≠ key config state) :
    step config state request = ⟨state, .rejectedWrongKey, []⟩ := by simp [step, wrong]

theorem old_generation_unchanged (config : Config n) (state : State n) (request : Request n)
    (old : request.key.generation < state.generation) :
    step config state request = ⟨state, .rejectedWrongKey, []⟩ := by
  apply wrong_key_unchanged
  intro same
  have equal := congrArg Key.generation same
  simp [key] at equal
  omega

theorem other_cta_unchanged (config : Config n) (state : State n) (request : Request n)
    (other : request.key.cta ≠ config.cta) :
    step config state request = ⟨state, .rejectedWrongKey, []⟩ := by
  apply wrong_key_unchanged
  intro same
  exact other (congrArg Key.cta same)

theorem duplicate_wait_unchanged (config : Config n) (state : State n) (request : Request n)
    (same : request.key = key config state) (waiting : Waiting state request.thread) :
    step config state request = ⟨state, .waiting, []⟩ := by
  change state.arrived request.thread = true at waiting
  simp [step, same, waiting]

theorem completing_step (config : Config n) (state : State n) (request : Request n)
    (same : request.key = key config state) (fresh : Runnable state request.thread)
    (complete : Complete (mark state request.thread)) :
    step config state request =
      ⟨reset (state.generation + 1), .released,
        [.arrival request.key request.thread, .completion request.key]⟩ := by
  change state.arrived request.thread = false at fresh
  simp [step, same, fresh, complete]

theorem waiting_step (config : Config n) (state : State n) (request : Request n)
    (same : request.key = key config state) (fresh : Runnable state request.thread)
    (incomplete : ¬Complete (mark state request.thread)) :
    step config state request =
      ⟨mark state request.thread, .waiting, [.arrival request.key request.thread]⟩ := by
  change state.arrived request.thread = false at fresh
  simp [step, same, fresh, incomplete]

theorem released_iff (config : Config n) (state : State n) (request : Request n) :
    (step config state request).disposition = .released ↔
      request.key = key config state ∧ Runnable state request.thread ∧
      Complete (mark state request.thread) := by
  cases h : state.arrived request.thread <;>
    by_cases hk : request.key = key config state <;>
    by_cases hc : Complete (mark state request.thread) <;>
    simp [step, hk, hc, Runnable, h]

theorem missing_other_blocks_release (config : Config n) (state : State n)
    (request : Request n) (other : Fin n) (different : other ≠ request.thread)
    (missing : Runnable state other) : (step config state request).disposition ≠ .released := by
  intro released
  have complete := ((released_iff _ _ _).mp released).2.2
  have waiting := complete other
  change state.arrived other = false at missing
  simp [Waiting, mark, different, missing] at waiting

theorem release_resets (config : Config n) (state : State n) (request : Request n)
    (released : (step config state request).disposition = .released) :
    (step config state request).state = reset (state.generation + 1) := by
  obtain ⟨same, fresh, complete⟩ := (released_iff _ _ _).mp released
  rw [completing_step config state request same fresh complete]

theorem release_all_runnable (config : Config n) (state : State n) (request : Request n)
    (released : (step config state request).disposition = .released) (thread : Fin n) :
    Runnable (step config state request).state thread := by
  rw [release_resets _ _ _ released]
  rfl

theorem step_invariant (config : Config n) (state : State n) (request : Request n)
    (invariant : Invariant state) : Invariant (step config state request).state := by
  by_cases hk : request.key = key config state
  · by_cases hw : state.arrived request.thread = true
    · simpa [step, hk, hw] using invariant
    · by_cases hc : Complete (mark state request.thread)
      · simpa [step, hk, hw, hc] using reset_invariant config (state.generation+1)
      · simp [step, hk, hw, hc, Invariant]
  · simpa [step, hk] using invariant

theorem arrival_monotone_in_generation (config : Config n) (state : State n) (request : Request n)
    (sameGeneration : (step config state request).state.generation = state.generation)
    (thread : Fin n) (waiting : Waiting state thread) :
    Waiting (step config state request).state thread := by
  by_cases hk : request.key = key config state
  · by_cases hw : state.arrived request.thread = true
    · simpa [step, hk, hw] using waiting
    · by_cases hc : Complete (mark state request.thread)
      · simp [step, hk, hw, hc, reset] at sameGeneration
      · simpa [step, hk, hw, hc] using mark_monotone state request.thread thread waiting
  · simpa [step, hk] using waiting

/-- An emitted arrival certifies a fresh participant at the currently active key.
This is protocol provenance, not evidence that a PTX instruction was fetched. -/
theorem arrival_event_iff (config : Config n) (state : State n) (request : Request n)
    (observed : Key) (thread : Fin n) :
    Event.arrival observed thread ∈ (step config state request).events ↔
      request.key = key config state ∧ Runnable state request.thread ∧
      observed = request.key ∧ thread = request.thread := by
  cases h : state.arrived request.thread <;>
    by_cases hk : request.key = key config state <;>
    by_cases hc : Complete (mark state request.thread) <;>
    simp [step, hk, hc, Runnable, h]

/-- Completion is emitted only by the transition that fills the final arrival,
and keeps its old phase key while the new state has already reset for reuse. -/
theorem completion_event_iff (config : Config n) (state : State n) (request : Request n)
    (observed : Key) :
    Event.completion observed ∈ (step config state request).events ↔
      request.key = key config state ∧ Runnable state request.thread ∧
      Complete (mark state request.thread) ∧ observed = request.key := by
  cases h : state.arrived request.thread <;>
    by_cases hk : request.key = key config state <;>
    by_cases hc : Complete (mark state request.thread) <;>
    simp [step, hk, hc, Runnable, h]

/-- Each thread belongs to exactly one represented warp by this map; surjectivity
excludes fictitious empty warps. Physical placement must be supplied separately. -/
structure WarpPartition (n w : Nat) where
  warpOf : Fin n → Fin w
  inhabited : ∀ warp, ∃ thread, warpOf thread = warp

def WarpComplete (partition : WarpPartition n w) (state : State n) (warp : Fin w) : Prop :=
  ∀ thread, partition.warpOf thread = warp → Waiting state thread

theorem complete_iff_all_warps (partition : WarpPartition n w) (state : State n) :
    Complete state ↔ ∀ warp, WarpComplete partition state warp := by
  constructor
  · intro complete warp thread _
    exact complete thread
  · intro complete thread
    exact complete (partition.warpOf thread) thread rfl

/-- Pure finite protocol execution records every request, including rejected and
repeated requests. The eventual instruction layer must enforce its dispatch rules. -/
inductive Runs (config : Config n) : State n → List (Request n) → State n → Prop where
  | nil : Runs config state [] state
  | cons : Runs config (step config state request).state rest final →
      Runs config state (request :: rest) final

def run (config : Config n) : State n → List (Request n) → State n
  | state, [] => state
  | state, request :: rest => run config (step config state request).state rest

theorem run_sound (config : Config n) (state : State n) (requests : List (Request n)) :
    Runs config state requests (run config state requests) := by
  induction requests generalizing state with
  | nil => exact .nil
  | cons request rest ih => exact .cons (ih _)

theorem runs_eq_run (execution : Runs config state requests final) :
    run config state requests = final := by
  induction execution with
  | nil => rfl
  | cons _ ih => exact ih

theorem runs_append (first : Runs config state left middle) (second : Runs config middle right final) :
    Runs config state (left ++ right) final := by
  induction first with
  | nil => exact second
  | cons _ ih => exact .cons (ih second)

def Reachable (config : Config n) (state : State n) : Prop :=
  ∃ requests, Runs config initial requests state

theorem runs_invariant (execution : Runs config state requests final) (invariant : Invariant state) :
    Invariant final := by
  induction execution with
  | nil => exact invariant
  | cons _ ih => exact ih (step_invariant _ _ _ invariant)

theorem reachable_invariant (config : Config n) (state : State n) (reachable : Reachable config state) :
    Invariant state := by
  obtain ⟨requests, execution⟩ := reachable
  exact runs_invariant execution (initial_invariant config)

/-- An explicit prefixState schedule visits participant indices in increasing order. -/
def prefixState (generation count : Nat) : State n :=
  ⟨generation, fun thread => decide (thread.val < count)⟩

theorem prefix_zero (generation : Nat) : (prefixState generation 0 : State n) = reset generation := by
  rfl

theorem mark_prefix (generation count : Nat) (bound : count < n) :
    mark (prefixState generation count) ⟨count, bound⟩ = (prefixState generation (count+1) : State n) := by
  unfold mark prefixState
  congr 1
  funext thread
  by_cases same : thread = ⟨count, bound⟩
  · subst thread; simp
  · have different : thread.val ≠ count := by intro h; exact same (Fin.ext h)
    simp [same]
    congr 1
    omega

theorem complete_prefix_iff (_config : Config n) (generation count : Nat) :
    Complete (prefixState generation count : State n) ↔ n ≤ count := by
  constructor
  · intro complete
    by_cases enough : n ≤ count
    · exact enough
    · have bound : count < n := by omega
      have h := complete ⟨count, bound⟩
      simp [Waiting, prefixState] at h
  · intro bound thread
    simp [Waiting, prefixState]
    omega

/-- One new arrival advances the increasing-index schedule; its final arrival
releases and resets. The old generation key is used throughout this schedule. -/
theorem prefix_step (config : Config n) (generation count : Nat) (bound : count < n) :
    (step config (prefixState generation count)
      ⟨⟨config.cta, config.resource, generation, config.site⟩, ⟨count,bound⟩⟩).state =
      if count+1 = n then reset (generation+1) else prefixState generation (count+1) := by
  let request : Request n := ⟨⟨config.cta, config.resource, generation, config.site⟩, ⟨count,bound⟩⟩
  have same : request.key = key config (prefixState generation count) := rfl
  have fresh : Runnable (prefixState generation count) request.thread := by
    simp [Runnable, prefixState, request]
  have marked : mark (prefixState generation count) request.thread = prefixState generation (count+1) :=
    mark_prefix generation count bound
  by_cases last : count+1 = n
  · have complete : Complete (mark (prefixState generation count) request.thread) := by
      rw [marked, complete_prefix_iff config]
      omega
    have transition := completing_step config (prefixState generation count) request same fresh complete
    simpa [last, prefixState] using congrArg Result.state transition
  · have incomplete : ¬Complete (mark (prefixState generation count) request.thread) := by
      rw [marked, complete_prefix_iff config]
      omega
    have transition := waiting_step config (prefixState generation count) request same fresh incomplete
    simpa [last, marked] using congrArg Result.state transition

/-- A concrete finite request sequence completes a round. Its existence is
independent of any promise that an external scheduler will choose that sequence. -/
theorem prefix_execution (config : Config n) (generation count : Nat) (bound : count ≤ n) :
    ∃ requests : List (Request n), requests.length = count ∧
      Runs config (reset generation) requests
        (if count = n then reset (generation+1) else prefixState generation count) := by
  induction count with
  | zero =>
    have nonzero : n ≠ 0 := by have := config.nonempty; omega
    exact ⟨[], rfl, by simpa [Ne.symm nonzero, prefix_zero] using (Runs.nil (config := config) (state := reset generation))⟩
  | succ count ih =>
    have below : count < n := by omega
    obtain ⟨requests, length, execution⟩ := ih (by omega)
    have different : count ≠ n := by omega
    simp only [different, ↓reduceIte] at execution
    let request : Request n := ⟨⟨config.cta, config.resource, generation, config.site⟩, ⟨count, below⟩⟩
    have single : Runs config (prefixState generation count) [request]
        (if count+1 = n then reset (generation+1) else prefixState generation (count+1)) := by
      have h := prefix_step config generation count below
      exact .cons (by rw [show request = _ from rfl, h]; exact .nil)
    exact ⟨requests ++ [request], by simp [length], runs_append execution single⟩

theorem round_exists (config : Config n) (generation : Nat) :
    ∃ requests : List (Request n), requests.length = n ∧
      Runs config (reset generation) requests (reset (generation+1)) := by
  simpa using prefix_execution config generation n (Nat.le_refl n)

theorem successive_reuse (config : Config n) (generation : Nat) :
    ∃ requests : List (Request n), requests.length = n+n ∧
      Runs config (reset generation) requests (reset (generation+2)) := by
  obtain ⟨first, firstLength, firstRun⟩ := round_exists config generation
  obtain ⟨second, secondLength, secondRun⟩ := round_exists config (generation+1)
  exact ⟨first ++ second, by simp [firstLength, secondLength], runs_append firstRun secondRun⟩

end Ptx.Barrier
