import PtxBinary32.ParallelConcrete

/-! Checked chronological replay of concrete-read traces. Replay validates
recorded addresses and load values; it is not a replacement for PTX memory
admission, coherence or barrier-order constraints. -/
namespace Ptx.Scalar.Parallel.Replay

structure Arrays where
  global : List Word
  shared : List Word
  deriving DecidableEq, Repr

def arrays (s : State n) : Arrays := ⟨s.global,s.shared⟩

def effect (memory : List Word) : Option Scalar.MemoryEffect → Option (List Word)
  | none => some memory
  | some e => match Scalar.addressIndex memory e.address with
    | .error _ => none
    | .ok index => match e.kind with
      | .load => if memory[index]! = e.value then some memory else none
      | .store => some (memory.set index e.value)

def event (memory : Arrays) : Event n → Option Arrays
  | .scalar _ space occ => match space with
    | none => if occ.memory.isNone then some memory else none
    | some .global => (effect memory.global occ.memory).map (fun g => {memory with global := g})
    | some .shared => (effect memory.shared occ.memory).map (fun s => {memory with shared := s})
  | _ => some memory

def trace (memory : Arrays) : List (Event n) → Option Arrays
  | [] => some memory
  | e::es => (event memory e).bind (fun next => trace next es)

theorem trace_append (memory : Arrays) (left right : List (Event n)) :
    trace memory (left++right) = (trace memory left).bind (fun middle => trace middle right) := by
  induction left generalizing memory with
  | nil => rfl
  | cons e es ih => simp [trace,ih,Option.bind_assoc]

/-- Replay checks the actual value in every recorded concrete load. -/
theorem eval_replays (s next : Scalar.State) (instruction : Scalar.Instr) (occ : Scalar.Occurrence)
    (step : Scalar.eval none instruction s = .next next occ) :
    effect s.memory occ.memory = some next.memory := by
  cases instruction with
  | mk guard op =>
    cases op <;> cases hg : guard.eval s <;> simp only [Scalar.eval,hg,ite_true] at step
    all_goals first
      | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj step; rfl)
      | contradiction
      | skip
    all_goals
      split at step
      · contradiction
      · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj step
        simp [effect,Scalar.occurrence,show Scalar.addressIndex s.memory _ = .ok _ from by assumption]

private theorem local_no_effect (step : Scalar.eval none instruction s = .next next occ)
    (empty : s.memory = []) : occ.memory = none := by
  cases hm : occ.memory with
  | none => rfl
  | some e =>
    have safe := Scalar.eval_memory_safe step hm
    simp [Scalar.ValidAddress,empty] at safe

theorem scalar_replays (state : State n) (t : Fin n) (space : Option Space) (instruction : Scalar.Instr) :
    trace (arrays state) (scalarStep none t space instruction state).events =
      some (arrays (scalarStep none t space instruction state).state) := by
  cases hs : Scalar.eval none instruction {(state.lanes t).scalar with memory := arena state space} with
  | next next occ =>
    have checked := eval_replays _ next instruction occ hs
    cases space with
    | none =>
      have empty := local_no_effect hs (by rfl)
      simp [scalarStep,hs,trace,event,empty,arrays,setLane]
    | some space =>
      cases space <;> simp [arena] at checked
      all_goals simp [scalarStep,hs,trace,event,arrays,setLane,checked]
  | halted next occ =>
    have empty := (Scalar.eval_halted hs).2
    cases space with
    | none => simp [scalarStep,hs,trace,event,arrays,setLane,empty]
    | some space => cases space <;> simp [scalarStep,hs,trace,event,arrays,setLane,empty,effect]
  | fault reason => simp [scalarStep,hs,trace]
  | unsupported name => simp [scalarStep,hs,trace]

theorem barriers_replay (memory : Arrays) (events : List (Barrier.Event n)) :
    trace memory (events.map Event.barrier) = some memory := by
  induction events with
  | nil => rfl
  | cons e es ih => simpa [trace,event] using ih

theorem dispatch_replays (dispatch : Dispatch cfg none t instruction state out) :
    trace (arrays state) out.events = some (arrays out.state) := by
  cases dispatch with
  | localStep => exact scalar_replays _ _ _ _
  | memory => exact scalar_replays _ _ _ _
  | binary32 _ => simp [trace,event,arrays,setLane]
  | exit => simp [trace,event,arrays,setLane]
  | sync =>
    rename_i resource
    cases h : (Barrier.step (barrierConfig cfg state t) state.barrier (barrierRequest cfg state t resource)).disposition <;>
      simp [synchronize,h,trace,arrays,barriers_replay]

theorem step_replays (step : Step cfg program none t state out) :
    trace (arrays state) out.events = some (arrays out.state) := by
  have h := step.2
  split at h
  · subst out; rfl
  · split at h
    · subst out; rfl
    · split at h
      · subst out; rfl
      · exact dispatch_replays h

theorem concrete_replays (run : ConcreteRuns cfg program state events final) :
    trace (arrays state) events = some (arrays final) := by
  induction run with
  | nil => rfl
  | cons step _ ih => rw [trace_append,step_replays step]; exact ih

/-- A changed load value fails replay even when the address remains valid. -/
theorem reject_wrong_load (memory : List Word) (address : Scalar.Address) (index : Nat) (value : Word)
    (checked : Scalar.addressIndex memory address = .ok index) (wrong : memory[index]! ≠ value) :
    effect memory (some ⟨.load,address,value⟩) = none := by
  rw [List.getElem!_eq_getElem?_getD] at wrong
  simp [effect,checked,wrong]

end Ptx.Scalar.Parallel.Replay
