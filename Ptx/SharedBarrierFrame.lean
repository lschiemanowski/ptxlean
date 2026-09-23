import Ptx.SharedBarrierProgram
import Ptx.SharedBarrierInvariant

/-! Data and address facts for every schedule of the fetched shared program. -/
namespace Ptx.SharedBarrier
namespace Frame

def Holds (before after : State n) : Prop :=
  (∀ thread, (after.threads thread).registers 0 = (before.threads thread).registers 0) ∧
  (∀ thread, (after.threads thread).addresses = (before.threads thread).addresses) ∧
  after.arena.owner = before.arena.owner

theorem refl (state : State n) : Holds state state := ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem trans (ab : Holds a b) (bc : Holds b c) : Holds a c :=
  ⟨fun t => (bc.1 t).trans (ab.1 t), fun t => (bc.2.1 t).trans (ab.2.1 t),
    bc.2.2.trans ab.2.2⟩

def PreservesInput : Instruction → Prop
  | .load destination _ => destination ≠ 0
  | _ => True

theorem fetched_preserves_input (fetch : program[(pc : Nat)]? = some instruction) :
    PreservesInput instruction := by
  have member := List.mem_of_getElem? fetch
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h <;> subst instruction <;> simp [PreservesInput]

theorem dispatch_frame (cfg : Config n) (reads : Option Word) (tid : Fin n)
    (instruction : Instruction) (state : State n) (safe : PreservesInput instruction) :
    Holds state (dispatch cfg reads tid instruction state).state := by
  cases instruction with
  | store a r =>
    simp only [dispatch]
    split
    · split
      · exact refl state
      · simp only [Holds]
        refine ⟨?_, ?_, trivial⟩ <;> intro other <;> by_cases h : other = tid <;> simp [update, advance, h]
    · exact refl state
  | load d a =>
    have ne : 0 ≠ d := Ne.symm safe
    simp only [dispatch]
    split
    · split
      · exact refl state
      · simp only [Holds]
        refine ⟨?_, ?_, trivial⟩ <;> intro other <;> by_cases h : other = tid <;> simp [update, ne, h]
    · exact refl state
  | sync resource =>
    simp only [dispatch]
    split <;> simp [Holds, advance]
  | exit =>
    simp only [dispatch, Holds]
    refine ⟨?_, ?_, trivial⟩ <;> intro other <;> by_cases h : other = tid <;> simp [update, h]

theorem step_frame (cfg : Config n) (reads : Option Word) (tid : Fin n) (state : State n) :
    Holds state (stepWith cfg reads tid state).state := by
  unfold stepWith
  split
  · exact refl state
  · split
    · exact refl state
    · split
      · exact refl state
      · rename_i instruction fetch
        exact dispatch_frame cfg reads tid instruction state (fetched_preserves_input fetch)

theorem run_frame (cfg : Config n) (reads : Fin n → Option Word) (state : State n)
    (schedule : List (Fin n)) : Holds state (runWith cfg reads state schedule).state := by
  induction schedule generalizing state with
  | nil => exact refl state
  | cons tid rest ih => exact trans (step_frame cfg (reads tid) tid state) (ih _)

theorem initialized (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) :
    (∀ thread, ((runWith cfg reads (start cfg initial) schedule).state.threads thread).registers 0 = initial.inputs thread) ∧
    (∀ thread, ((runWith cfg reads (start cfg initial) schedule).state.threads thread).addresses 0 = slotAddress thread) ∧
    (∀ thread, ((runWith cfg reads (start cfg initial) schedule).state.threads thread).addresses 1 = slotAddress (cfg.partner thread)) ∧
    (runWith cfg reads (start cfg initial) schedule).state.arena.owner = cfg.cta := by
  have frame := run_frame cfg reads (start cfg initial) schedule
  refine ⟨?_, ?_, ?_, frame.2.2⟩
  · intro thread
    rw [frame.1 thread]
    simp [start, startThread, update]
  · intro thread
    rw [frame.2.1 thread]
    simp [start, startThread, update]
  · intro thread
    rw [frame.2.1 thread]
    simp [start, startThread, update]

/-- Exact memory fields are obtained from the fetched program, with no event
relabeling or assumption about successful reads. -/
theorem step_memory_fields (cfg : Config n) (observations : Fin n → Word)
    (tid : Fin n) (state : State n)
    (member : Event.memory effect ∈ (stepWith cfg (some (observations tid)) tid state).events) :
    effect = ⟨.store, cfg.cta, tid, 0, (state.threads tid).addresses 0,
      (state.threads tid).registers 0⟩ ∨
    effect = ⟨.load, cfg.cta, tid, 2, (state.threads tid).addresses 1, observations tid⟩ := by
  obtain ⟨instruction, _, _, fetch, member⟩ := event_origin cfg _ tid state member
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  have pc : (state.threads tid).pc = 0 ∨ (state.threads tid).pc = 1 ∨
      (state.threads tid).pc = 2 ∨ (state.threads tid).pc = 3 := by
    simp only [program, List.length_cons, List.length_nil] at bound
    omega
  rcases pc with pc | pc | pc | pc
  · simp [program, pc] at fetch
    subst instruction
    simp only [dispatch] at member
    split at member
    · split at member
      · simp at member
      · simp only [List.mem_singleton, Event.memory.injEq] at member
        exact Or.inl (member.trans (by simp [pc]))
    · simp at member
  · simp [program, pc] at fetch
    subst instruction
    simp only [dispatch] at member
    split at member <;> simp at member
  · simp [program, pc] at fetch
    subst instruction
    simp only [dispatch] at member
    split at member
    · split at member
      · simp at member
      · simp only [List.mem_singleton, Event.memory.injEq] at member
        exact Or.inr (member.trans (by simp [pc]))
    · simp at member
  · simp [program, pc] at fetch
    subst instruction
    simp [dispatch] at member

theorem step_initial_fields (cfg : Config n) (initial : Initial n)
    (observations : Fin n → Word) (tid : Fin n) (state : State n)
    (frame : Holds (start cfg initial) state)
    (member : Event.memory effect ∈ (stepWith cfg (some (observations tid)) tid state).events) :
    Event.memory effect = storeEvent cfg initial tid ∨
    Event.memory effect = readEvent cfg initial (fun t => some (observations t)) tid := by
  rcases step_memory_fields cfg observations tid state member with h | h
  · left
    simp only [h, frame.1 tid, frame.2.1 tid]
    simp [storeEvent, start, startThread, update]
  · right
    simp only [h, frame.2.1 tid]
    simp [readEvent, readValue, start, startThread, update]

theorem trace_memory_fields (cfg : Config n) (initial : Initial n)
    (observations : Fin n → Word) (schedule : List (Fin n))
    (member : Event.memory effect ∈
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace) :
    Event.memory effect = storeEvent cfg initial effect.thread ∨
    Event.memory effect = readEvent cfg initial (fun t => some (observations t)) effect.thread := by
  revert member
  have general : ∀ state : State n, Holds (start cfg initial) state →
      Event.memory effect ∈ (runWith cfg (fun t => some (observations t)) state schedule).trace →
      Event.memory effect = storeEvent cfg initial effect.thread ∨
      Event.memory effect = readEvent cfg initial (fun t => some (observations t)) effect.thread := by
    induction schedule with
    | nil => intro state frame member; simp [runWith] at member
    | cons tid rest ih =>
      intro state frame member
      simp only [runWith, List.mem_append] at member
      rcases member with member | member
      · have fields := step_initial_fields cfg initial observations tid state frame member
        have thread := (memory_safe cfg (some (observations tid)) tid state effect member).2.2.2.1
        simpa only [thread] using fields
      · exact ih _ (trans frame (step_frame cfg _ tid state)) member
  intro member
  exact general _ (refl _) member

/-- This relates only the actual result to the proposed observation. It does not
assume that the observation is a permitted PTX memory value. -/
def Output (observations : Fin n → Word) (state : State n) : Prop :=
  ∀ thread, 3 ≤ (state.threads thread).pc →
    (state.threads thread).registers 1 = observations thread

theorem step_output (cfg : Config n) (observations : Fin n → Word)
    (state : State n) (control : Control state) (output : Output observations state)
    (tid : Fin n) : Output observations (stepWith cfg (some (observations tid)) tid state).state := by
  by_cases halted : (state.threads tid).halted = true
  · simpa [stepWith, halted] using output
  have live : (state.threads tid).halted = false := by simpa using halted
  by_cases waiting : Barrier.Waiting state.barrier tid
  · simpa [stepWith, live, waiting] using output
  have bound := control.bound tid
  have pcs : (state.threads tid).pc = 0 ∨ (state.threads tid).pc = 1 ∨
      (state.threads tid).pc = 2 ∨ (state.threads tid).pc = 3 := by omega
  rcases pcs with pc | pc | pc | pc
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_zero, dispatch]
    split
    · split
      · exact output
      · intro other hp
        by_cases same : other = tid
        · subst other; simp [update, advance, pc] at hp
        · simpa [update, same] using output other (by simpa [update, same] using hp)
    · exact output
  · have same : (barrierRequest cfg state tid 0).key = Barrier.key (barrierConfig cfg) state.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable state.barrier tid := by
      simpa [Barrier.Waiting, Barrier.Runnable] using waiting
    by_cases complete : Barrier.Complete (Barrier.mark state.barrier tid)
    · have bs := Barrier.completing_step (barrierConfig cfg) state.barrier
        (barrierRequest cfg state tid 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      intro other hp
      have atSite := control.all_at_barrier tid pc complete other
      simp [advance, atSite] at hp
    · have bs := Barrier.waiting_step (barrierConfig cfg) state.barrier
        (barrierRequest cfg state tid 0) same fresh complete
      simpa only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs, Output] using output
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    split
    · split
      · exact output
      · intro other hp
        by_cases same : other = tid
        · subst other; simp [update]
        · simpa [update, same] using output other (by simpa [update, same] using hp)
    · exact output
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    intro other hp
    by_cases same : other = tid
    · subst other; simpa [update] using output tid (by omega)
    · simpa [update, same] using output other (by simpa [update, same] using hp)

theorem run_output (cfg : Config n) (observations : Fin n → Word)
    (state : State n) (control : Control state) (output : Output observations state)
    (schedule : List (Fin n)) :
    Output observations (runWith cfg (fun t => some (observations t)) state schedule).state := by
  induction schedule generalizing state with
  | nil => exact output
  | cons tid rest ih =>
    exact ih _ (control.step_preserves cfg _ tid) (step_output cfg observations state control output tid)

theorem start_control (cfg : Config n) (initial : Initial n) : Control (start cfg initial) :=
  Control.initial (fun _ => rfl) (fun _ => rfl) rfl

theorem initialized_output (cfg : Config n) (initial : Initial n) (observations : Fin n → Word)
    (schedule : List (Fin n)) :
    Output observations (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).state :=
  run_output cfg observations _ (start_control cfg initial)
    (by intro thread hp; simp [start, startThread] at hp) schedule

theorem halted_output (cfg : Config n) (initial : Initial n) (observations : Fin n → Word)
    (schedule : List (Fin n)) (thread : Fin n)
    (halted : ((runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).state.threads thread).halted = true) :
    ((runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).state.threads thread).registers 1 = observations thread := by
  have control := (start_control cfg initial).run_preserves cfg (fun t => some (observations t)) schedule
  exact initialized_output cfg initial observations schedule thread (by rw [control.halted thread halted]; exact Nat.le_refl _)

theorem halted_memory_counts (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (thread : Fin n)
    (halted : ((runWith cfg reads (start cfg initial) schedule).state.threads thread).halted = true) :
    Control.memoryCount .store (runWith cfg reads (start cfg initial) schedule).trace thread = 1 ∧
    Control.memoryCount .load (runWith cfg reads (start cfg initial) schedule).trace thread = 1 := by
  have startControl := start_control cfg initial
  have pc := (startControl.run_preserves cfg reads schedule).halted thread halted
  constructor
  · have balance := startControl.run_memory_balance cfg reads schedule thread .store
    simp only [Control.memoryCredit, pc] at balance
    simpa [start, startThread] using balance.symm
  · have balance := startControl.run_memory_balance cfg reads schedule thread .load
    simp only [Control.memoryCredit, pc] at balance
    simpa [start, startThread] using balance.symm

end Frame
end Ptx.SharedBarrier
