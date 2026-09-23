import Ptx.SharedBarrierMachine

/-! Control-only invariants for every finite schedule of the fetched program.
No hypothesis constrains candidate read values or assumes a completed barrier. -/
namespace Ptx.SharedBarrier

structure Control (s : State n) : Prop where
  generation : s.barrier.generation = 0 ∨ s.barrier.generation = 1
  bound : ∀ t, (s.threads t).pc ≤ 3
  halted : ∀ t, (s.threads t).halted = true → (s.threads t).pc = 3
  before : s.barrier.generation = 0 → ∀ t, (s.threads t).pc ≤ 1
  waiting : ∀ t, Barrier.Waiting s.barrier t →
    s.barrier.generation = 0 ∧ (s.threads t).pc = 1
  after : s.barrier.generation = 1 → ∀ t, 2 ≤ (s.threads t).pc

namespace Control

variable {s : State n}

theorem initial (pcs : ∀ t, (s.threads t).pc = 0)
    (live : ∀ t, (s.threads t).halted = false)
    (barrier : s.barrier = Barrier.initial) : Control s := by
  constructor
  · left; simp [barrier, Barrier.initial, Barrier.reset]
  · intro t; simp [pcs]
  · intro t h; simp [live] at h
  · intro _ t; simp [pcs]
  · intro t h; simp [Barrier.Waiting, barrier, Barrier.initial, Barrier.reset] at h
  · intro h; simp [barrier, Barrier.initial, Barrier.reset] at h

theorem clear_after (h : Control s) (phase : s.barrier.generation = 1) (t : Fin n) :
    s.barrier.arrived t = false := by
  cases bits : s.barrier.arrived t
  · rfl
  · have := (h.waiting t bits).1; omega

theorem live_before (h : Control s) (phase : s.barrier.generation = 0) (t : Fin n) :
    (s.threads t).halted = false := by
  cases live : (s.threads t).halted
  · rfl
  · have := h.halted t live; have := h.before phase t; omega

theorem phase_at_barrier (h : Control s) (t : Fin n) (pc : (s.threads t).pc = 1) :
    s.barrier.generation = 0 := by
  rcases h.generation with zero | one
  · exact zero
  · have := h.after one t; omega

/-- The release precondition is a consequence of the actual final arrival and
waiting-state invariant, not an extra premise assuming everyone reached the site. -/
theorem all_at_barrier (h : Control s) (thread : Fin n)
    (pc : (s.threads thread).pc = 1)
    (complete : Barrier.Complete (Barrier.mark s.barrier thread)) :
    ∀ t, (s.threads t).pc = 1 := by
  intro t
  by_cases same : t = thread
  · simpa [same] using pc
  · have wait : Barrier.Waiting s.barrier t := by
      simpa [Barrier.Waiting, Barrier.mark, same] using complete t
    exact (h.waiting t wait).2

/-- Altering data without changing control does not affect the invariant. -/
theorem congr (h : Control s) {next : State n}
    (barrier : next.barrier = s.barrier)
    (pcs : ∀ t, (next.threads t).pc = (s.threads t).pc)
    (halted : ∀ t, (next.threads t).halted = (s.threads t).halted) : Control next := by
  constructor
  · simpa [barrier] using h.generation
  · intro t; simpa [pcs] using h.bound t
  · intro t ht; rw [halted] at ht; simpa [pcs] using h.halted t ht
  · intro hg t; rw [barrier] at hg; simpa [pcs] using h.before hg t
  · intro t ht; rw [barrier] at ht; simpa [barrier, pcs] using h.waiting t ht
  · intro hg t; rw [barrier] at hg; simpa [pcs] using h.after hg t

/-- Successful store/load advances one runnable, live thread at PC zero/two. -/
theorem advance_one (h : Control s) (thread : Fin n) (replacement : ThreadState)
    (pc : (s.threads thread).pc = 0 ∨ (s.threads thread).pc = 2)
    (runnable : ¬Barrier.Waiting s.barrier thread)
    (nextPC : replacement.pc = (s.threads thread).pc + 1)
    (nextLive : replacement.halted = false) (arena : Arena n) :
    Control {s with threads := update s.threads thread replacement, arena := arena} := by
  constructor
  · exact h.generation
  · intro t; by_cases same : t = thread
    · subst t; simp only [update, ↓reduceIte, nextPC]; rcases pc with hp | hp <;> omega
    · simpa [update, same] using h.bound t
  · intro t ht; by_cases same : t = thread
    · subst t; simp [update, nextLive] at ht
    · simp only [update, same, ↓reduceIte] at ht ⊢; exact h.halted t ht
  · intro phase t; by_cases same : t = thread
    · subst t; have := h.before phase thread
      simp only [update, ↓reduceIte, nextPC]; rcases pc with hp | hp <;> omega
    · simpa [update, same] using h.before phase t
  · intro t ht; by_cases same : t = thread
    · subst t; exact False.elim (runnable ht)
    · simpa [update, same] using h.waiting t ht
  · intro phase t; by_cases same : t = thread
    · subst t; have := h.after phase thread
      simp only [update, ↓reduceIte, nextPC]; omega
    · simpa [update, same] using h.after phase t

theorem mark_arrival (h : Control s) (thread : Fin n)
    (pc : (s.threads thread).pc = 1) :
    Control {s with barrier := Barrier.mark s.barrier thread} := by
  have phase := h.phase_at_barrier thread pc
  constructor
  · left; exact phase
  · exact h.bound
  · exact h.halted
  · intro _; exact h.before phase
  · intro t ht
    refine ⟨phase, ?_⟩
    by_cases same : t = thread
    · simpa [same] using pc
    · apply (h.waiting t _).2
      simpa [Barrier.Waiting, Barrier.mark, same] using ht
  · intro hg; change s.barrier.generation = 1 at hg; omega

theorem release (h : Control s) (thread : Fin n)
    (pc : (s.threads thread).pc = 1)
    (complete : Barrier.Complete (Barrier.mark s.barrier thread)) :
    Control {s with threads := (fun t => advance (s.threads t)), barrier := Barrier.reset (s.barrier.generation + 1)} := by
  have phase := h.phase_at_barrier thread pc
  have all := h.all_at_barrier thread pc complete
  constructor
  · right; simp [Barrier.reset, phase]
  · intro t; simp [advance, all]
  · intro t ht
    change (s.threads t).halted = true at ht
    have := h.live_before phase t; simp_all
  · intro hg; simp [Barrier.reset, phase] at hg
  · intro t ht; simp [Barrier.Waiting, Barrier.reset] at ht
  · intro _ t; simp [advance, all]

theorem exit (h : Control s) (thread : Fin n) (pc : (s.threads thread).pc = 3) :
    Control {s with threads := update s.threads thread {s.threads thread with halted := true}} := by
  constructor
  · exact h.generation
  · intro t; by_cases same : t = thread <;> simp [update, same, h.bound]
  · intro t ht; by_cases same : t = thread
    · subst t; simpa [update] using pc
    · simp only [update, same, ↓reduceIte] at ht ⊢; exact h.halted t ht
  · intro phase t; by_cases same : t = thread <;> simp [update, same, h.before phase]
  · intro t ht; by_cases same : t = thread <;> simpa [update, same] using h.waiting t ht
  · intro phase t; by_cases same : t = thread <;> simp [update, same, h.after phase]

/-- Count actual completion events in a finite emitted trace. -/
def completions (trace : List (Event n)) : Nat :=
  (trace.filter fun event => match event with
    | .barrier (.completion _) => true | _ => false).length

@[simp] theorem completions_append (left right : List (Event n)) :
    completions (left ++ right) = completions left + completions right := by
  simp [completions, List.filter_append]

/-- The actual fetched step preserves control, never retreats a PC, and advances
its generation exactly by its emitted completion count. -/
theorem step_properties (h : Control s) (config : Config n) (override : Option Word)
    (thread : Fin n) :
    let result := stepWith config override thread s
    Control result.state ∧
      (∀ t, (s.threads t).pc ≤ (result.state.threads t).pc) ∧
      result.state.barrier.generation = s.barrier.generation + completions result.events := by
  dsimp only
  by_cases halted : (s.threads thread).halted = true
  · simp [stepWith, halted, completions, h]
  have live : (s.threads thread).halted = false := by simpa using halted
  by_cases waiting : Barrier.Waiting s.barrier thread
  · simp [stepWith, live, waiting, completions, h]
  have bound := h.bound thread
  have pcs : (s.threads thread).pc = 0 ∨ (s.threads thread).pc = 1 ∨
      (s.threads thread).pc = 2 ∨ (s.threads thread).pc = 3 := by omega
  rcases pcs with pc | pc | pc | pc
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_zero, dispatch]
    split
    · split
      · simp [completions, h]
      · refine ⟨?_, ?_, ?_⟩
        · apply h.advance_one thread _ (Or.inl pc) waiting
          · rfl
          · exact live
        · intro t; by_cases same : t = thread <;> simp [update, same, advance]
        · simp [completions]
    · simp [completions, h]
  · have phase := h.phase_at_barrier thread pc
    have same : (barrierRequest config s thread 0).key = Barrier.key (barrierConfig config) s.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable s.barrier thread := by
      simpa [Barrier.Waiting, Barrier.Runnable] using waiting
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
    · have bs := Barrier.completing_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      refine ⟨h.release thread pc complete, ?_, ?_⟩
      · intro t; simp [advance]
      · simp [Barrier.reset, completions]
    · have bs := Barrier.waiting_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      exact ⟨h.mark_arrival thread pc, fun _ => Nat.le_refl _, by simp [Barrier.mark, completions]⟩
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    split
    · split
      · simp [completions, h]
      · refine ⟨?_, ?_, ?_⟩
        · apply h.advance_one thread _ (Or.inr pc) waiting
          · simp [pc]
          · rfl
        · intro t; by_cases same : t = thread <;> simp [update, same, pc]
        · simp [completions]
    · simp [completions, h]
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    refine ⟨by simpa only [pc] using h.exit thread pc, ?_, ?_⟩
    · intro t; by_cases same : t = thread <;> simp [update, same, pc]
    · simp [completions]

theorem step_preserves (h : Control s) (config : Config n) (override : Option Word)
    (thread : Fin n) : Control (stepWith config override thread s).state :=
  (h.step_properties config override thread).1

theorem step_pc_monotone (h : Control s) (config : Config n) (override : Option Word)
    (thread t : Fin n) : (s.threads t).pc ≤ ((stepWith config override thread s).state.threads t).pc :=
  (h.step_properties config override thread).2.1 t

/-- Arbitrary finite schedules, including unsuccessful/repeated dispatches. -/
theorem run_properties (h : Control s) (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) :
    let execution := runWith config reads s schedule
    Control execution.state ∧
      (∀ t, (s.threads t).pc ≤ (execution.state.threads t).pc) ∧
      execution.state.barrier.generation = s.barrier.generation + completions execution.trace := by
  induction schedule generalizing s with
  | nil => exact ⟨h, fun _ => Nat.le_refl _, by simp [runWith, completions]⟩
  | cons thread rest ih =>
    obtain ⟨first, monotone, count⟩ := h.step_properties config (reads thread) thread
    obtain ⟨last, later, total⟩ := ih first
    refine ⟨last, fun t => Nat.le_trans (monotone t) (later t), ?_⟩
    simp only [runWith, completions_append]
    omega

theorem run_preserves (h : Control s) (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) : Control (runWith config reads s schedule).state :=
  (h.run_properties config reads schedule).1

theorem completion_count (h : Control s) (phase : s.barrier.generation = 0)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n)) :
    completions (runWith config reads s schedule).trace =
      (runWith config reads s schedule).state.barrier.generation := by
  have := (h.run_properties config reads schedule).2.2
  omega

theorem completed_exactly_once (h : Control s) (phase : s.barrier.generation = 0)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n))
    (completed : (runWith config reads s schedule).state.barrier.generation = 1) :
    completions (runWith config reads s schedule).trace = 1 := by
  rw [h.completion_count phase config reads schedule, completed]

/-- Per-participant arrival balance includes a completed generation: after release
its bit is clear, but its unique arrival remains in history. -/
def arrivalCredit (s : State n) (t : Fin n) : Nat :=
  s.barrier.generation + if s.barrier.arrived t then 1 else 0

def arrivals (trace : List (Event n)) (t : Fin n) : Nat :=
  (trace.filter fun event => match event with
    | .barrier (.arrival _ thread) => decide (thread = t) | _ => false).length

@[simp] theorem arrivals_append (left right : List (Event n)) (t : Fin n) :
    arrivals (left ++ right) t = arrivals left t + arrivals right t := by
  simp [arrivals, List.filter_append]

theorem step_arrival_balance (h : Control s) (config : Config n) (override : Option Word)
    (thread t : Fin n) :
    arrivalCredit (stepWith config override thread s).state t =
      arrivalCredit s t + arrivals (stepWith config override thread s).events t := by
  by_cases halted : (s.threads thread).halted = true
  · simp [stepWith, halted, arrivals]
  have live : (s.threads thread).halted = false := by simpa using halted
  by_cases waiting : Barrier.Waiting s.barrier thread
  · simp [stepWith, live, waiting, arrivals]
  have bound := h.bound thread
  have pcs : (s.threads thread).pc = 0 ∨ (s.threads thread).pc = 1 ∨
      (s.threads thread).pc = 2 ∨ (s.threads thread).pc = 3 := by omega
  rcases pcs with pc | pc | pc | pc
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_zero, dispatch]
    split
    · split <;> simp [arrivalCredit, arrivals]
    · simp [arrivalCredit, arrivals]
  · have same : (barrierRequest config s thread 0).key = Barrier.key (barrierConfig config) s.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable s.barrier thread := by
      simpa [Barrier.Waiting, Barrier.Runnable] using waiting
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
    · have bs := Barrier.completing_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      by_cases sameThread : t = thread
      · subst t
        simp [arrivalCredit, arrivals, Barrier.reset, barrierRequest, Barrier.Runnable] at fresh ⊢
        simp [fresh]
      · have bits : s.barrier.arrived t = true := by
          simpa [Barrier.Waiting, Barrier.mark, sameThread] using complete t
        simp [arrivalCredit, arrivals, Barrier.reset, barrierRequest, Ne.symm sameThread, bits]
    · have bs := Barrier.waiting_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      by_cases sameThread : t = thread
      · subst t
        change s.barrier.arrived thread = false at fresh
        simp [arrivalCredit, arrivals, Barrier.mark, barrierRequest, fresh]
      · simp [arrivalCredit, arrivals, Barrier.mark, barrierRequest, sameThread, Ne.symm sameThread]
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    split
    · split <;> simp [arrivalCredit, arrivals]
    · simp [arrivalCredit, arrivals]
  · simp [stepWith, live, waiting, pc, program, dispatch, arrivalCredit, arrivals]

theorem run_arrival_balance (h : Control s) (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (t : Fin n) :
    arrivalCredit (runWith config reads s schedule).state t =
      arrivalCredit s t + arrivals (runWith config reads s schedule).trace t := by
  induction schedule generalizing s with
  | nil => simp [runWith, arrivals]
  | cons thread rest ih =>
    have first := h.step_arrival_balance config (reads thread) thread t
    have later := ih (h.step_preserves config (reads thread) thread)
    simp only [runWith, arrivals_append]
    omega

theorem all_arrived_exactly_once (h : Control s) (start : s.barrier = Barrier.initial)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n))
    (completed : (runWith config reads s schedule).state.barrier.generation = 1) (t : Fin n) :
    arrivals (runWith config reads s schedule).trace t = 1 := by
  have balance := h.run_arrival_balance config reads schedule t
  have clear := (h.run_preserves config reads schedule).clear_after completed t
  simpa [arrivalCredit, start, Barrier.initial, Barrier.reset, completed, clear] using balance.symm

/-- Once a thread leaves PC zero, its store must have appeared in the trace.
The post-load PC similarly records one load. These credits concern control only. -/
def memoryCredit (kind : MemoryKind) (s : State n) (t : Fin n) : Nat :=
  match kind with
  | .store => if (s.threads t).pc = 0 then 0 else 1
  | .load => if (s.threads t).pc = 3 then 1 else 0

def memoryCount (kind : MemoryKind) (trace : List (Event n)) (t : Fin n) : Nat :=
  (trace.filter fun event => match event with
    | .memory effect => decide (effect.kind = kind ∧ effect.thread = t) | _ => false).length

@[simp] theorem memoryCount_append (kind : MemoryKind) (left right : List (Event n)) (t : Fin n) :
    memoryCount kind (left ++ right) t = memoryCount kind left t + memoryCount kind right t := by
  simp [memoryCount, List.filter_append]

theorem step_memory_balance (h : Control s) (config : Config n) (override : Option Word)
    (thread t : Fin n) (kind : MemoryKind) :
    memoryCredit kind (stepWith config override thread s).state t =
      memoryCredit kind s t + memoryCount kind (stepWith config override thread s).events t := by
  by_cases halted : (s.threads thread).halted = true
  · simp [stepWith, halted, memoryCount]
  have live : (s.threads thread).halted = false := by simpa using halted
  by_cases waiting : Barrier.Waiting s.barrier thread
  · simp [stepWith, live, waiting, memoryCount]
  have bound := h.bound thread
  have pcs : (s.threads thread).pc = 0 ∨ (s.threads thread).pc = 1 ∨
      (s.threads thread).pc = 2 ∨ (s.threads thread).pc = 3 := by omega
  rcases pcs with pc | pc | pc | pc
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_zero, dispatch]
    split
    · split
      · simp [memoryCount]
      · cases kind <;> by_cases sameThread : t = thread
        all_goals simp [memoryCredit, memoryCount, update, advance, sameThread, eq_comm, pc]
    · simp [memoryCount]
  · have same : (barrierRequest config s thread 0).key = Barrier.key (barrierConfig config) s.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable s.barrier thread := by
      simpa [Barrier.Waiting, Barrier.Runnable] using waiting
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
    · have bs := Barrier.completing_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      have all := h.all_at_barrier thread pc complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      cases kind <;> simp [memoryCredit, memoryCount, advance, all]
    · have bs := Barrier.waiting_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
        pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
      cases kind <;> simp [memoryCredit, memoryCount]
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    split
    · split
      · simp [memoryCount]
      · cases kind <;> by_cases sameThread : t = thread
        all_goals simp [memoryCredit, memoryCount, update, sameThread, eq_comm, pc]
    · simp [memoryCount]
  · simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, waiting,
      pc, program, List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch]
    cases kind <;> by_cases sameThread : t = thread
    all_goals simp [memoryCredit, memoryCount, update, sameThread, pc]

theorem run_memory_balance (h : Control s) (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (t : Fin n) (kind : MemoryKind) :
    memoryCredit kind (runWith config reads s schedule).state t =
      memoryCredit kind s t + memoryCount kind (runWith config reads s schedule).trace t := by
  induction schedule generalizing s with
  | nil => simp [runWith, memoryCount]
  | cons thread rest ih =>
    have first := h.step_memory_balance config (reads thread) thread t kind
    have later := ih (h.step_preserves config (reads thread) thread)
    simp only [runWith, memoryCount_append]
    omega

/-- Control information carried by each actual emitted event. -/
def EventControl (config : Config n) (s : State n) (selected : Fin n) : Event n → Prop
  | .memory effect => effect.thread = selected ∧
      effect.pc = (s.threads selected).pc ∧
      match effect.kind with
      | .store => (s.threads selected).pc = 0 ∧ s.barrier.generation = 0
      | .load => (s.threads selected).pc = 2 ∧ s.barrier.generation = 1
  | .barrier (.arrival key thread) => thread = selected ∧
      (s.threads selected).pc = 1 ∧ s.barrier.generation = 0 ∧
      key = ⟨config.cta, 0, 0, 1⟩
  | .barrier (.completion key) => (s.threads selected).pc = 1 ∧
      s.barrier.generation = 0 ∧ key = ⟨config.cta, 0, 0, 1⟩
  | .exited thread pc => thread = selected ∧ pc = 3 ∧ (s.threads selected).pc = 3 ∧
      s.barrier.generation = 1

theorem step_event_control (h : Control s) (config : Config n) (override : Option Word)
    (thread : Fin n) (event : Event n)
    (member : event ∈ (stepWith config override thread s).events) :
    EventControl config s thread event := by
  obtain ⟨instruction, live, runnable, fetch, emitted⟩ := event_origin _ _ _ _ member
  have bound := h.bound thread
  have pcs : (s.threads thread).pc = 0 ∨ (s.threads thread).pc = 1 ∨
      (s.threads thread).pc = 2 ∨ (s.threads thread).pc = 3 := by omega
  rcases pcs with pc | pc | pc | pc
  · have phase : s.barrier.generation = 0 := by
      rcases h.generation with zero | one
      · exact zero
      · have := h.after one thread; omega
    simp [program, pc] at fetch
    subst instruction
    simp only [dispatch] at emitted
    split at emitted
    · split at emitted
      · simp at emitted
      · simp only [List.mem_singleton] at emitted; subst event
        simp [EventControl, pc, phase]
    · simp at emitted
  · have phase := h.phase_at_barrier thread pc
    simp [program, pc] at fetch
    subst instruction
    have same : (barrierRequest config s thread 0).key = Barrier.key (barrierConfig config) s.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable s.barrier thread := by
      simpa [Barrier.Waiting, Barrier.Runnable] using runnable
    by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
    · have bs := Barrier.completing_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [dispatch, bs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at emitted
      rcases emitted with rfl | rfl <;> simp [EventControl, barrierRequest, pc, phase]
    · have bs := Barrier.waiting_step (barrierConfig config) s.barrier
        (barrierRequest config s thread 0) same fresh complete
      simp only [dispatch, bs, List.map_cons, List.map_nil, List.mem_singleton] at emitted
      subst event
      simp [EventControl, barrierRequest, pc, phase]
  · have phase : s.barrier.generation = 1 := by
      rcases h.generation with zero | one
      · have := h.before zero thread; omega
      · exact one
    simp [program, pc] at fetch
    subst instruction
    simp only [dispatch] at emitted
    split at emitted
    · split at emitted
      · simp at emitted
      · simp only [List.mem_singleton] at emitted; subst event
        simp [EventControl, pc, phase]
    · simp at emitted
  · have phase : s.barrier.generation = 1 := by
      rcases h.generation with zero | one
      · have := h.before zero thread; omega
      · exact one
    simp [program, pc] at fetch
    subst instruction
    simp only [dispatch, List.mem_singleton] at emitted; subst event
    simp [EventControl, pc, phase]

/-- Every trace event has an actual schedule prefix immediately before its step.
The trace decomposition exposes all preceding emitted events, without timestamps. -/
theorem run_event_prefix (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (event : Event n)
    (member : event ∈ (runWith config reads s schedule).trace) :
    ∃ earlier thread suffix,
      schedule = earlier ++ thread :: suffix ∧
      event ∈ (stepWith config (reads thread) thread (runWith config reads s earlier).state).events ∧
      (runWith config reads s schedule).trace =
        (runWith config reads s earlier).trace ++
        (stepWith config (reads thread) thread (runWith config reads s earlier).state).events ++
        (runWith config reads
          (stepWith config (reads thread) thread (runWith config reads s earlier).state).state suffix).trace := by
  induction schedule generalizing s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith, List.mem_append] at member
    rcases member with first | later
    · exact ⟨[], selected, rest, rfl, first, by simp [runWith]⟩
    · obtain ⟨earlier, thread, suffix, scheduleEq, eventAt, traceEq⟩ := ih later
      refine ⟨selected :: earlier, thread, suffix, ?_, ?_, ?_⟩
      · simp [scheduleEq]
      · simpa [runWith] using eventAt
      · simp only [runWith, traceEq, List.append_assoc]

/-- Any load in an arbitrary initial run has one actual completion in a strictly
preceding schedule prefix. The earlier also contains every participant's arrival. -/
theorem load_has_completed_prefix (h : Control s) (start : s.barrier = Barrier.initial)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n))
    (effect : MemoryEvent n) (kind : effect.kind = .load)
    (member : Event.memory effect ∈ (runWith config reads s schedule).trace) :
    ∃ earlier thread suffix,
      schedule = earlier ++ thread :: suffix ∧
      Event.memory effect ∈
        (stepWith config (reads thread) thread (runWith config reads s earlier).state).events ∧
      completions (runWith config reads s earlier).trace = 1 ∧
      ∀ t, arrivals (runWith config reads s earlier).trace t = 1 := by
  obtain ⟨earlier, thread, suffix, scheduleEq, eventAt, _⟩ := run_event_prefix config reads schedule _ member
  have atControl := h.run_preserves config reads earlier
  have origin := atControl.step_event_control config (reads thread) thread _ eventAt
  simp only [EventControl, kind] at origin
  have phase := origin.2.2.2
  refine ⟨earlier, thread, suffix, scheduleEq, eventAt, ?_, ?_⟩
  · exact h.completed_exactly_once (by simp [start, Barrier.initial, Barrier.reset]) config reads earlier phase
  · exact h.all_arrived_exactly_once start config reads earlier phase

/-- Each arrival has the same thread's actual store in an earlier schedule prefix. -/
theorem arrival_has_store_prefix (h : Control s) (pcs : ∀ t, (s.threads t).pc = 0)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n))
    (key : Barrier.Key) (t : Fin n)
    (member : Event.barrier (.arrival key t) ∈ (runWith config reads s schedule).trace) :
    ∃ earlier thread suffix,
      schedule = earlier ++ thread :: suffix ∧
      Event.barrier (.arrival key t) ∈
        (stepWith config (reads thread) thread (runWith config reads s earlier).state).events ∧
      memoryCount .store (runWith config reads s earlier).trace t = 1 := by
  obtain ⟨earlier, thread, suffix, scheduleEq, eventAt, _⟩ := run_event_prefix config reads schedule _ member
  have atControl := h.run_preserves config reads earlier
  have origin := atControl.step_event_control config (reads thread) thread _ eventAt
  change t = thread ∧ _ at origin
  have pc : ((runWith config reads s earlier).state.threads t).pc = 1 := by
    simpa only [origin.1] using origin.2.1
  have balance := h.run_memory_balance config reads earlier t .store
  refine ⟨earlier, thread, suffix, scheduleEq, eventAt, ?_⟩
  simpa [memoryCredit, pc, pcs] using balance.symm

/-- An actual completion event certifies that every participant was parked at
PC one immediately before its final-arrival step. -/
theorem completion_all_at_barrier (h : Control s) (config : Config n) (override : Option Word)
    (thread : Fin n) (key : Barrier.Key)
    (member : Event.barrier (.completion key) ∈ (stepWith config override thread s).events) :
    ∀ t, (s.threads t).pc = 1 := by
  have origin := h.step_event_control config override thread _ member
  have pc : (s.threads thread).pc = 1 := origin.1
  obtain ⟨instruction, live, runnable, fetch, emitted⟩ := event_origin _ _ _ _ member
  simp [program, pc] at fetch
  subst instruction
  by_cases complete : Barrier.Complete (Barrier.mark s.barrier thread)
  · exact h.all_at_barrier thread pc complete
  · have same : (barrierRequest config s thread 0).key = Barrier.key (barrierConfig config) s.barrier := by
      simp [barrierRequest, Barrier.key, barrierConfig, pc]
    have fresh : Barrier.Runnable s.barrier thread := by
      simpa [Barrier.Waiting, Barrier.Runnable] using runnable
    have bs := Barrier.waiting_step (barrierConfig config) s.barrier
      (barrierRequest config s thread 0) same fresh complete
    simp [dispatch, bs] at emitted

/-- Every participant's store is in a strictly earlier schedule segment than
an actual completion. No chosen memory result is used to obtain this ordering. -/
theorem completion_has_stores_prefix (h : Control s) (pcs : ∀ t, (s.threads t).pc = 0)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n))
    (key : Barrier.Key)
    (member : Event.barrier (.completion key) ∈ (runWith config reads s schedule).trace) :
    ∃ earlier thread suffix,
      schedule = earlier ++ thread :: suffix ∧
      Event.barrier (.completion key) ∈
        (stepWith config (reads thread) thread (runWith config reads s earlier).state).events ∧
      ∀ t, memoryCount .store (runWith config reads s earlier).trace t = 1 := by
  obtain ⟨earlier, thread, suffix, scheduleEq, eventAt, _⟩ := run_event_prefix config reads schedule _ member
  have atControl := h.run_preserves config reads earlier
  have all := atControl.completion_all_at_barrier config (reads thread) thread key eventAt
  refine ⟨earlier, thread, suffix, scheduleEq, eventAt, ?_⟩
  intro t
  have balance := h.run_memory_balance config reads earlier t .store
  simpa [memoryCredit, all, pcs] using balance.symm

/-- The halted flag changes only by emitting that thread's actual exit event. -/
theorem step_halted_iff (config : Config n) (override : Option Word)
    (selected t : Fin n) :
    ((stepWith config override selected s).state.threads t).halted = true ↔
      (s.threads t).halted = true ∨
      ∃ pc, Event.exited t pc ∈ (stepWith config override selected s).events := by
  unfold stepWith
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i instruction fetch
        cases instruction with
        | store a r =>
          simp only [dispatch]
          split
          · split
            · simp
            · by_cases same : t = selected <;> simp [update, advance, same]
          · simp
        | load d a =>
          simp only [dispatch]
          split
          · split
            · simp
            · by_cases same : t = selected <;> simp [update, same]
          · simp
        | sync resource =>
          simp only [dispatch]
          split <;> simp [advance]
        | exit => by_cases same : t = selected <;> simp [dispatch, update, same]

theorem run_halted_iff (config : Config n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (t : Fin n) :
    ((runWith config reads s schedule).state.threads t).halted = true ↔
      (s.threads t).halted = true ∨
      ∃ pc, Event.exited t pc ∈ (runWith config reads s schedule).trace := by
  induction schedule generalizing s with
  | nil => simp [runWith]
  | cons selected rest ih =>
    simp only [runWith, ih, step_halted_iff, List.mem_append]
    constructor
    · rintro ((initial | ⟨pc, first⟩) | ⟨pc, later⟩)
      · exact Or.inl initial
      · exact Or.inr ⟨pc, Or.inl first⟩
      · exact Or.inr ⟨pc, Or.inr later⟩
    · rintro (initial | ⟨pc, first | later⟩)
      · exact Or.inl (Or.inl initial)
      · exact Or.inl (Or.inr ⟨pc, first⟩)
      · exact Or.inr ⟨pc, later⟩

theorem halted_iff_exit_event (h : Control s) (live : ∀ t, (s.threads t).halted = false)
    (config : Config n) (reads : Fin n → Option Word) (schedule : List (Fin n)) (t : Fin n) :
    ((runWith config reads s schedule).state.threads t).halted = true ↔
      Event.exited t 3 ∈ (runWith config reads s schedule).trace := by
  rw [run_halted_iff]
  simp only [live, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨pc, member⟩
    obtain ⟨earlier, selected, suffix, _, eventAt, _⟩ := run_event_prefix config reads schedule _ member
    have origin := (h.run_preserves config reads earlier).step_event_control config (reads selected) selected _ eventAt
    have equal : pc = 3 := origin.2.1
    simpa only [equal] using member
  · exact fun member => ⟨3, member⟩

end Control
end Ptx.SharedBarrier
