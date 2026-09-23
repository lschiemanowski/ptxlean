import Ptx.SharedBarrierFrame

/-! Actual ordered publication paths for arbitrary schedules. The common phase
key is proved from fetched control; no global issue order is imposed. -/
namespace Ptx.SharedBarrier
namespace History
open List

/-- Filtering a trace for one memory kind and participant cannot count an absent
memory event. This lemma makes the later exact event accounting explicit. -/
theorem memory_member (trace : List (Event n)) (kind : MemoryKind) (thread : Fin n)
    (positive : 0 < Control.memoryCount kind trace thread) :
    ∃ effect, Event.memory effect ∈ trace ∧ effect.kind = kind ∧ effect.thread = thread := by
  obtain ⟨event, member⟩ := List.length_pos_iff_exists_mem.mp positive
  obtain ⟨member, accepted⟩ := List.mem_filter.mp member
  cases event with
  | memory effect => exact ⟨effect, member, by simpa using accepted⟩
  | barrier event => simp at accepted
  | exited thread pc => simp at accepted

theorem arrival_member (trace : List (Event n)) (thread : Fin n)
    (positive : 0 < Control.arrivals trace thread) :
    ∃ key, Event.barrier (.arrival key thread) ∈ trace := by
  obtain ⟨event, member⟩ := List.length_pos_iff_exists_mem.mp positive
  obtain ⟨member, accepted⟩ := List.mem_filter.mp member
  cases event with
  | memory effect => simp at accepted
  | exited thread pc => simp at accepted
  | barrier event =>
    cases event with
    | completion key => simp at accepted
    | arrival key selected =>
      have same : selected = thread := by simpa using accepted
      exact ⟨key, by simpa [same] using member⟩

theorem completion_member (trace : List (Event n))
    (positive : 0 < Control.completions trace) :
    ∃ key, Event.barrier (.completion key) ∈ trace := by
  obtain ⟨event, member⟩ := List.length_pos_iff_exists_mem.mp positive
  obtain ⟨member, accepted⟩ := List.mem_filter.mp member
  cases event with
  | memory effect => simp at accepted
  | exited thread pc => simp at accepted
  | barrier event =>
    cases event with
    | completion key => exact ⟨key, member⟩
    | arrival key selected => simp at accepted

theorem barrier_key (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (event : Barrier.Event n)
    (member : Event.barrier event ∈ (runWith cfg reads (start cfg initial) schedule).trace) :
    (match event with | .arrival key _ => key | .completion key => key) = phaseKey cfg := by
  obtain ⟨earlier, tid, suffix, _, eventAt, _⟩ := Control.run_event_prefix cfg reads schedule _ member
  have origin := ((Frame.start_control cfg initial).run_preserves cfg reads earlier).step_event_control cfg (reads tid) tid _ eventAt
  cases event with
  | arrival key thread => exact origin.2.2.2
  | completion key => exact origin.2.2

theorem store_fields (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (effect : MemoryEvent n) (kind : effect.kind = .store)
    (member : Event.memory effect ∈ (runWith cfg reads (start cfg initial) schedule).trace) :
    Event.memory effect = storeEvent cfg initial effect.thread := by
  obtain ⟨earlier, tid, suffix, _, eventAt, _⟩ := Control.run_event_prefix cfg reads schedule _ member
  have origin := ((Frame.start_control cfg initial).run_preserves cfg reads earlier).step_event_control cfg (reads tid) tid _ eventAt
  simp only [Control.EventControl, kind] at origin
  have pc := origin.2.2.1
  obtain ⟨instruction, _, _, fetch, emitted⟩ := event_origin cfg (reads tid) tid _ eventAt
  simp [program, pc] at fetch
  subst instruction
  have frame := Frame.run_frame cfg reads (start cfg initial) earlier
  simp only [dispatch] at emitted
  split at emitted
  · split at emitted
    · simp at emitted
    · simp only [List.mem_singleton, Event.memory.injEq] at emitted
      simp only [emitted, frame.1 tid, frame.2.1 tid, pc]
      simp [storeEvent, start, startThread, update]
  · simp at emitted

theorem counted_store (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (thread : Fin n)
    (positive : 0 < Control.memoryCount .store
      (runWith cfg reads (start cfg initial) schedule).trace thread) :
    storeEvent cfg initial thread ∈
      (runWith cfg reads (start cfg initial) schedule).trace := by
  obtain ⟨effect, member, kind, owner⟩ := memory_member _ _ _ positive
  have fields := store_fields cfg initial reads schedule effect kind member
  simpa only [fields, owner] using member

theorem arrival_path (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (thread : Fin n)
    (member : arrivalEvent cfg thread ∈
      (runWith cfg reads (start cfg initial) schedule).trace) :
    [storeEvent cfg initial thread, arrivalEvent cfg thread] <+
      (runWith cfg reads (start cfg initial) schedule).trace := by
  obtain ⟨earlier, selected, suffix, scheduleEq, eventAt, count⟩ :=
    (Frame.start_control cfg initial).arrival_has_store_prefix (fun _ => rfl) cfg
      reads schedule (phaseKey cfg) thread member
  have storeAt := counted_store cfg initial reads earlier thread (by omega)
  rw [scheduleEq, runWith_append]
  simp only [runWith]
  exact (List.singleton_sublist.mpr storeAt).append
    ((List.singleton_sublist.mpr eventAt).trans (List.sublist_append_left _ _))

/-- A completion-producing dispatch exposes exactly its final arrival followed
by completion. Other participants must already be waiting. -/
theorem completing_events (cfg : Config n) (state : State n) (control : Control state)
    (override : Option Word) (tid : Fin n) (key : Barrier.Key)
    (member : Event.barrier (.completion key) ∈ (stepWith cfg override tid state).events) :
    Barrier.Complete (Barrier.mark state.barrier tid) ∧
    (stepWith cfg override tid state).events = [arrivalEvent cfg tid, completionEvent cfg] := by
  have origin := control.step_event_control cfg override tid _ member
  have pc := origin.1
  have phase := origin.2.1
  obtain ⟨instruction, live, runnable, fetch, emitted⟩ := event_origin _ _ _ _ member
  simp [program, pc] at fetch
  subst instruction
  have same : (barrierRequest cfg state tid 0).key = Barrier.key (barrierConfig cfg) state.barrier := by
    simp [barrierRequest, Barrier.key, barrierConfig, pc]
  have fresh : Barrier.Runnable state.barrier tid := by simpa [Barrier.Waiting, Barrier.Runnable] using runnable
  by_cases complete : Barrier.Complete (Barrier.mark state.barrier tid)
  · refine ⟨complete, ?_⟩
    have bs := Barrier.completing_step (barrierConfig cfg) state.barrier (barrierRequest cfg state tid 0) same fresh complete
    simp only [stepWith, live, Bool.false_eq_true, ↓reduceIte, runnable, pc, program,
      List.getElem?_cons_succ, List.getElem?_cons_zero, dispatch, bs]
    simp [barrierRequest, phase, pc, arrivalEvent, completionEvent, phaseKey]
  · have bs := Barrier.waiting_step (barrierConfig cfg) state.barrier (barrierRequest cfg state tid 0) same fresh complete
    simp [dispatch, bs] at emitted

/-- Every producer's own publication and arrival precede the actual common
completion, including the final participant whose arrival shares that step. -/
theorem completion_path (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (writer : Fin n)
    (member : completionEvent cfg ∈
      (runWith cfg reads (start cfg initial) schedule).trace) :
    [storeEvent cfg initial writer, arrivalEvent cfg writer, completionEvent cfg] <+
      (runWith cfg reads (start cfg initial) schedule).trace := by
  obtain ⟨earlier, tid, suffix, scheduleEq, eventAt, traceEq⟩ :=
    Control.run_event_prefix cfg reads schedule _ member
  have atControl := (Frame.start_control cfg initial).run_preserves cfg reads earlier
  obtain ⟨complete, events⟩ := completing_events cfg _ atControl _ tid (phaseKey cfg) eventAt
  have origin := atControl.step_event_control cfg _ tid _ eventAt
  have pc : ((runWith cfg reads (start cfg initial) earlier).state.threads tid).pc = 1 := origin.1
  have phase : (runWith cfg reads (start cfg initial) earlier).state.barrier.generation = 0 := origin.2.1
  rw [traceEq]
  by_cases same : writer = tid
  · subst writer
    have balance := (Frame.start_control cfg initial).run_memory_balance cfg
      reads earlier tid .store
    simp only [Control.memoryCredit, pc] at balance
    have count : Control.memoryCount .store
        (runWith cfg reads (start cfg initial) earlier).trace tid = 1 := by
      simpa [start, startThread] using balance.symm
    have storeAt := counted_store cfg initial reads earlier tid (by omega)
    have pair : [arrivalEvent cfg tid, completionEvent cfg] <+
        (stepWith cfg (reads tid) tid
          (runWith cfg reads (start cfg initial) earlier).state).events := by rw [events]; exact List.Sublist.refl _
    exact ((List.singleton_sublist.mpr storeAt).append pair).trans (List.sublist_append_left _ _)
  · have bits : (runWith cfg reads (start cfg initial) earlier).state.barrier.arrived writer = true := by
      simpa [Barrier.Waiting, Barrier.mark, same] using complete writer
    have balance := (Frame.start_control cfg initial).run_arrival_balance cfg
      reads earlier writer
    simp only [Control.arrivalCredit, phase, bits] at balance
    have count : Control.arrivals
        (runWith cfg reads (start cfg initial) earlier).trace writer = 1 := by
      simpa [start, Barrier.initial, Barrier.reset] using balance.symm
    obtain ⟨key, arrivalAt⟩ := arrival_member _ writer (by omega : 0 < Control.arrivals
        (runWith cfg reads (start cfg initial) earlier).trace writer)
    have keyEq := barrier_key cfg initial reads earlier _ arrivalAt
    simp only at keyEq
    subst key
    have before := arrival_path cfg initial reads earlier writer arrivalAt
    exact (before.append (List.singleton_sublist.mpr eventAt)).trans (List.sublist_append_left _ _)

/-- The ordered path is in the actual trace for every scheduling interleaving;
the candidate read remains arbitrary and is not assumed memory-valid here. -/
theorem load_path_general (cfg : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (schedule : List (Fin n)) (effect : MemoryEvent n) (kind : effect.kind = .load)
    (member : Event.memory effect ∈
      (runWith cfg reads (start cfg initial) schedule).trace)
    (writer : Fin n) :
    [storeEvent cfg initial writer, arrivalEvent cfg writer, completionEvent cfg,
      Event.memory effect] <+
      (runWith cfg reads (start cfg initial) schedule).trace := by
  obtain ⟨earlier, tid, suffix, scheduleEq, eventAt, count, _⟩ :=
    (Frame.start_control cfg initial).load_has_completed_prefix rfl cfg
      reads schedule effect kind member
  obtain ⟨key, completeAt⟩ := completion_member _ (by omega : 0 < Control.completions
      (runWith cfg reads (start cfg initial) earlier).trace)
  have keyEq := barrier_key cfg initial reads earlier _ completeAt
  simp only at keyEq
  subst key
  have before := completion_path cfg initial reads earlier writer completeAt
  rw [scheduleEq, runWith_append]
  simp only [runWith]
  exact before.append ((List.singleton_sublist.mpr eventAt).trans (List.sublist_append_left _ _))

/-- Candidate specialization of the general actual-history theorem. -/
theorem load_path (cfg : Config n) (initial : Initial n) (observations : Fin n → Word)
    (schedule : List (Fin n)) (effect : MemoryEvent n) (kind : effect.kind = .load)
    (member : Event.memory effect ∈
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace)
    (writer : Fin n) :
    [storeEvent cfg initial writer, arrivalEvent cfg writer, completionEvent cfg,
      Event.memory effect] <+
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace :=
  load_path_general cfg initial (fun t => some (observations t)) schedule effect kind member writer

/-- Complete memory coverage is a count plus exact field identity, independent
of how stores and arrivals are interleaved. No other memory effects are present. -/
theorem completed_memory_accounting (cfg : Config n) (initial : Initial n)
    (observations : Fin n → Word) (schedule : List (Fin n))
    (completed : ∀ thread,
      ((runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).state.threads thread).halted = true) :
    (∀ thread, Control.memoryCount .store
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace thread = 1 ∧
      Control.memoryCount .load
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace thread = 1) ∧
    (∀ effect, Event.memory effect ∈
      (runWith cfg (fun t => some (observations t)) (start cfg initial) schedule).trace →
      Event.memory effect = storeEvent cfg initial effect.thread ∨
      Event.memory effect = readEvent cfg initial (fun t => some (observations t)) effect.thread) :=
  ⟨fun thread => Frame.halted_memory_counts cfg initial _ schedule thread (completed thread),
    fun _ member => Frame.trace_memory_fields cfg initial observations schedule member⟩

end History
end Ptx.SharedBarrier
