import Ptx.SharedBarrierMachine

/-! A complete finite schedule for the actual shared-store/barrier/partner-load
program. Candidate load values remain independent of the arena's concrete values. -/
namespace Ptx.SharedBarrier

structure Initial (n : Nat) where
  old : Fin n → Word
  inputs : Fin n → Word
  registers : Fin n → Nat → Word
  addresses : Fin n → Nat → Word

def slotAddress (thread : Fin n) : Word := BitVec.ofNat 32 (4*thread.val)

theorem slotAddress_toNat (config : Config n) (thread : Fin n) :
    (slotAddress thread).toNat = 4*thread.val := by
  have bound : 4*thread.val < 2^32 := by have := config.noWrap; have := thread.isLt; omega
  simp [slotAddress, Nat.mod_eq_of_lt bound]

theorem accessIndex_slot (config : Config n) (thread : Fin n) :
    accessIndex n (slotAddress thread) = some thread := by
  simp [accessIndex, slotAddress_toNat config]

def startThread (config : Config n) (initial : Initial n) (thread : Fin n) : ThreadState :=
  ⟨0, update (initial.registers thread) 0 (initial.inputs thread),
    update (update (initial.addresses thread) 0 (slotAddress thread)) 1 (slotAddress (config.partner thread)), false⟩

def start (config : Config n) (initial : Initial n) : State n :=
  ⟨startThread config initial, ⟨config.cta, initial.old⟩, Barrier.initial⟩

/-- First `count` participants have the new value; all others retain the old one. -/
def prefixMap (count : Nat) (before after : Fin n → α) : Fin n → α :=
  fun thread => if thread.val < count then after thread else before thread

theorem prefixMap_zero (before after : Fin n → α) : prefixMap 0 before after = before := by
  funext thread
  simp [prefixMap]

theorem prefixMap_full (before after : Fin n → α) : prefixMap n before after = after := by
  funext thread
  simp [prefixMap]

theorem update_prefixMap (count : Nat) (bound : count < n) (before after : Fin n → α) :
    update (prefixMap count before after) ⟨count,bound⟩ (after ⟨count,bound⟩) =
      prefixMap (count+1) before after := by
  funext thread
  by_cases same : thread = ⟨count,bound⟩
  · subst thread
    simp [update, prefixMap]
  · have different : thread.val ≠ count := by intro h; exact same (Fin.ext h)
    have less : thread.val < count+1 ↔ thread.val < count := by omega
    simp [update, prefixMap, same, less]

def storedThread (config : Config n) (initial : Initial n) (thread : Fin n) : ThreadState :=
  {startThread config initial thread with pc := 1}

def resumedThread (config : Config n) (initial : Initial n) (thread : Fin n) : ThreadState :=
  {startThread config initial thread with pc := 2}

def readValue (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (thread : Fin n) : Word :=
  (reads thread).getD (initial.inputs (config.partner thread))

def readThread (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (thread : Fin n) : ThreadState :=
  {startThread config initial thread with pc := 3, registers := update (startThread config initial thread).registers 1 (readValue config initial reads thread)}

def exitedThread (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (thread : Fin n) : ThreadState :=
  {readThread config initial reads thread with halted := true}

def storeStage (config : Config n) (initial : Initial n) (count : Nat) : State n :=
  ⟨prefixMap count (startThread config initial) (storedThread config initial),
    ⟨config.cta, prefixMap count initial.old initial.inputs⟩, Barrier.reset 0⟩

def barrierStage (config : Config n) (initial : Initial n) (count : Nat) : State n :=
  if count = n then
    ⟨resumedThread config initial, ⟨config.cta, initial.inputs⟩, Barrier.reset 1⟩
  else ⟨storedThread config initial, ⟨config.cta, initial.inputs⟩, Barrier.prefixState 0 count⟩

def readStage (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (count : Nat) : State n :=
  ⟨prefixMap count (resumedThread config initial) (readThread config initial reads),
    ⟨config.cta, initial.inputs⟩, Barrier.reset 1⟩

def exitStage (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (count : Nat) : State n :=
  ⟨prefixMap count (readThread config initial reads) (exitedThread config initial reads),
    ⟨config.cta, initial.inputs⟩, Barrier.reset 1⟩

def phaseKey (config : Config n) : Barrier.Key := ⟨config.cta, 0, 0, 1⟩

def storeEvent (config : Config n) (initial : Initial n) (thread : Fin n) : Event n :=
  .memory ⟨.store, config.cta, thread, 0, slotAddress thread, initial.inputs thread⟩

def arrivalEvent (config : Config n) (thread : Fin n) : Event n :=
  .barrier (.arrival (phaseKey config) thread)

def completionEvent (config : Config n) : Event n := .barrier (.completion (phaseKey config))

def readEvent (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) (thread : Fin n) : Event n :=
  .memory ⟨.load, config.cta, thread, 2, slotAddress (config.partner thread), readValue config initial reads thread⟩

def exitEvent (thread : Fin n) : Event n := .exited thread 3

/-- Exact fetched store, including its actual register value and event. -/
theorem store_stage_step (config : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (count : Nat) (bound : count < n) :
    stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (storeStage config initial count) =
      ⟨storeStage config initial (count+1), .advanced, [storeEvent config initial ⟨count,bound⟩]⟩ := by
  have lookup : prefixMap count (startThread config initial) (storedThread config initial) ⟨count,bound⟩ = startThread config initial ⟨count,bound⟩ := by simp [prefixMap]
  simp only [stepWith, storeStage, lookup]
  simp [startThread, Barrier.Waiting, Barrier.reset, program, dispatch, update,
    accessIndex_slot config, advance, storeEvent, prefixMap]
  congr 2
  exact ⟨update_prefixMap count bound (startThread config initial) (storedThread config initial),
    update_prefixMap count bound initial.old initial.inputs⟩

/-- Exact fetched partner load. Candidate and concrete modes differ only in the
selected observation, after passing the same shared ownership and address checks. -/
theorem read_stage_step (config : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (count : Nat) (bound : count < n) :
    stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (readStage config initial reads count) =
      ⟨readStage config initial reads (count+1), .advanced, [readEvent config initial reads ⟨count,bound⟩]⟩ := by
  have lookup : prefixMap count (resumedThread config initial) (readThread config initial reads) ⟨count,bound⟩ = resumedThread config initial ⟨count,bound⟩ := by simp [prefixMap]
  simp only [stepWith, readStage, lookup]
  simp [startThread, resumedThread, Barrier.Waiting, Barrier.reset, program, dispatch, update,
    accessIndex_slot config, readEvent, readValue, prefixMap]
  congr 2
  exact update_prefixMap count bound (resumedThread config initial) (readThread config initial reads)

theorem exit_stage_step (config : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (count : Nat) (bound : count < n) :
    stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (exitStage config initial reads count) =
      ⟨exitStage config initial reads (count+1), .halted, [exitEvent ⟨count,bound⟩]⟩ := by
  have lookup : prefixMap count (readThread config initial reads) (exitedThread config initial reads) ⟨count,bound⟩ = readThread config initial reads ⟨count,bound⟩ := by simp [prefixMap]
  simp only [stepWith, exitStage, lookup]
  simp [startThread, readThread, Barrier.Waiting, Barrier.reset, program, dispatch,
    exitEvent, readValue, prefixMap]
  congr 2
  exact update_prefixMap count bound (readThread config initial reads) (exitedThread config initial reads)

def barrierEvents (config : Config n) (thread : Fin n) : List (Event n) :=
  if thread.val+1 = n then [arrivalEvent config thread, completionEvent config]
  else [arrivalEvent config thread]

theorem barrier_stage_step (config : Config n) (initial : Initial n) (reads : Fin n → Option Word)
    (count : Nat) (bound : count < n) :
    stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (barrierStage config initial count) =
      ⟨barrierStage config initial (count+1),
        if count+1 = n then .released else .waiting, barrierEvents config ⟨count,bound⟩⟩ := by
  have notFull : count ≠ n := by omega
  let request : Barrier.Request n := ⟨phaseKey config, ⟨count,bound⟩⟩
  have same : request.key = Barrier.key (barrierConfig config) (Barrier.prefixState 0 count) := rfl
  have fresh : Barrier.Runnable (Barrier.prefixState 0 count) request.thread := by
    simp [Barrier.Runnable, Barrier.prefixState, request]
  have marked : Barrier.mark (Barrier.prefixState 0 count) request.thread = Barrier.prefixState 0 (count+1) :=
    Barrier.mark_prefix 0 count bound
  have protocol : Barrier.step (barrierConfig config) (Barrier.prefixState 0 count) request =
      if count+1 = n then
        ⟨Barrier.reset 1, .released, [.arrival (phaseKey config) ⟨count,bound⟩, .completion (phaseKey config)]⟩
      else ⟨Barrier.prefixState 0 (count+1), .waiting, [.arrival (phaseKey config) ⟨count,bound⟩]⟩ := by
    by_cases last : count+1 = n
    · have complete : Barrier.Complete (Barrier.mark (Barrier.prefixState 0 count) request.thread) := by
        rw [marked, Barrier.complete_prefix_iff (barrierConfig config)]
        omega
      simpa [last, request, Barrier.prefixState] using
        Barrier.completing_step (barrierConfig config) (Barrier.prefixState 0 count) request same fresh complete
    · have incomplete : ¬Barrier.Complete (Barrier.mark (Barrier.prefixState 0 count) request.thread) := by
        rw [marked, Barrier.complete_prefix_iff (barrierConfig config)]
        omega
      simpa [last, request, marked] using
        Barrier.waiting_step (barrierConfig config) (Barrier.prefixState 0 count) request same fresh incomplete
  rw [fetched_step config (reads ⟨count,bound⟩) ⟨count,bound⟩ (barrierStage config initial count)
    (by simp [barrierStage, notFull, storedThread, startThread])
    (by simp [barrierStage, notFull, Barrier.Waiting, Barrier.prefixState])
    (show program[((barrierStage config initial count).threads ⟨count,bound⟩).pc]? = some (.sync 0) by
      simp [barrierStage, notFull, storedThread, program])]
  have actualRequest : barrierRequest config (barrierStage config initial count) ⟨count,bound⟩ 0 = request := by
    simp [barrierRequest, barrierStage, notFull, storedThread, Barrier.prefixState, request, phaseKey]
  have actualState : (barrierStage config initial count).barrier = Barrier.prefixState 0 count := by
    simp [barrierStage, notFull]
  simp only [dispatch, actualRequest, actualState, protocol]
  by_cases last : count+1 = n
  · simp [last, barrierStage, notFull, barrierEvents, arrivalEvent, completionEvent,
      advance, storedThread, startThread]
    rfl
  · simp [last, barrierStage, notFull, barrierEvents, arrivalEvent]

/-- A fully explicit increasing-index schedule, with dependent indices checked. -/
def prefixSchedule : (count : Nat) → count ≤ n → List (Fin n)
  | 0, _ => []
  | count+1, bound => prefixSchedule count (by omega) ++ [⟨count, by omega⟩]

def schedule (n : Nat) : List (Fin n) := prefixSchedule n (Nat.le_refl n)

theorem prefixSchedule_length (count : Nat) (bound : count ≤ n) :
    (prefixSchedule count bound).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prefixSchedule, ih]

theorem schedule_length (n : Nat) : (schedule n).length = n := prefixSchedule_length _ _

/-- Generic composition of exact per-participant stage transitions. -/
theorem run_stage (config : Config n) (reads : Fin n → Option Word)
    (states : Nat → State n) (events : Fin n → List (Event n))
    (steps : ∀ count (bound : count < n),
      (stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (states count)).state = states (count+1) ∧
      (stepWith config (reads ⟨count,bound⟩) ⟨count,bound⟩ (states count)).events = events ⟨count,bound⟩)
    (count : Nat) (bound : count ≤ n) :
    runWith config reads (states 0) (prefixSchedule count bound) =
      ⟨states count, (prefixSchedule count bound).flatMap events⟩ := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have below : count < n := by omega
    simp only [prefixSchedule, runWith_append]
    rw [ih (by omega)]
    simp [runWith, (steps count below).1, (steps count below).2]

theorem flatMap_singleton (list : List α) (f : α → β) : list.flatMap (fun a => [f a]) = list.map f := by
  induction list with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem store_execution (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    runWith config reads (storeStage config initial 0) (schedule n) =
      ⟨storeStage config initial n, (schedule n).map (storeEvent config initial)⟩ := by
  have result := run_stage config reads (storeStage config initial) (fun thread => [storeEvent config initial thread])
    (fun count bound => by rw [store_stage_step]; exact ⟨rfl,rfl⟩) n (Nat.le_refl n)
  simpa [schedule, flatMap_singleton] using result

theorem barrier_execution (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    runWith config reads (barrierStage config initial 0) (schedule n) =
      ⟨barrierStage config initial n, (schedule n).flatMap (barrierEvents config)⟩ := by
  exact run_stage config reads (barrierStage config initial) (barrierEvents config)
    (fun count bound => by rw [barrier_stage_step]; exact ⟨rfl,rfl⟩) n (Nat.le_refl n)

theorem read_execution (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    runWith config reads (readStage config initial reads 0) (schedule n) =
      ⟨readStage config initial reads n, (schedule n).map (readEvent config initial reads)⟩ := by
  have result := run_stage config reads (readStage config initial reads) (fun thread => [readEvent config initial reads thread])
    (fun count bound => by rw [read_stage_step]; exact ⟨rfl,rfl⟩) n (Nat.le_refl n)
  simpa [schedule, flatMap_singleton] using result

theorem exit_execution (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    runWith config reads (exitStage config initial reads 0) (schedule n) =
      ⟨exitStage config initial reads n, (schedule n).map exitEvent⟩ := by
  have result := run_stage config reads (exitStage config initial reads) (fun thread => [exitEvent thread])
    (fun count bound => by rw [exit_stage_step]; exact ⟨rfl,rfl⟩) n (Nat.le_refl n)
  simpa [schedule, flatMap_singleton] using result

theorem barrier_trace_prefix (config : Config n) (count : Nat) (bound : count ≤ n) :
    (prefixSchedule count bound).flatMap (barrierEvents config) =
      if count = n then (prefixSchedule count bound).map (arrivalEvent config) ++ [completionEvent config]
      else (prefixSchedule count bound).map (arrivalEvent config) := by
  induction count with
  | zero =>
    have notZero : 0 ≠ n := by have := config.nonempty; omega
    simp [prefixSchedule, notZero]
  | succ count ih =>
    have below : count < n := by omega
    have notFull : count ≠ n := by omega
    simp only [prefixSchedule, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.map_cons, List.map_nil, ih, notFull, ↓reduceIte]
    by_cases last : count+1 = n <;> simp [barrierEvents, last, List.append_assoc]

theorem store_start (config : Config n) (initial : Initial n) :
    storeStage config initial 0 = start config initial := by
  simp [storeStage, prefixMap_zero, start, Barrier.initial]

theorem store_to_barrier (config : Config n) (initial : Initial n) :
    storeStage config initial n = barrierStage config initial 0 := by
  have notZero : 0 ≠ n := by have := config.nonempty; omega
  simp [storeStage, prefixMap_full, barrierStage, notZero, Barrier.prefix_zero]

theorem barrier_to_read (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    barrierStage config initial n = readStage config initial reads 0 := by
  simp [barrierStage, readStage, prefixMap_zero]

theorem read_to_exit (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    readStage config initial reads n = exitStage config initial reads 0 := by
  simp [readStage, exitStage, prefixMap_full, prefixMap_zero]

def fullSchedule (n : Nat) : List (Fin n) := schedule n ++ schedule n ++ schedule n ++ schedule n

def finalState (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) : State n :=
  ⟨exitedThread config initial reads, ⟨config.cta, initial.inputs⟩, Barrier.reset 1⟩

def canonicalTrace (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) : List (Event n) :=
  (schedule n).map (storeEvent config initial) ++
  (schedule n).map (arrivalEvent config) ++ [completionEvent config] ++
  (schedule n).map (readEvent config initial reads) ++ (schedule n).map exitEvent

/-- Actual fetched execution generates every store, barrier arrival, completion,
partner read and exit. Loaded candidates remain arbitrary throughout the proof. -/
theorem canonical_execution (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    runWith config reads (start config initial) (fullSchedule n) =
      ⟨finalState config initial reads, canonicalTrace config initial reads⟩ := by
  rw [← store_start]
  simp only [fullSchedule, runWith_append, store_execution]
  rw [store_to_barrier, barrier_execution, barrier_to_read, read_execution, read_to_exit, exit_execution]
  simp [canonicalTrace, finalState, exitStage, prefixMap_full, schedule, barrier_trace_prefix,
    List.append_assoc]

theorem fullSchedule_length (n : Nat) : (fullSchedule n).length = 4*n := by
  simp [fullSchedule, schedule_length]
  omega

theorem canonical_trace_length (config : Config n) (initial : Initial n) (reads : Fin n → Option Word) :
    (canonicalTrace config initial reads).length = 4*n+1 := by
  simp [canonicalTrace, schedule_length]
  omega

theorem candidate_completed (config : Config n) (initial : Initial n) (observations : Fin n → Word) :
    let result := runWith config (fun thread => some (observations thread)) (start config initial) (fullSchedule n)
    Runs config (fun thread => some (observations thread)) (start config initial) (fullSchedule n) result ∧
      (∀ thread, (result.state.threads thread).halted = true ∧
        (result.state.threads thread).pc = 3 ∧
        (result.state.threads thread).registers 1 = observations thread) ∧
      result.state.arena.words = initial.inputs ∧ result.state.barrier = Barrier.reset 1 ∧
      result.trace = canonicalTrace config initial (fun thread => some (observations thread)) := by
  dsimp
  refine ⟨runWith_sound _ _ _ _, ?_⟩
  rw [canonical_execution]
  simp [finalState, exitedThread, readThread, readValue, update]

theorem concrete_completed (config : Config n) (initial : Initial n) :
    let result := run config (start config initial) (fullSchedule n)
    Runs config (fun _ => none) (start config initial) (fullSchedule n) result ∧
      (∀ thread, (result.state.threads thread).halted = true ∧
        (result.state.threads thread).pc = 3 ∧
        (result.state.threads thread).registers 1 = initial.inputs (config.partner thread)) ∧
      result.state.arena.words = initial.inputs ∧ result.state.barrier = Barrier.reset 1 := by
  dsimp [run]
  refine ⟨runWith_sound _ _ _ _, ?_⟩
  rw [canonical_execution]
  simp [finalState, exitedThread, readThread, readValue, update]

theorem prefixSchedule_eq_take (count : Nat) (bound : count ≤ n) :
    prefixSchedule count bound = (List.finRange n).take count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have below : count < (List.finRange n).length := by simp; omega
    rw [prefixSchedule, ih, List.take_succ_eq_append_getElem below]
    simp

theorem schedule_eq_finRange (n : Nat) : schedule n = List.finRange n := by
  rw [schedule, prefixSchedule_eq_take]
  simpa only [List.length_finRange] using (List.take_length (l := List.finRange n))

theorem schedule_contains (thread : Fin n) : thread ∈ schedule n := by
  rw [schedule_eq_finRange]
  exact List.mem_finRange thread

theorem schedule_nodup (n : Nat) : (schedule n).Nodup := by
  rw [schedule_eq_finRange]
  exact List.nodup_finRange n

theorem schedule_map_eq_ofFn (f : Fin n → α) : (schedule n).map f = List.ofFn f := by
  rw [schedule_eq_finRange]
  apply List.ext_getElem (by simp)
  intro index left right
  simp

end Ptx.SharedBarrier
