import Ptx.SharedReductionControl

/-! Actual temporal publication history. No read freshness or output equality
is an invariant premise. Address/value provenance remains a separate layer. -/
namespace Ptx.Scalar.SharedReduction.Machine.History
open List

/-- One after the actual publication instruction, zero before it. -/
def publicationCredit (lane : Lane) : Nat :=
  match lane.block with
  | .producer => 0
  | .publish => if lane.scalar.pc = 0 then 0 else 1
  | _ => 1

def isPublication (thread : Fin n) : Event n → Bool
  | .scalar issuer _ (some .shared) event =>
      issuer == thread && (event.memory.map (fun effect => effect.kind == .store)).getD false
  | _ => false

def publications (thread : Fin n) (trace : List (Event n)) : Nat :=
  (trace.filter (isPublication thread)).length

@[simp] theorem publications_append (thread : Fin n) (left right : List (Event n)) :
    publications thread (left ++ right) = publications thread left + publications thread right := by
  simp [publications,List.filter_append]

theorem credit_bound (lane : Lane) : publicationCredit lane ≤ 1 := by
  cases block : lane.block <;> simp [publicationCredit,block]
  split <;> omega

set_option maxRecDepth 4096 in
private theorem step_publication_balance (cfg : Config n) (reads : Option Word)
    (selected thread : Fin n) (s : State n) (invariant : Control.Invariant s) :
    publicationCredit ((step cfg reads selected s).state.lanes thread) =
      publicationCredit (s.lanes thread) + publications thread (step cfg reads selected s).events := by
  by_cases halted : (s.lanes selected).halted = true
  · simp [step,halted,publications]
  have live : (s.lanes selected).halted = false := Bool.eq_false_iff.mpr halted
  cases block : (s.lanes selected).block
  case barrier =>
    cases pc : (s.lanes selected).scalar.pc with
    | succ k => simp [step,live,block,pc,program,publications]
    | zero =>
      by_cases waiting : s.barrier.arrived selected = true
      · simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
          Barrier.key,waiting,publications]
      · by_cases complete : Barrier.Complete (Barrier.mark s.barrier selected)
        · have credit : publicationCredit (s.lanes thread) = 1 := by
            by_cases eq : thread = selected
            · subst thread; simp [publicationCredit,block]
            · have arrived : s.barrier.arrived thread = true := by
                simpa [Barrier.Waiting,Barrier.mark,eq] using complete thread
              have site := invariant thread arrived
              simp [publicationCredit,site.1]
          rw [credit]
          simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
            Barrier.key,waiting,complete,publications,isPublication,publicationCredit]
        · simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
            Barrier.key,waiting,complete,publications,isPublication]
  all_goals
    rcases pc : (s.lanes selected).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals by_cases same : thread = selected
    all_goals cases pred : (s.lanes selected).scalar.preds 0
    all_goals simp [step,live,block,pc,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
      publications,isPublication,occurrence,setLane,same,sharedStore,Operand64.eval,Operand32.eval,pred]
    all_goals first
      | (cases address : addressIndex s.shared ((s.lanes selected).scalar.addrs 0) <;>
          simp_all [publicationCredit,publications,isPublication,occurrence,setLane,Instr.plain])
      | skip
    all_goals cases globalAddress : addressIndex s.global ((s.lanes selected).scalar.addrs 0)
    all_goals cases outputAddress : addressIndex s.global (bytePointer n)
    all_goals try simp_all [publicationCredit,publications,isPublication,occurrence,setLane,Instr.plain]
    all_goals (intro reversed; exact same reversed.symm)

theorem run_publication_balance (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (invariant : Control.Invariant s) (thread : Fin n) :
    publicationCredit ((runWith cfg reads schedule s).state.lanes thread) =
      publicationCredit (s.lanes thread) + publications thread (runWith cfg reads schedule s).trace := by
  induction schedule generalizing reads s with
  | nil => simp [runWith,publications]
  | cons selected rest ih =>
    have first := step_publication_balance cfg (reads 0) selected thread s invariant
    have later := ih (fun i => reads (i+1)) _ (Control.step_preserves cfg (reads 0) selected s invariant)
    simp only [runWith,publications_append]
    omega

theorem publication_count (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) (thread : Fin n) :
    publications thread (runWith cfg reads schedule (start input scratch seeds)).trace =
      publicationCredit ((runWith cfg reads schedule (start input scratch seeds)).state.lanes thread) := by
  simpa [start,publicationCredit] using
    (run_publication_balance cfg reads schedule _ (Control.initial input scratch seeds) thread).symm

theorem publication_at_most_once (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) (thread : Fin n) :
    publications thread (runWith cfg reads schedule (start input scratch seeds)).trace ≤ 1 := by
  rw [publication_count]
  exact credit_bound _

/-- A continuation block is reached only after the full barrier releases. -/
def phaseCredit (lane : Lane) : Nat :=
  match lane.block with
  | .producer | .publish | .barrier => 0
  | _ => 1

def isCompletion : Event n → Bool
  | .barrier (.completion _) => true
  | _ => false

def completions (trace : List (Event n)) : Nat := (trace.filter isCompletion).length

@[simp] theorem completions_append (left right : List (Event n)) :
    completions (left ++ right) = completions left + completions right := by
  simp [completions,List.filter_append]
set_option maxRecDepth 4096 in
private theorem step_phase_balance (cfg : Config n) (reads : Option Word)
    (selected thread : Fin n) (s : State n) (invariant : Control.Invariant s) :
    phaseCredit ((step cfg reads selected s).state.lanes thread) =
      phaseCredit (s.lanes thread) + completions (step cfg reads selected s).events := by
  by_cases halted : (s.lanes selected).halted = true
  · simp [step,halted,completions]
  have live : (s.lanes selected).halted = false := Bool.eq_false_iff.mpr halted
  cases block : (s.lanes selected).block
  case barrier =>
    cases pc : (s.lanes selected).scalar.pc with
    | succ k => simp [step,live,block,pc,program,completions]
    | zero =>
      by_cases waiting : s.barrier.arrived selected = true
      · simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
          Barrier.key,waiting,completions]
      · by_cases complete : Barrier.Complete (Barrier.mark s.barrier selected)
        · have credit : phaseCredit (s.lanes thread) = 0 := by
            by_cases eq : thread = selected
            · subst thread; simp [phaseCredit,block]
            · have arrived : s.barrier.arrived thread = true := by
                simpa [Barrier.Waiting,Barrier.mark,eq] using complete thread
              have site := invariant thread arrived
              simp [phaseCredit,site.1]
          rw [credit]
          simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
            Barrier.key,waiting,complete,completions,isCompletion,phaseCredit]
          rfl
        · simp [step,live,block,pc,program,dispatch,Barrier.step,barrierConfig,barrierRequest,
            Barrier.key,waiting,complete,completions,isCompletion]
  all_goals
    rcases pc : (s.lanes selected).scalar.pc with _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals by_cases same : thread = selected
    all_goals cases pred : (s.lanes selected).scalar.preds 0
    all_goals simp [step,live,block,pc,program,dispatch,scalarStep,eval,Instr.plain,Guard.eval,
      completions,isCompletion,occurrence,setLane,same,sharedStore,Operand64.eval,Operand32.eval,pred]
    all_goals first
      | (cases address : addressIndex s.shared ((s.lanes selected).scalar.addrs 0) <;>
          simp_all [phaseCredit,completions,isCompletion,occurrence,setLane,Instr.plain])
      | skip
    all_goals cases globalAddress : addressIndex s.global ((s.lanes selected).scalar.addrs 0)
    all_goals cases outputAddress : addressIndex s.global (bytePointer n)
    all_goals try simp_all [phaseCredit,completions,isCompletion,occurrence,setLane,Instr.plain]
    all_goals try (intro reversed; exact same reversed.symm)

theorem run_phase_balance (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (invariant : Control.Invariant s) (thread : Fin n) :
    phaseCredit ((runWith cfg reads schedule s).state.lanes thread) =
      phaseCredit (s.lanes thread) + completions (runWith cfg reads schedule s).trace := by
  induction schedule generalizing reads s with
  | nil => simp [runWith,completions]
  | cons selected rest ih =>
    have first := step_phase_balance cfg (reads 0) selected thread s invariant
    have later := ih (fun i => reads (i+1)) _ (Control.step_preserves cfg (reads 0) selected s invariant)
    simp only [runWith,completions_append]
    omega

theorem completion_count (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) (thread : Fin n) :
    completions (runWith cfg reads schedule (start input scratch seeds)).trace =
      phaseCredit ((runWith cfg reads schedule (start input scratch seeds)).state.lanes thread) := by
  simpa [start,phaseCredit] using
    (run_phase_balance cfg reads schedule _ (Control.initial input scratch seeds) thread).symm

/-- Dynamic read indices advance with the actual schedule prefix, including waits. -/
theorem run_event_prefix (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (event : Event n)
    (member : event ∈ (runWith cfg reads schedule s).trace) :
    ∃ earlier selected suffix tail,
      schedule = earlier ++ selected :: suffix ∧
      event ∈ (step cfg (reads earlier.length) selected (runWith cfg reads earlier s).state).events ∧
      (runWith cfg reads schedule s).trace =
        (runWith cfg reads earlier s).trace ++
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier s).state).events ++ tail := by
  induction schedule generalizing reads s with
  | nil => simp [runWith] at member
  | cons selected rest ih =>
    simp only [runWith,List.mem_append] at member
    rcases member with first | later
    · exact ⟨[],selected,rest,(runWith cfg (fun i => reads (i+1)) rest (step cfg (reads 0) selected s).state).trace,
        rfl,first,by simp [runWith]⟩
    · obtain ⟨earlier,thread,suffix,tail,scheduleEq,eventAt,traceEq⟩ := ih _ _ later
      refine ⟨selected :: earlier,thread,suffix,tail,?_,?_,?_⟩
      · simp [scheduleEq]
      · simpa [runWith] using eventAt
      · simpa [runWith,List.append_assoc] using congrArg
          (fun trace => (step cfg (reads 0) selected s).events ++ trace) traceEq

private theorem scalar_no_barrier (reads : Option Word) (thread : Fin n) (space : Option Space)
    (i : Instr) (s : State n) (event : Barrier.Event n) :
    Event.barrier event ∉ (scalarStep reads thread space i s).events := by
  rcases space with _ | (_ | _)
  all_goals simp only [scalarStep]; split <;> simp

theorem step_barrier_origin (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (event : Barrier.Event n)
    (member : Event.barrier event ∈ (step cfg reads selected s).events) :
    Control.AtBarrier (s.lanes selected) ∧
      event ∈ (Barrier.step (barrierConfig cfg) s.barrier (barrierRequest cfg s selected 0)).events := by
  simp only [step] at member
  split at member
  · simp at member
  · rename_i live
    have alive : (s.lanes selected).halted = false := Bool.eq_false_iff.mpr live
    split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i => exact False.elim (scalar_no_barrier reads selected none i s event member)
      | memory space i => exact False.elim (scalar_no_barrier reads selected (some space) i s event member)
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        obtain ⟨block,pc,rfl⟩ := Control.fetch_sync _ _ _ fetch
        refine ⟨⟨block,pc,alive⟩,?_⟩
        simp only [dispatch] at member
        split at member
        · simp at member
        all_goals simpa using member

theorem step_arrival_origin (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (key : Barrier.Key) (thread : Fin n)
    (member : Event.barrier (.arrival key thread) ∈ (step cfg reads selected s).events) :
    thread = selected ∧ Control.AtBarrier (s.lanes thread) ∧
      key = Barrier.key (barrierConfig cfg) s.barrier := by
  obtain ⟨site,actual⟩ := step_barrier_origin cfg reads selected s _ member
  obtain ⟨same,fresh,keyEq,threadEq⟩ := (Barrier.arrival_event_iff ..).mp actual
  have eq : thread = selected := threadEq
  exact ⟨eq,by simpa [eq] using site,keyEq.trans same⟩

theorem arrival_has_store_prefix (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (key : Barrier.Key) (thread : Fin n)
    (member : Event.barrier (.arrival key thread) ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace) :
    ∃ earlier selected suffix tail,
      schedule = earlier ++ selected :: suffix ∧
      Event.barrier (.arrival key thread) ∈
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events ∧
      (runWith cfg reads schedule (start input scratch seeds)).trace =
        (runWith cfg reads earlier (start input scratch seeds)).trace ++
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events ++ tail ∧
      publications thread (runWith cfg reads earlier (start input scratch seeds)).trace = 1 := by
  obtain ⟨earlier,selected,suffix,tail,scheduleEq,eventAt,traceEq⟩ := run_event_prefix cfg reads schedule _ _ member
  have origin := step_arrival_origin cfg (reads earlier.length) selected _ key thread eventAt
  refine ⟨earlier,selected,suffix,tail,scheduleEq,eventAt,traceEq,?_⟩
  rw [publication_count]
  simp [publicationCredit,origin.2.1.1]

private theorem step_generation_balance (cfg : Config n) (reads : Option Word)
    (selected : Fin n) (s : State n) :
    (step cfg reads selected s).state.barrier.generation = s.barrier.generation +
      completions (step cfg reads selected s).events := by
  simp only [step]
  split
  · simp [completions]
  · split
    · simp [completions]
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        simp only [dispatch,scalarStep]
        split <;> simp [completions,isCompletion,setLane]
      | memory space i =>
        cases space <;> simp only [dispatch,scalarStep] <;>
          split <;> simp [completions,isCompletion,setLane]
      | branch guard destination => simp [dispatch,setLane,completions,isCompletion]
      | exit => simp [dispatch,setLane,completions,isCompletion]
      | sync resource =>
        obtain ⟨_,_,rfl⟩ := Control.fetch_sync _ _ _ fetch
        by_cases waiting : s.barrier.arrived selected = true
        · simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,completions]
        · by_cases complete : Barrier.Complete (Barrier.mark s.barrier selected)
          all_goals simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,
            complete,Barrier.reset,completions,isCompletion]
          all_goals try simp [Barrier.mark,completions,isCompletion]
          all_goals rfl

theorem generation_count (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) :
    (runWith cfg reads schedule s).state.barrier.generation =
      s.barrier.generation + completions (runWith cfg reads schedule s).trace := by
  induction schedule generalizing reads s with
  | nil => simp [runWith,completions]
  | cons selected rest ih =>
    have first := step_generation_balance cfg (reads 0) selected s
    have later := ih (fun i => reads (i+1)) (step cfg (reads 0) selected s).state
    simp only [runWith,completions_append]
    omega

def phaseKey (cfg : Config n) : Barrier.Key := ⟨cfg.cta,0,0,5⟩

theorem generation_at_barrier (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) (thread : Fin n)
    (block : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes thread).block = .barrier) :
    (runWith cfg reads schedule (start input scratch seeds)).state.barrier.generation = 0 := by
  have count := completion_count cfg reads schedule input scratch seeds thread
  have generation := generation_count cfg reads schedule (start input scratch seeds)
  simp [phaseCredit,block] at count
  rw [count] at generation
  simpa [start,Barrier.initial,Barrier.reset] using generation

theorem barrier_key (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (event : Barrier.Event n)
    (member : Event.barrier event ∈ (runWith cfg reads schedule (start input scratch seeds)).trace) :
    (match event with | .arrival key _ => key | .completion key => key) = phaseKey cfg := by
  obtain ⟨earlier,selected,suffix,tail,_,atStep,_⟩ := run_event_prefix cfg reads schedule _ _ member
  obtain ⟨site,actual⟩ := step_barrier_origin cfg (reads earlier.length) selected _ event atStep
  have zero := generation_at_barrier cfg reads earlier input scratch seeds selected site.1
  cases event with
  | arrival key thread =>
    have origin := (Barrier.arrival_event_iff ..).mp actual
    simpa [Barrier.key,barrierConfig,barrierRequest,phaseKey,zero] using origin.2.2.1
  | completion key =>
    have origin := (Barrier.completion_event_iff ..).mp actual
    simpa [Barrier.key,barrierConfig,barrierRequest,phaseKey,zero] using origin.2.2.2

def arrivalCredit (s : State n) (thread : Fin n) : Nat :=
  s.barrier.generation + if s.barrier.arrived thread then 1 else 0

def arrivals (thread : Fin n) (trace : List (Event n)) : Nat :=
  (trace.filter fun event => match event with
    | .barrier (.arrival _ issuer) => issuer == thread | _ => false).length

@[simp] theorem arrivals_append (thread : Fin n) (left right : List (Event n)) :
    arrivals thread (left ++ right) = arrivals thread left + arrivals thread right := by
  simp [arrivals,List.filter_append]

private theorem step_arrival_balance (cfg : Config n) (reads : Option Word)
    (selected thread : Fin n) (s : State n) :
    arrivalCredit (step cfg reads selected s).state thread = arrivalCredit s thread +
      arrivals thread (step cfg reads selected s).events := by
  simp only [step]
  split
  · simp [arrivals]
  · split
    · simp [arrivals]
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        simp only [dispatch,scalarStep]
        split <;> simp [arrivalCredit,arrivals,setLane] <;> rfl
      | memory space i =>
        cases space <;> simp only [dispatch,scalarStep] <;>
          split <;> simp [arrivalCredit,arrivals,setLane] <;> rfl
      | branch guard destination => simp [dispatch,setLane,arrivalCredit,arrivals] <;> rfl
      | exit => simp [dispatch,setLane,arrivalCredit,arrivals] <;> rfl
      | sync resource =>
        obtain ⟨_,_,rfl⟩ := Control.fetch_sync _ _ _ fetch
        by_cases waiting : s.barrier.arrived selected = true
        · simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,arrivalCredit,arrivals]
        · have fresh : s.barrier.arrived selected = false := Bool.eq_false_iff.mpr waiting
          by_cases complete : Barrier.Complete (Barrier.mark s.barrier selected)
          · by_cases same : thread = selected
            · subst thread
              simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
                Barrier.reset,arrivalCredit,arrivals,fresh]
              all_goals simp [Barrier.mark,arrivals]
            · have marked : s.barrier.arrived thread = true := by
                simpa [Barrier.Waiting,Barrier.mark,same] using complete thread
              simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
                Barrier.reset,arrivalCredit,arrivals,marked,same,Ne.symm same]
              all_goals simp [Barrier.mark,arrivals]
          · by_cases same : thread = selected
            · subst thread
              simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
                arrivalCredit,arrivals,fresh]
              all_goals simp [Barrier.mark,arrivals,fresh]
            · simp [dispatch,Barrier.step,barrierRequest,barrierConfig,Barrier.key,waiting,complete,
                arrivalCredit,arrivals,same,Ne.symm same]
              all_goals simp [Barrier.mark,arrivals,same]

theorem run_arrival_balance (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) :
    arrivalCredit (runWith cfg reads schedule s).state thread =
      arrivalCredit s thread + arrivals thread (runWith cfg reads schedule s).trace := by
  induction schedule generalizing reads s with
  | nil => simp [runWith,arrivals]
  | cons selected rest ih =>
    have first := step_arrival_balance cfg (reads 0) selected thread s
    have later := ih (fun i => reads (i+1)) (step cfg (reads 0) selected s).state
    simp only [runWith,arrivals_append]
    omega

theorem publication_member (thread : Fin n) (trace : List (Event n))
    (positive : 0 < publications thread trace) :
    ∃ event, event ∈ trace ∧ isPublication thread event = true := by
  obtain ⟨event,member⟩ := List.length_pos_iff_exists_mem.mp positive
  exact ⟨event,List.mem_filter.mp member⟩

theorem completion_member (trace : List (Event n)) (positive : 0 < completions trace) :
    ∃ key, Event.barrier (.completion key) ∈ trace := by
  obtain ⟨event,member⟩ := List.length_pos_iff_exists_mem.mp positive
  obtain ⟨member,accepted⟩ := List.mem_filter.mp member
  cases event with
  | scalar _ _ _ _ => simp [isCompletion] at accepted
  | branch _ _ _ _ => simp [isCompletion] at accepted
  | exit _ _ => simp [isCompletion] at accepted
  | barrier bar =>
    cases bar with
    | arrival _ _ => simp [isCompletion] at accepted
    | completion key => exact ⟨key,member⟩

theorem arrival_member (thread : Fin n) (trace : List (Event n))
    (positive : 0 < arrivals thread trace) :
    ∃ key, Event.barrier (.arrival key thread) ∈ trace := by
  obtain ⟨event,member⟩ := List.length_pos_iff_exists_mem.mp positive
  obtain ⟨member,accepted⟩ := List.mem_filter.mp member
  cases event with
  | scalar _ _ _ _ => simp at accepted
  | branch _ _ _ _ => simp at accepted
  | exit _ _ => simp at accepted
  | barrier bar =>
    cases bar with
    | completion _ => simp at accepted
    | arrival key issuer =>
      have same : issuer = thread := by simpa using accepted
      exact ⟨key,by simpa [same] using member⟩

theorem arrival_path (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (key : Barrier.Key) (thread : Fin n)
    (member : Event.barrier (.arrival key thread) ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace) :
    ∃ store, isPublication thread store = true ∧
      [store,Event.barrier (.arrival key thread)] <+
        (runWith cfg reads schedule (start input scratch seeds)).trace := by
  obtain ⟨earlier,selected,suffix,tail,_,eventAt,traceEq,count⟩ :=
    arrival_has_store_prefix cfg reads schedule input scratch seeds key thread member
  obtain ⟨store,storeAt,published⟩ := publication_member thread (runWith cfg reads earlier (start input scratch seeds)).trace (by omega)
  refine ⟨store,published,?_⟩
  rw [traceEq]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using (List.singleton_sublist.mpr storeAt).append
    ((List.singleton_sublist.mpr eventAt).trans (List.sublist_append_left _ tail))

/-- The completing step emits its final arrival immediately before completion. -/
theorem completing_events (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (key : Barrier.Key)
    (member : Event.barrier (.completion key) ∈ (step cfg reads selected s).events) :
    Control.AtBarrier (s.lanes selected) ∧ Barrier.Complete (Barrier.mark s.barrier selected) ∧
      (step cfg reads selected s).events =
        [Event.barrier (.arrival key selected),Event.barrier (.completion key)] := by
  obtain ⟨site,actual⟩ := step_barrier_origin cfg reads selected s _ member
  obtain ⟨same,fresh,complete,keyEq⟩ := (Barrier.completion_event_iff ..).mp actual
  refine ⟨site,complete,?_⟩
  have barrierStep := Barrier.completing_step (barrierConfig cfg) s.barrier
    (barrierRequest cfg s selected 0) same fresh complete
  simp [step,site.1,site.2.1,site.2.2,program,dispatch,barrierStep,keyEq]
  rfl

theorem completion_has_stores_prefix (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (key : Barrier.Key)
    (member : Event.barrier (.completion key) ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace) :
    ∃ earlier selected suffix tail,
      schedule = earlier ++ selected :: suffix ∧
      (runWith cfg reads schedule (start input scratch seeds)).trace =
        (runWith cfg reads earlier (start input scratch seeds)).trace ++
        [Event.barrier (.arrival key selected),Event.barrier (.completion key)] ++ tail ∧
      ∀ thread, publications thread (runWith cfg reads earlier (start input scratch seeds)).trace = 1 := by
  obtain ⟨earlier,selected,suffix,tail,scheduleEq,eventAt,traceEq⟩ := run_event_prefix cfg reads schedule _ _ member
  obtain ⟨site,complete,events⟩ := completing_events cfg (reads earlier.length) selected _ key eventAt
  have invariant := Control.runWith_preserves cfg reads earlier _ (Control.initial input scratch seeds)
  refine ⟨earlier,selected,suffix,tail,scheduleEq,by rw [traceEq,events],?_⟩
  intro thread
  rw [publication_count]
  by_cases same : thread = selected
  · subst thread; simp [publicationCredit,site.1]
  · have arrived : (runWith cfg reads earlier (start input scratch seeds)).state.barrier.arrived thread = true := by
      simpa [Barrier.Waiting,Barrier.mark,same] using complete thread
    have atSite := invariant thread arrived
    simp [publicationCredit,atSite.1]

theorem completion_path (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (key : Barrier.Key) (writer : Fin n)
    (member : Event.barrier (.completion key) ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace) :
    ∃ store, isPublication writer store = true ∧
      [store,Event.barrier (.arrival key writer),Event.barrier (.completion key)] <+
        (runWith cfg reads schedule (start input scratch seeds)).trace := by
  have keyIs := barrier_key cfg reads schedule input scratch seeds (.completion key) member
  change key = phaseKey cfg at keyIs
  obtain ⟨earlier,selected,suffix,tail,_,eventAt,traceEq⟩ := run_event_prefix cfg reads schedule _ _ member
  obtain ⟨site,complete,events⟩ := completing_events cfg (reads earlier.length) selected _ key eventAt
  have control := Control.runWith_preserves cfg reads earlier _ (Control.initial input scratch seeds)
  by_cases same : writer = selected
  · subst writer
    have count : publications selected (runWith cfg reads earlier (start input scratch seeds)).trace = 1 := by
      rw [publication_count]; simp [publicationCredit,site.1]
    obtain ⟨store,storeAt,published⟩ := publication_member selected (runWith cfg reads earlier (start input scratch seeds)).trace (by omega)
    refine ⟨store,published,?_⟩
    rw [traceEq,events]
    have suffixPath : [Event.barrier (.arrival key selected),Event.barrier (.completion key)] <+
        Event.barrier (.arrival key selected) :: Event.barrier (.completion key) :: tail :=
      .cons_cons _ (.cons_cons _ (List.nil_sublist tail))
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (List.singleton_sublist.mpr storeAt).append suffixPath
  · have arrived : (runWith cfg reads earlier (start input scratch seeds)).state.barrier.arrived writer = true := by
      simpa [Barrier.Waiting,Barrier.mark,same] using complete writer
    have zero := generation_at_barrier cfg reads earlier input scratch seeds selected site.1
    have balance := run_arrival_balance cfg reads earlier (start input scratch seeds) writer
    have initialCredit : arrivalCredit (start input scratch seeds) writer = 0 := rfl
    rw [initialCredit,Nat.zero_add] at balance
    simp only [arrivalCredit,zero,arrived,↓reduceIte,Nat.zero_add] at balance
    obtain ⟨arrivalKey,arrivalAt⟩ := arrival_member writer (runWith cfg reads earlier (start input scratch seeds)).trace (by omega)
    have arrivalKeyIs := barrier_key cfg reads earlier input scratch seeds (.arrival arrivalKey writer) arrivalAt
    have equalKey : arrivalKey = key := arrivalKeyIs.trans keyIs.symm
    subst arrivalKey
    obtain ⟨store,published,path⟩ := arrival_path cfg reads earlier input scratch seeds key writer arrivalAt
    refine ⟨store,published,?_⟩
    rw [traceEq]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using path.append ((List.singleton_sublist.mpr (show Event.barrier (.completion key) ∈
      (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events by
        rw [events]; simp)).trans (List.sublist_append_left _ tail))

private theorem fetched_shared_load (block : Block) (pc : Nat) (i : Instr)
    (fetch : (program n block)[pc]? = some (.memory .shared i))
    (load : Control.memoryKind i.op = some .load) : block = .loop := by
  have member := List.mem_of_getElem? fetch
  cases block <;> simp [program] at member
  all_goals subst i
  · simp [sharedStore,Instr.plain,Control.memoryKind] at load
  · rfl

/-- Shared loads cannot originate in the producer or publication block. -/
theorem step_shared_load_loop (cfg : Config n) (reads : Option Word) (selected : Fin n)
    (s : State n) (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈ (step cfg reads selected s).events)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    (s.lanes selected).block = .loop := by
  simp only [step] at member
  split at member
  · simp at member
  · split at member
    · simp at member
    · rename_i instruction fetch
      cases instruction with
      | localStep i =>
        have origin := Control.scalar_effect_origin reads selected none i s thread block (some .shared) event effect member memory
        simp at origin
      | memory actualSpace i =>
        have origin := Control.scalar_effect_origin reads selected (some actualSpace) i s thread block (some .shared) event effect member memory
        have spaceEq : actualSpace = .shared := by simpa using origin.2.2.1.symm
        subst actualSpace
        exact fetched_shared_load _ _ i fetch (by simpa [load] using origin.2.2.2.2.2.2)
      | branch guard destination => simp [dispatch] at member
      | exit => simp [dispatch] at member
      | sync resource =>
        simp only [dispatch] at member
        split at member <;> simp only [List.mem_map] at member
        · simp at member
        all_goals obtain ⟨_,_,impossible⟩ := member; contradiction

theorem load_has_completed_prefix (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block (some .shared) event ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    ∃ earlier selected suffix tail,
      schedule = earlier ++ selected :: suffix ∧
      .scalar thread block (some .shared) event ∈
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events ∧
      (runWith cfg reads schedule (start input scratch seeds)).trace =
        (runWith cfg reads earlier (start input scratch seeds)).trace ++
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events ++ tail ∧
      completions (runWith cfg reads earlier (start input scratch seeds)).trace = 1 := by
  obtain ⟨earlier,selected,suffix,tail,scheduleEq,eventAt,traceEq⟩ := run_event_prefix cfg reads schedule _ _ member
  have blockIs := step_shared_load_loop cfg (reads earlier.length) selected _ thread block event effect eventAt memory load
  refine ⟨earlier,selected,suffix,tail,scheduleEq,eventAt,traceEq,?_⟩
  rw [completion_count cfg reads earlier input scratch seeds selected]
  simp [phaseCredit,blockIs]

/-- Every actual shared load has every writer's ordered store/arrival/completion
path in its preceding trace, with one exact common phase key. -/
theorem load_path (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect) (writer : Fin n)
    (member : .scalar thread block (some .shared) event ∈
      (runWith cfg reads schedule (start input scratch seeds)).trace)
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    ∃ store, isPublication writer store = true ∧
      [store,Event.barrier (.arrival (phaseKey cfg) writer),Event.barrier (.completion (phaseKey cfg)),
        Event.scalar thread block (some .shared) event] <+
        (runWith cfg reads schedule (start input scratch seeds)).trace := by
  obtain ⟨earlier,selected,suffix,tail,_,eventAt,traceEq,count⟩ :=
    load_has_completed_prefix cfg reads schedule input scratch seeds thread block event effect member memory load
  obtain ⟨key,completed⟩ := completion_member (runWith cfg reads earlier (start input scratch seeds)).trace (by omega)
  have keyIs := barrier_key cfg reads earlier input scratch seeds (.completion key) completed
  change key = phaseKey cfg at keyIs
  subst key
  obtain ⟨store,published,path⟩ := completion_path cfg reads earlier input scratch seeds (phaseKey cfg) writer completed
  refine ⟨store,published,?_⟩
  rw [traceEq]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using path.append ((List.singleton_sublist.mpr eventAt).trans (List.sublist_append_left _ tail))

/-- The filter predicate exposes genuine shared-store effects, not an abstract
publication token whose data fields could be supplied separately. -/
theorem isPublication_iff (thread : Fin n) (event : Event n) :
    isPublication thread event = true ↔
      ∃ block occurrence effect, event = Event.scalar thread block (some .shared) occurrence ∧
        occurrence.memory = some effect ∧ effect.kind = .store := by
  cases event with
  | branch _ _ _ _ => simp [isPublication]
  | barrier _ => simp [isPublication]
  | exit _ _ => simp [isPublication]
  | scalar issuer block space occurrence =>
    cases space with
    | none => simp [isPublication]
    | some space =>
      cases space with
      | global => simp [isPublication]
      | shared =>
        constructor
        · intro accepted
          cases memory : occurrence.memory with
          | none => simp [isPublication,memory] at accepted
          | some effect =>
            have facts : issuer = thread ∧ effect.kind = .store := by
              simpa [isPublication,memory] using accepted
            exact ⟨block,occurrence,effect,by rw [facts.1],memory,facts.2⟩
        · rintro ⟨b,occ,effect,equal,memory,kind⟩
          obtain ⟨rfl,rfl,_,rfl⟩ := Event.scalar.inj equal
          simp [isPublication,memory,kind]

theorem publication_progress (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (invariant : Control.Invariant s) (thread : Fin n) :
    publicationCredit (s.lanes thread) ≤ publicationCredit ((runWith cfg reads schedule s).state.lanes thread) := by
  have := run_publication_balance cfg reads schedule s invariant thread
  omega

theorem phase_progress (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (invariant : Control.Invariant s) (thread : Fin n) :
    phaseCredit (s.lanes thread) ≤ phaseCredit ((runWith cfg reads schedule s).state.lanes thread) := by
  have := run_phase_balance cfg reads schedule s invariant thread
  omega

theorem completion_at_most_once (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed) :
    completions (runWith cfg reads schedule (start input scratch seeds)).trace ≤ 1 := by
  rw [completion_count cfg reads schedule input scratch seeds ⟨0,cfg.nonempty⟩]
  cases block : ((runWith cfg reads schedule (start input scratch seeds)).state.lanes ⟨0,cfg.nonempty⟩).block <;>
    simp [phaseCredit,block]

/-- Locate an exact dynamic trace index, not merely an equal-valued occurrence. -/
theorem run_index_prefix (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (event : Event n) (position : Nat)
    (atIndex : (runWith cfg reads schedule s).trace[position]? = some event) :
    ∃ earlier selected suffix tail localIndex,
      schedule = earlier ++ selected :: suffix ∧
      (step cfg (reads earlier.length) selected (runWith cfg reads earlier s).state).events[localIndex]? = some event ∧
      (runWith cfg reads schedule s).trace =
        (runWith cfg reads earlier s).trace ++
        (step cfg (reads earlier.length) selected (runWith cfg reads earlier s).state).events ++ tail ∧
      position = (runWith cfg reads earlier s).trace.length + localIndex := by
  induction schedule generalizing reads s position with
  | nil => simp [runWith] at atIndex
  | cons selected rest ih =>
    by_cases first : position < (step cfg (reads 0) selected s).events.length
    · have localIndex : (step cfg (reads 0) selected s).events[position]? = some event := by
        simpa [runWith,List.getElem?_append,first] using atIndex
      exact ⟨[],selected,rest,(runWith cfg (fun i => reads (i+1)) rest (step cfg (reads 0) selected s).state).trace,
        position,rfl,localIndex,by simp [runWith],by simp [runWith]⟩
    · have later : (runWith cfg (fun i => reads (i+1)) rest (step cfg (reads 0) selected s).state).trace[position - (step cfg (reads 0) selected s).events.length]? = some event := by
        simpa [runWith,List.getElem?_append,first] using atIndex
      obtain ⟨earlier,thread,suffix,tail,localIndex,scheduleEq,eventAt,traceEq,indexEq⟩ := ih _ _ _ later
      refine ⟨selected :: earlier,thread,suffix,tail,localIndex,?_,?_,?_,?_⟩
      · simp [scheduleEq]
      · simpa [runWith] using eventAt
      · simpa [runWith,List.append_assoc] using congrArg
          (fun trace => (step cfg (reads 0) selected s).events ++ trace) traceEq
      · simp only [runWith,List.length_append]
        omega

/-- Every writer's store/arrival/completion witnesses are strictly before the
specified load occurrence. Equal event values or repeated PCs need not be unique. -/
theorem load_prefix_at_index (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (input scratch : List Word) (seeds : Fin n → Seed)
    (thread : Fin n) (block : Block) (event : Occurrence) (effect : MemoryEffect) (position : Nat)
    (atIndex : (runWith cfg reads schedule (start input scratch seeds)).trace[position]? =
      some (.scalar thread block (some .shared) event))
    (memory : event.memory = some effect) (load : effect.kind = .load) :
    ∃ earlierTrace suffix,
      (runWith cfg reads schedule (start input scratch seeds)).trace = earlierTrace ++ suffix ∧
      earlierTrace.length ≤ position ∧
      ∀ writer, ∃ store, isPublication writer store = true ∧
        [store,Event.barrier (.arrival (phaseKey cfg) writer),Event.barrier (.completion (phaseKey cfg))] <+ earlierTrace := by
  obtain ⟨earlier,selected,suffix,tail,localIndex,_,eventAt,traceEq,indexEq⟩ :=
    run_index_prefix cfg reads schedule _ _ position atIndex
  have member := List.mem_of_getElem? eventAt
  have blockIs := step_shared_load_loop cfg (reads earlier.length) selected _ thread block event effect member memory load
  have count : completions (runWith cfg reads earlier (start input scratch seeds)).trace = 1 := by
    rw [completion_count cfg reads earlier input scratch seeds selected]
    simp [phaseCredit,blockIs]
  obtain ⟨key,completed⟩ := completion_member (runWith cfg reads earlier (start input scratch seeds)).trace (by omega)
  have keyIs := barrier_key cfg reads earlier input scratch seeds (.completion key) completed
  change key = phaseKey cfg at keyIs
  subst key
  refine ⟨(runWith cfg reads earlier (start input scratch seeds)).trace,
    (step cfg (reads earlier.length) selected (runWith cfg reads earlier (start input scratch seeds)).state).events ++ tail,
    by simpa only [List.append_assoc] using traceEq,by omega,?_⟩
  intro writer
  exact completion_path cfg reads earlier input scratch seeds (phaseKey cfg) writer completed

end Ptx.Scalar.SharedReduction.Machine.History
