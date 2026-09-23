import Ptx.SharedBarrierProgram
import Ptx.SharedBarrierEnvironment
import Ptx.SharedBarrierMemory
import Ptx.SharedBarrierHistory
import Ptx.ScopedMemory

/-! Connect actual fetched candidate/concrete executions to the restricted
shared-window graph. Candidate observations stay arbitrary until memory validity
forces their sources. This straight-line fragment has one completed phase.
-/
namespace Ptx.SharedBarrier
open List

def memoryOccurrence (effect : MemoryEvent n) : Ptx.Occurrence :=
  ⟨some effect.thread.val, effect.pc,
    ⟨match effect.kind with | .store => .store .relaxed | .load => .load .relaxed,
      effect.address.toNat / 4, effect.value⟩⟩

def projectMemory : Event n → Option Ptx.Occurrence
  | .memory effect => some (memoryOccurrence effect)
  | _ => none

def graphTrace (config : Config n) (initial : Initial n) (observations : Fin n → Word)
    (source : Fin (3*n) → Fin (3*n)) (co : Fin (3*n) → Fin (3*n) → Bool) : List Ptx.Occurrence :=
  let g := SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co
  (schedule n).map (fun lane => g.event (SharedBarrierMemory.indexOf lane 1)) ++
    (schedule n).map (fun lane => g.event (SharedBarrierMemory.indexOf lane 2))

theorem project_store (config : Config n) (initial : Initial n) (observations : Fin n → Word)
    (source co) (lane : Fin n) :
    projectMemory (storeEvent config initial lane) =
      some ((SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co).event
        (SharedBarrierMemory.indexOf lane 1)) := by
  simp [projectMemory, memoryOccurrence, storeEvent, SharedBarrierMemory.event,
    slotAddress_toNat config]

theorem project_read (config : Config n) (initial : Initial n) (observations : Fin n → Word)
    (source co) (lane : Fin n) :
    projectMemory (readEvent config initial (fun t => some (observations t)) lane) =
      some ((SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co).event
        (SharedBarrierMemory.indexOf lane 2)) := by
  simp [projectMemory, memoryOccurrence, readEvent, readValue, SharedBarrierMemory.event,
    slotAddress_toNat config]

/-- No program memory event is invented or omitted by the graph projection. -/
theorem candidate_graph_trace (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co) :
    (runWith config (fun t => some (observations t)) (start config initial) (fullSchedule n)).trace.filterMap
        projectMemory = graphTrace config initial observations source co := by
  rw [canonical_execution]
  simp only [canonicalTrace, List.filterMap_append, List.filterMap_map]
  simp only [Function.comp_def, project_store config initial observations source co,
    project_read config initial observations source co]
  have erased : (schedule n).filterMap (fun _ => (none : Option Ptx.Occurrence)) = [] := by simp
  simp [graphTrace, projectMemory, arrivalEvent, completionEvent, exitEvent,
    List.filterMap_eq_map', List.filterMap_cons, erased]

/-- The actual trace supplies the store, own arrival, common completion and
partner read in order. Resumption is the state transition at that completion,
not a fictitious extra PTX instruction. -/
theorem phase_path_in_trace (config : Config n) (initial : Initial n)
    (reads : Fin n → Option Word) (writer reader : Fin n) :
    [storeEvent config initial writer, arrivalEvent config writer,
      completionEvent config, readEvent config initial reads reader] <+
      (runWith config reads (start config initial) (fullSchedule n)).trace := by
  rw [canonical_execution]
  have hs : [storeEvent config initial writer] <+ (schedule n).map (storeEvent config initial) :=
    List.singleton_sublist.mpr (List.mem_map.mpr ⟨writer, schedule_contains writer, rfl⟩)
  have ha : [arrivalEvent config writer] <+ (schedule n).map (arrivalEvent config) :=
    List.singleton_sublist.mpr (List.mem_map.mpr ⟨writer, schedule_contains writer, rfl⟩)
  have hr : [readEvent config initial reads reader] <+ (schedule n).map (readEvent config initial reads) :=
    List.singleton_sublist.mpr (List.mem_map.mpr ⟨reader, schedule_contains reader, rfl⟩)
  have path := (((hs.append ha).append (List.Sublist.refl [completionEvent config])).append hr).append
    (List.nil_sublist ((schedule n).map exitEvent))
  simpa [canonicalTrace] using path

theorem cross_origin (config : Config n) (initial : Initial n) (observations : Fin n → Word)
    (a b : Fin (3*n)) (edge : (SharedBarrierMemory.phaseOrder n).cross a b) :
    ∃ writer reader : Fin n,
      a = SharedBarrierMemory.indexOf writer 1 ∧ b = SharedBarrierMemory.indexOf reader 2 ∧
      [storeEvent config initial writer, arrivalEvent config writer,
        completionEvent config, readEvent config initial (fun t => some (observations t)) reader] <+
        (runWith config (fun t => some (observations t)) (start config initial) (fullSchedule n)).trace := by
  obtain ⟨ha, hb⟩ := (SharedBarrierMemory.cross_iff a b).mp edge
  refine ⟨SharedBarrierMemory.laneOf a, SharedBarrierMemory.laneOf b, ?_, ?_,
    phase_path_in_trace config initial _ _ _⟩
  · simpa [ha] using (SharedBarrierMemory.index_eta a).symm
  · simpa [hb] using (SharedBarrierMemory.index_eta b).symm

/-- This is a universal result over proposed observations and memory relations,
not merely a calculation of the selected concrete arena execution. -/
theorem candidate_publication (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co)
    (valid : Graph.Ordered.Valid
      (SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co)
      (SharedBarrierMemory.phaseOrder n).cross) (lane : Fin n) :
    ((runWith config (fun t => some (observations t)) (start config initial) (fullSchedule n)).state.threads lane).registers 1 =
      initial.inputs (config.partner lane) := by
  have result := ((candidate_completed config initial observations).2.1 lane).2.2
  exact result.trans (SharedBarrierMemory.read_after_phase initial.old initial.inputs observations
    config.partner source co valid lane)

/-- Every completed candidate schedule has the same result, with no restriction
on the dispatch order and no desired read value in the execution premise. -/
theorem completed_candidate_publication (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co) (dispatches : List (Fin n))
    (valid : Graph.Ordered.Valid
      (SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co)
      (SharedBarrierMemory.phaseOrder n).cross)
    (completed : ∀ lane,
      ((runWith config (fun t => some (observations t)) (start config initial) dispatches).state.threads lane).halted = true) :
    ∀ lane,
      ((runWith config (fun t => some (observations t)) (start config initial) dispatches).state.threads lane).registers 1 =
        initial.inputs (config.partner lane) ∧
      Control.memoryCount .store (runWith config (fun t => some (observations t))
        (start config initial) dispatches).trace lane = 1 ∧
      Control.memoryCount .load (runWith config (fun t => some (observations t))
        (start config initial) dispatches).trace lane = 1 := by
  intro lane
  refine ⟨?_, Frame.halted_memory_counts config initial _ dispatches lane (completed lane)⟩
  exact (Frame.halted_output config initial observations dispatches lane (completed lane)).trans
    (SharedBarrierMemory.read_after_phase initial.old initial.inputs observations
      config.partner source co valid lane)

/-- Every extra memory-order edge has its exact keyed instruction trace path,
for every completed dispatch order rather than only the existence witness. -/
theorem completed_cross_origin (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (dispatches : List (Fin n))
    (completed : ∀ lane,
      ((runWith config (fun t => some (observations t)) (start config initial) dispatches).state.threads lane).halted = true)
    (a b : Fin (3*n)) (edge : (SharedBarrierMemory.phaseOrder n).cross a b) :
    ∃ writer reader : Fin n,
      a = SharedBarrierMemory.indexOf writer 1 ∧ b = SharedBarrierMemory.indexOf reader 2 ∧
      [storeEvent config initial writer, arrivalEvent config writer,
        completionEvent config, readEvent config initial (fun t => some (observations t)) reader] <+
        (runWith config (fun t => some (observations t)) (start config initial) dispatches).trace := by
  obtain ⟨ha, hb⟩ := (SharedBarrierMemory.cross_iff a b).mp edge
  let writer := SharedBarrierMemory.laneOf a
  let reader := SharedBarrierMemory.laneOf b
  have count := (Frame.halted_memory_counts config initial (fun t => some (observations t))
    dispatches reader (completed reader)).2
  obtain ⟨effect, member, kind, thread⟩ := History.memory_member
    (runWith config (fun t => some (observations t)) (start config initial) dispatches).trace
    .load reader (by omega)
  have path := History.load_path config initial observations dispatches effect kind member writer
  have fields := Frame.trace_memory_fields config initial observations dispatches member
  have effectEq : Event.memory effect =
      readEvent config initial (fun t => some (observations t)) reader := by
    rcases fields with store | load
    · simp only [storeEvent, Event.memory.injEq] at store
      have impossible := congrArg MemoryEvent.kind store
      simp [kind] at impossible
    · simpa [thread] using load
  rw [effectEq] at path
  refine ⟨writer, reader, ?_, ?_, path⟩
  · simpa [writer, ha] using (SharedBarrierMemory.index_eta a).symm
  · simpa [reader, hb] using (SharedBarrierMemory.index_eta b).symm

/-- The same event table equipped with the actual one-CTA topology and explicit
CTA scopes. Initial writes do not impersonate program participants. -/
def scopedGraph (config : Config n) (initial : Initial n) (observations : Fin n → Word)
    (source : Fin (3*n) → Fin (3*n)) (co : Fin (3*n) → Fin (3*n) → Bool) : ScopedGraph (3*n) :=
  ⟨SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co,
    location config.cta, fun _ => .cta⟩

theorem all_in_scope (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co) :
    (scopedGraph config initial observations source co).AllInScope := by
  intro a b ha hb
  rw [← SharedBarrierMemory.index_eta a] at ha ⊢
  rw [← SharedBarrierMemory.index_eta b] at hb ⊢
  generalize SharedBarrierMemory.laneOf a = la at *
  generalize SharedBarrierMemory.laneOf b = lb at *
  generalize SharedBarrierMemory.slotOf a = sa at *
  generalize SharedBarrierMemory.slotOf b = sb at *
  have ca : sa = 0 ∨ sa = 1 ∨ sa = 2 := by omega
  have cb : sb = 0 ∨ sb = 1 ∨ sb = 2 := by omega
  rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
  all_goals simp_all [scopedGraph, Graph.initial, SharedBarrierMemory.event,
    ScopedGraph.mutualScope, location, Scope.includes, ThreadLocation.sameCTA,
    ThreadLocation.sameCluster]

/-- Mutual scope is established from topology, so the whole-word observation
rule used by the graph agrees with the scoped rule on this fragment. -/
theorem observation_scope (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co) (a b : Fin (3*n)) :
    (scopedGraph config initial observations source co).observation a b ↔
      (SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co).observation a b :=
  ScopedGraph.observation_legacy (all_in_scope config initial observations source co)

/-- Initial graph labels name exactly the supplied arena contents. -/
theorem initial_graph_label (config : Config n) (initial : Initial n)
    (observations : Fin n → Word) (source co) (lane : Fin n) :
    (SharedBarrierMemory.graph initial.old initial.inputs observations config.partner source co).event
      (SharedBarrierMemory.indexOf lane 0) =
      ⟨none, 0, ⟨.init, lane.val, (start config initial).arena.words lane⟩⟩ := by
  simp [SharedBarrierMemory.event, start]

/-- The concrete witness and its candidate description have identical effects
and final state after the explicit four-stage schedule. -/
theorem concrete_eq_candidate (config : Config n) (initial : Initial n) :
    run config (start config initial) (fullSchedule n) =
      runWith config (fun t => some (initial.inputs (config.partner t)))
        (start config initial) (fullSchedule n) := by
  simp only [run, canonical_execution]
  rfl

/-- The allocation descriptor is preserved across every step; only contents can
change. This is internal arena lifetime, not an external allocator guarantee. -/
theorem step_environment (config : Config n) (override : Option Word) (thread : Fin n)
    (state : State n) :
    (stepWith config override thread state).state.arena.environment = state.arena.environment := by
  have owner := (Frame.step_frame config override thread state).2.2
  unfold Arena.environment
  rw [owner]

/-- Every access in every finite trace passes the same initial allocation's
checker, including prefixes that do not complete the program. -/
theorem trace_accessible (config : Config n) (reads : Fin n → Option Word)
    (state : State n) (dispatches : List (Fin n)) (effect : MemoryEvent n)
    (member : Event.memory effect ∈ (runWith config reads state dispatches).trace) :
    state.arena.environment.accessible (location effect.cta effect.thread.val)
      effect.kind.accessKind (sharedAddress effect.address) 4 false := by
  induction dispatches generalizing state with
  | nil => simp [runWith] at member
  | cons thread rest ih =>
    simp only [runWith, List.mem_append] at member
    rcases member with first | later
    · exact emitted_accessible config (reads thread) thread state effect first
    · have safe := ih _ later
      rw [step_environment] at safe
      exact safe

/-- An actual completed instruction execution, a fully valid memory witness,
exact graph labels, access safety and nonvacuous register result together. -/
theorem verified_execution (config : Config n) (initial : Initial n) :
    ∃ dispatches : List (Fin n), ∃ result : Execution n,
      dispatches.length = 4*n ∧
      Runs config (fun _ => none) (start config initial) dispatches result ∧
      (∀ thread, (result.state.threads thread).halted = true ∧
        (result.state.threads thread).pc = 3 ∧
        (result.state.threads thread).registers 1 = initial.inputs (config.partner thread)) ∧
      result.state.arena.words = initial.inputs ∧
      result.state.barrier = Barrier.reset 1 ∧
      Graph.Ordered.Valid (SharedBarrierMemory.freshGraph initial.old initial.inputs config.partner)
        (SharedBarrierMemory.phaseOrder n).cross ∧
      result.trace.filterMap projectMemory =
        graphTrace config initial (fun t => initial.inputs (config.partner t))
          (SharedBarrierMemory.witnessSource config.partner true) SharedBarrierMemory.witnessCo ∧
      (∀ effect, Event.memory effect ∈ result.trace →
        (start config initial).arena.environment.accessible (location effect.cta effect.thread.val)
          effect.kind.accessKind (sharedAddress effect.address) 4 false) := by
  refine ⟨fullSchedule n, run config (start config initial) (fullSchedule n),
    fullSchedule_length n, (concrete_completed config initial).1,
    (concrete_completed config initial).2.1,
    (concrete_completed config initial).2.2.1,
    (concrete_completed config initial).2.2.2,
    SharedBarrierMemory.fresh_phase_valid initial.old initial.inputs config.partner, ?_, ?_⟩
  · rw [concrete_eq_candidate]
    exact candidate_graph_trace config initial _ _ _
  · exact fun effect member => trace_accessible config (fun _ => none) _ _ effect member

/-- A concrete selected two-warp configuration uses the proved partner map. -/
def twoWarpConfig (cta : Nat) : Config 64 :=
  ⟨cta, SharedBarrierMemory.partner64, by decide, by decide⟩

theorem two_warp_verified (cta : Nat) (initial : Initial 64) :
    ∃ result : Execution 64,
      Runs (twoWarpConfig cta) (fun _ => none) (start (twoWarpConfig cta) initial)
        (fullSchedule 64) result ∧
      (∀ thread, (result.state.threads thread).halted = true ∧
        (result.state.threads thread).registers 1 = initial.inputs (SharedBarrierMemory.partner64 thread)) ∧
      (∀ thread, SharedBarrierMemory.warp32 (SharedBarrierMemory.partner64 thread) ≠
        SharedBarrierMemory.warp32 thread) := by
  refine ⟨run (twoWarpConfig cta) (start (twoWarpConfig cta) initial) (fullSchedule 64),
    (concrete_completed _ _).1, ?_, SharedBarrierMemory.partner64_other_warp⟩
  intro thread
  have done := (concrete_completed (twoWarpConfig cta) initial).2.1 thread
  exact ⟨done.1, done.2.2⟩

end Ptx.SharedBarrier
