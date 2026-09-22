import Ptx.SharedVector

/-! A relational witness for disjoint vector-add lanes in one shared allocation.
Candidate input words remain parameters until source compatibility fixes them.
The six labels per lane include three initial words and three memory effects. -/
namespace Ptx.Scalar.SharedVectorMemory

def laneOf (index : Fin (6 * n)) : Fin n := ⟨index.val / 6, by have := index.isLt; omega⟩
def slotOf (index : Fin (6 * n)) : Fin 6 := ⟨index.val % 6, Nat.mod_lt _ (by decide)⟩
def indexOf (lane : Fin n) (slot : Fin 6) : Fin (6 * n) :=
  ⟨6 * lane.val + slot.val, by have := lane.isLt; have := slot.isLt; omega⟩

@[simp] theorem lane_index (lane : Fin n) (slot : Fin 6) : laneOf (indexOf lane slot) = lane := by
  apply Fin.ext; simp [laneOf,indexOf]; omega
@[simp] theorem slot_index (lane : Fin n) (slot : Fin 6) : slotOf (indexOf lane slot) = slot := by
  apply Fin.ext; simp [slotOf,indexOf]
theorem index_eta (index : Fin (6 * n)) : indexOf (laneOf index) (slotOf index) = index := by
  apply Fin.ext; simp [laneOf,slotOf,indexOf]; omega

@[simp] theorem index_eq (a b : Fin n) (x y : Fin 6) :
    indexOf a x = indexOf b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg laneOf h, by simpa using congrArg slotOf h⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem forall_index_iff (p : Fin (6 * n) → Prop) :
    (∀ index, p index) ↔ ∀ lane slot, p (indexOf lane slot) := by
  constructor
  · exact fun h lane slot => h _
  · intro h index; simpa only [index_eta] using h (laneOf index) (slotOf index)

theorem exists_index_iff (p : Fin (6 * n) → Prop) :
    (∃ index, p index) ↔ ∃ lane slot, p (indexOf lane slot) := by
  constructor
  · rintro ⟨index,h⟩; exact ⟨laneOf index,slotOf index,by simpa only [index_eta] using h⟩
  · rintro ⟨lane,slot,h⟩; exact ⟨_,h⟩

def event (memory : List Word) (left right : Fin n → Word) (lane : Fin n) (slot : Fin 6) : Ptx.Occurrence :=
  match slot.val with
  | 0 => ⟨none,3*lane.val,⟨.init,3*lane.val,memory[3*lane.val]!⟩⟩
  | 1 => ⟨none,3*lane.val+1,⟨.init,3*lane.val+1,memory[3*lane.val+1]!⟩⟩
  | 2 => ⟨none,3*lane.val+2,⟨.init,3*lane.val+2,memory[3*lane.val+2]!⟩⟩
  | 3 => ⟨some lane.val,0,⟨.load .relaxed,3*lane.val,left lane⟩⟩
  | 4 => ⟨some lane.val,1,⟨.load .relaxed,3*lane.val+1,right lane⟩⟩
  | _ => ⟨some lane.val,3,⟨.store .relaxed,3*lane.val+2,left lane + right lane⟩⟩

@[simp] theorem event0 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 0 = ⟨none,3*lane.val+0,⟨.init,3*lane.val+0,memory[3*lane.val+0]!⟩⟩ := rfl

@[simp] theorem event1 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 1 = ⟨none,3*lane.val+1,⟨.init,3*lane.val+1,memory[3*lane.val+1]!⟩⟩ := rfl

@[simp] theorem event2 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 2 = ⟨none,3*lane.val+2,⟨.init,3*lane.val+2,memory[3*lane.val+2]!⟩⟩ := rfl

@[simp] theorem event3 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 3 = ⟨some lane.val,0,⟨.load .relaxed,3*lane.val,left lane⟩⟩ := rfl

@[simp] theorem event4 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 4 = ⟨some lane.val,1,⟨.load .relaxed,3*lane.val+1,right lane⟩⟩ := rfl

@[simp] theorem event5 (memory : List Word) (left right : Fin n → Word) (lane : Fin n) :
    event memory left right lane 5 = ⟨some lane.val,3,⟨.store .relaxed,3*lane.val+2,left lane+right lane⟩⟩ := rfl

def graph (memory : List Word) (left right : Fin n → Word)
    (source : Fin (6*n) → Fin (6*n)) (co : Fin (6*n) → Fin (6*n) → Bool) : Graph (6*n) :=
  ⟨fun i => event memory left right (laneOf i) (slotOf i),source,co⟩

@[simp] theorem graph_event (memory : List Word) (left right : Fin n → Word)
    (source co) (lane : Fin n) (slot : Fin 6) :
    (graph memory left right source co).event (indexOf lane slot) = event memory left right lane slot := by
  simp [graph]

def witnessSource (i : Fin (6*n)) : Fin (6*n) :=
  indexOf (laneOf i) (if slotOf i = 4 then 1 else 0)
def witnessCo (a b : Fin (6*n)) : Bool :=
  laneOf a == laneOf b && slotOf a == 2 && slotOf b == 5
def witness (memory : List Word) : Graph (6*n) :=
  graph memory (fun lane => memory[3*lane.val]!) (fun lane => memory[3*lane.val+1]!)
    witnessSource witnessCo

def upper (a b : Fin (6*n)) : Prop :=
  laneOf a = laneOf b ∧ 3 ≤ (slotOf a).val ∧ (slotOf a).val < (slotOf b).val

set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local macro "by_slots" : tactic => `(tactic|
  (simp [forall_index_iff, exists_index_iff, Fin.forall_fin_succ, Fin.exists_fin_succ, Graph.baseEdge, Graph.sync,
    Graph.releasePattern, Graph.acquirePattern, Graph.observation, Graph.rf,
    Graph.morallyStrong, Graph.initial, Graph.release, Graph.acquire, Graph.po,
    Graph.sameAddress, Graph.read, Graph.write, Graph.coherence, Graph.upperCause,
    Graph.locationEdge, Graph.communication, witness, graph, event, witnessSource,
    witnessCo, upper] <;>
    (repeat' (first | intro _ | constructor)) <;>
    (try simp_all only [Fin.ext_iff]) <;> omega))

theorem witness_valid (memory : List Word) : (witness (n:=n) memory).Valid := by
  apply Graph.valid_of_certificate (upper := upper) (rank := Fin.val)
  exact {
    sources := ⟨by by_slots⟩
    co := ⟨by by_slots,by by_slots,by by_slots,by by_slots,by by_slots⟩
    edge_included := by by_slots
    upper_trans := by by_slots
    upper_irrefl := by by_slots
    coherence_cause := by by_slots
    no_future := by by_slots
    no_stale := by by_slots
    location_rank := by by_slots
  }

/-- Every noninitial label is the label extracted from an actual shared execution,
including the register-computed store. The footprint projection omits untouched
allocation words beyond the first three words per lane. -/
theorem shared_trace_labels (memory : List Word) (registers : Fin n → Nat → Word)
    (dispatches : List (Fin n)) (extent : 3*n ≤ memory.length)
    (noWrap : 12*n < 2^64)
    (completed : SharedVector.Complete (SharedVector.execute dispatches
      (SharedVector.initial memory registers))) (lane : Fin n) :
    SharedVector.laneTrace lane (SharedVector.trace dispatches
      (SharedVector.initial memory registers)) =
      [(witness memory).event (indexOf lane 3),
       (witness memory).event (indexOf lane 4),
       (witness memory).event (indexOf lane 5)] := by
  rw [SharedVector.completed_trace memory registers dispatches extent noWrap completed lane]
  simp [SharedVector.remaining, SharedVector.left, SharedVector.right,
    SharedVector.output, SharedVector.sum, witness]

/-- A single constructive execution and relational graph share exactly the
same per-lane program events. This is a restricted existence witness, not a
completeness assertion for dependent PTX programs or scheduler fairness. -/
theorem verified_shared_execution (memory : List Word) (registers : Fin n → Nat → Word)
    (extent : 3*n ≤ memory.length) (noWrap : 12*n < 2^64) :
    ∃ dispatches : List (Fin n),
      dispatches.length = 5*n ∧
      SharedVector.Execution dispatches (SharedVector.initial memory registers)
        (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      SharedVector.Complete (SharedVector.execute dispatches (SharedVector.initial memory registers)) ∧
      (∀ lane : Fin n,
        (SharedVector.execute dispatches (SharedVector.initial memory registers)).memory[SharedVector.output lane]! =
          SharedVector.sum memory lane) ∧
      (witness (n:=n) memory).Valid ∧
      ∀ lane : Fin n, SharedVector.laneTrace lane (SharedVector.trace dispatches
        (SharedVector.initial memory registers)) =
        [(witness memory).event (indexOf lane 3),
         (witness memory).event (indexOf lane 4),
         (witness memory).event (indexOf lane 5)] := by
  refine ⟨SharedVector.schedule n, SharedVector.schedule_length,
    SharedVector.execute_faithful memory _ _ extent noWrap (SharedVector.initial_invariant ..),
    SharedVector.schedule_complete memory registers,
    SharedVector.completed_correct memory registers extent _ (SharedVector.schedule_complete memory registers),
    witness_valid memory, ?_⟩
  exact shared_trace_labels memory registers _ extent noWrap (SharedVector.schedule_complete memory registers)

/-- Initial labels name the actual initialized allocation cells; bounds exclude
out-of-range `getElem!` defaults in any execution-level use of the graph. -/
theorem initial_labels (memory : List Word) (extent : 3*n ≤ memory.length)
    (lane : Fin n) (slot : Fin 3) :
    (witness memory).event (indexOf lane ⟨slot.val, by omega⟩) =
      ⟨none,3*lane.val+slot.val,
        ⟨.init,3*lane.val+slot.val,memory[3*lane.val+slot.val]!⟩⟩ ∧
      3*lane.val+slot.val < memory.length := by
  have := lane.isLt
  have := slot.isLt
  rcases (show slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 by omega) with h | h | h
  all_goals simp [witness,event,h]; omega

/-- Reads of input cells have exactly one possible writing event. This proves
source uniqueness across every lane, not just within a selected lane. -/
theorem input_writer (memory : List Word) (left right : Fin n → Word) (source co)
    (lane : Fin n) (i : Fin (6*n)) :
    ((graph memory left right source co).write i ∧
      (graph memory left right source co).sameAddress i (indexOf lane 3) → i = indexOf lane 0) ∧
    ((graph memory left right source co).write i ∧
      (graph memory left right source co).sameAddress i (indexOf lane 4) → i = indexOf lane 1) := by
  rw [← index_eta i]
  generalize laneOf i = owner
  generalize slotOf i = slot
  have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 ∨ slot = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Graph.write,Graph.sameAddress]
  all_goals try simp only [Fin.ext_iff]
  all_goals omega

/-- Source compatibility alone fixes all candidate input words. It does not
assume the desired sum or rely on a weaker selected notion of validity. -/
theorem input_sources (memory : List Word) (left right : Fin n → Word) (source co)
    (sources : (graph memory left right source co).Sources) (lane : Fin n) :
    left lane = memory[3*lane.val]! ∧ right lane = memory[3*lane.val+1]! := by
  have hl := sources.compatible (indexOf lane 3) (by simp [Graph.read])
  have hr := sources.compatible (indexOf lane 4) (by simp [Graph.read])
  have sl := (input_writer memory left right source co lane _).1 ⟨hl.1,hl.2.1⟩
  have sr := (input_writer memory left right source co lane _).2 ⟨hr.1,hr.2.1⟩
  rw [sl] at hl
  rw [sr] at hr
  exact ⟨by simpa using hl.2.2.symm, by simpa using hr.2.2.symm⟩

/-- Compatibility fixes every event value, making the candidate label table
identical to the execution-backed witness. Sources and coherence themselves may
still differ; this theorem does not identify candidate relations. -/
theorem candidate_event_eq (memory : List Word) (left right : Fin n → Word) (source co)
    (sources : (graph memory left right source co).Sources) (i : Fin (6*n)) :
    (graph memory left right source co).event i = (witness memory).event i := by
  obtain ⟨hl,hr⟩ := input_sources memory left right source co sources (laneOf i)
  simp [graph,witness,event,hl,hr]

/-- Any source-compatible candidate has exactly the labels of every completed
actual shared execution. This connects the universal candidate result to the
instruction semantics rather than merely postulating correct output labels. -/
theorem candidate_shared_trace_labels (memory : List Word) (left right : Fin n → Word)
    (source co) (sources : (graph memory left right source co).Sources)
    (registers : Fin n → Nat → Word) (dispatches : List (Fin n))
    (extent : 3*n ≤ memory.length) (noWrap : 12*n < 2^64)
    (completed : SharedVector.Complete (SharedVector.execute dispatches
      (SharedVector.initial memory registers))) (lane : Fin n) :
    SharedVector.laneTrace lane (SharedVector.trace dispatches
      (SharedVector.initial memory registers)) =
      [(graph memory left right source co).event (indexOf lane 3),
       (graph memory left right source co).event (indexOf lane 4),
       (graph memory left right source co).event (indexOf lane 5)] := by
  simp only [candidate_event_eq memory left right source co sources]
  exact shared_trace_labels memory registers dispatches extent noWrap completed lane

/-- Register-store output agrees with the original inputs in every source-
compatible candidate, regardless of candidate coherence choices. -/
theorem candidate_output (memory : List Word) (left right : Fin n → Word) (source co)
    (sources : (graph memory left right source co).Sources) (lane : Fin n) :
    ((graph memory left right source co).event (indexOf lane 5)).effect.value =
      SharedVector.sum memory lane := by
  obtain ⟨hl,hr⟩ := input_sources memory left right source co sources lane
  simp [SharedVector.sum,SharedVector.left,SharedVector.right,hl,hr]

end Ptx.Scalar.SharedVectorMemory
