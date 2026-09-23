import Ptx.CollectiveMemory
import Ptx.Barrier

/-!
One uniform CTA shared window: aligned strong u32 accesses, one program write per
slot, all participants in mutual scope, generic proxy. The underlying graph
algebra is reused deliberately; instruction origin and the byte-address/owner
connection must be established separately by the fetched-instruction wrapper.
-/
namespace Ptx.SharedBarrierMemory

def laneOf (index : Fin (3 * n)) : Fin n := ⟨index.val / 3, by have := index.isLt; omega⟩
def slotOf (index : Fin (3 * n)) : Fin 3 := ⟨index.val % 3, Nat.mod_lt _ (by decide)⟩
def indexOf (lane : Fin n) (slot : Fin 3) : Fin (3 * n) :=
  ⟨3 * lane.val + slot.val, by have := lane.isLt; have := slot.isLt; omega⟩

@[simp] theorem lane_index (lane : Fin n) (slot : Fin 3) : laneOf (indexOf lane slot) = lane := by
  apply Fin.ext; simp [laneOf, indexOf]; omega

@[simp] theorem slot_index (lane : Fin n) (slot : Fin 3) : slotOf (indexOf lane slot) = slot := by
  apply Fin.ext; simp [slotOf, indexOf]

theorem index_eta (index : Fin (3*n)) : indexOf (laneOf index) (slotOf index) = index := by
  apply Fin.ext; simp [laneOf, slotOf, indexOf]; omega

@[simp] theorem index_eq (a b : Fin n) (x y : Fin 3) :
    indexOf a x = indexOf b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg laneOf h, by simpa using congrArg slotOf h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem forall_index_iff (p : Fin (3*n) → Prop) :
    (∀ index, p index) ↔ ∀ lane slot, p (indexOf lane slot) := by
  constructor
  · exact fun h lane slot => h _
  · intro h index; simpa only [index_eta] using h (laneOf index) (slotOf index)

theorem exists_index_iff (p : Fin (3*n) → Prop) :
    (∃ index, p index) ↔ ∃ lane slot, p (indexOf lane slot) := by
  constructor
  · rintro ⟨index, h⟩; exact ⟨laneOf index, slotOf index, by simpa only [index_eta] using h⟩
  · rintro ⟨lane, slot, h⟩; exact ⟨_, h⟩

def event (old inputs reads : Fin n → Word) (partner : Fin n → Fin n)
    (lane : Fin n) (slot : Fin 3) : Ptx.Occurrence :=
  match slot.val with
  | 0 => ⟨none, 0, ⟨.init, lane.val, old lane⟩⟩
  | 1 => ⟨some lane.val, 0, ⟨.store .relaxed, lane.val, inputs lane⟩⟩
  | _ => ⟨some lane.val, 2, ⟨.load .relaxed, (partner lane).val, reads lane⟩⟩

def graph (old inputs reads : Fin n → Word) (partner : Fin n → Fin n)
    (source : Fin (3*n) → Fin (3*n)) (co : Fin (3*n) → Fin (3*n) → Bool) : Graph (3*n) :=
  ⟨fun i => event old inputs reads partner (laneOf i) (slotOf i), source, co⟩

@[simp] theorem graph_event (old inputs reads : Fin n → Word) (partner source co)
    (lane : Fin n) (slot : Fin 3) :
    (graph old inputs reads partner source co).event (indexOf lane slot) =
      event old inputs reads partner lane slot := by simp [graph]

/-- Coarse phase levels, not timestamps of a total issue-order execution.
Only own-thread before/after edges are extracted from these levels. -/
def phaseOrder (n : Nat) : CollectiveOrder.Certificate (Fin (3*n)) (Option (Fin n)) Unit where
  owner := fun e => if slotOf e = 0 then none else some (laneOf e)
  participates := fun _ t => t.isSome = true
  memoryPos := fun e => if slotOf e = 0 then 0 else if slotOf e = 1 then 1 else 5
  arrivalPos := fun _ _ => 2
  completionPos := fun _ => 3
  resumePos := fun _ _ => 4
  arrival_before_completion := by intros; decide
  completion_before_resume := by intros; decide

def barrierEdge (a b : Fin (3*n)) : Prop := slotOf a = 1 ∧ slotOf b = 2

theorem cross_iff (a b : Fin (3*n)) : (phaseOrder n).cross a b ↔ barrierEdge a b := by
  rw [← index_eta a, ← index_eta b]
  generalize laneOf a = la
  generalize laneOf b = lb
  generalize slotOf a = sa
  generalize slotOf b = sb
  have casesA : sa = 0 ∨ sa = 1 ∨ sa = 2 := by omega
  have casesB : sb = 0 ∨ sb = 1 ∨ sb = 2 := by omega
  rcases casesA with rfl | rfl | rfl <;> rcases casesB with rfl | rfl | rfl
  all_goals simp [CollectiveOrder.Certificate.cross, CollectiveOrder.Certificate.Before,
    CollectiveOrder.Certificate.After, phaseOrder, barrierEdge]

theorem source_choices (old inputs reads : Fin n → Word) (partner source co)
    (sources : (graph old inputs reads partner source co).Sources) (lane : Fin n) :
    source (indexOf lane 2) = indexOf (partner lane) 0 ∨
      source (indexOf lane 2) = indexOf (partner lane) 1 := by
  have h := sources.compatible (indexOf lane 2) (by simp [Graph.read, event])
  change (graph old inputs reads partner source co).write (source (indexOf lane 2)) ∧
    (graph old inputs reads partner source co).sameAddress (source (indexOf lane 2)) (indexOf lane 2) ∧
    ((graph old inputs reads partner source co).event (source (indexOf lane 2))).effect.value =
    ((graph old inputs reads partner source co).event (indexOf lane 2)).effect.value at h
  generalize hi : source (indexOf lane 2) = i at h ⊢
  rw [← index_eta i] at h ⊢
  generalize laneOf i = owner at h ⊢
  generalize slotOf i = slot at h ⊢
  have casesSlot : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
  rcases casesSlot with rfl | rfl | rfl
  all_goals simp [Graph.write, Graph.sameAddress, event] at h
  · exact Or.inl (by have eq : owner = partner lane := Fin.ext h.1; simp [eq])
  · exact Or.inr (by have eq : owner = partner lane := Fin.ext h.1; simp [eq])

theorem source_after_barrier (old inputs reads : Fin n → Word) (partner source co)
    (valid : Graph.Ordered.Valid (graph old inputs reads partner source co) barrierEdge)
    (lane : Fin n) : source (indexOf lane 2) = indexOf (partner lane) 1 := by
  let g := graph old inputs reads partner source co
  have choices := source_choices old inputs reads partner source co valid.sources lane
  rcases choices with initial | written
  · have obsolete := valid.co.initFirst (indexOf (partner lane) 0) (indexOf (partner lane) 1)
      (by simp [Graph.initial, event]) (by simp [Graph.write, event])
      (by simp [Graph.sameAddress, event]) (by simp)
    have ordered : Graph.Ordered.cause g barrierEdge (indexOf (partner lane) 1) (indexOf lane 2) :=
      Graph.Ordered.extra_cause g barrierEdge _ _ (by simp [barrierEdge]) (by simp [g, Graph.sameAddress, event])
    exact False.elim (valid.no_stale _ _ (by simp [Graph.write, event])
      (by simp [Graph.read, event]) (by simp [Graph.sameAddress, event]) ordered
      (by simpa [graph, initial] using obsolete))
  · exact written

theorem read_after_barrier (old inputs reads : Fin n → Word) (partner source co)
    (valid : Graph.Ordered.Valid (graph old inputs reads partner source co) barrierEdge)
    (lane : Fin n) : reads lane = inputs (partner lane) := by
  have source := source_after_barrier old inputs reads partner source co valid lane
  have h := Graph.value_of_source _ valid.sources _ (indexOf lane 2)
    (by simp [Graph.read, event]) source
  simpa [event] using h

def witnessSource (partner : Fin n → Fin n) (fresh : Bool) (i : Fin (3*n)) : Fin (3*n) :=
  indexOf (partner (laneOf i)) (if fresh then 1 else 0)

def witnessCo (a b : Fin (3*n)) : Bool :=
  laneOf a == laneOf b && slotOf a == 0 && slotOf b == 1

def freshGraph (old inputs : Fin n → Word) (partner : Fin n → Fin n) : Graph (3*n) :=
  graph old inputs (fun lane => inputs (partner lane)) partner (witnessSource partner true) witnessCo

def staleGraph (old inputs : Fin n → Word) (partner : Fin n → Fin n) : Graph (3*n) :=
  graph old inputs (fun lane => old (partner lane)) partner (witnessSource partner false) witnessCo

def localUpper (a b : Fin (3*n)) : Prop :=
  laneOf a = laneOf b ∧ slotOf a = 1 ∧ slotOf b = 2

def staleRank (i : Fin (3*n)) : Nat :=
  if slotOf i = 0 then 0 else if slotOf i = 1 then 2 else 1

set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local macro "by_slots" : tactic => `(tactic|
  (simp [forall_index_iff, exists_index_iff, Fin.forall_fin_succ, Fin.exists_fin_succ,
    Graph.Ordered.baseEdge, Graph.baseEdge, Graph.sync, Graph.releasePattern,
    Graph.acquirePattern, Graph.observation, Graph.rf, Graph.morallyStrong,
    Graph.initial, Graph.release, Graph.acquire, Graph.po, Graph.sameAddress,
    Graph.read, Graph.write, Graph.coherence, Graph.upperCause, Graph.locationEdge,
    Graph.communication, freshGraph, staleGraph, graph, event, witnessSource,
    witnessCo, barrierEdge, localUpper, staleRank] <;>
    (repeat' (first | intro _ | constructor)) <;>
    (try simp_all [Fin.ext_iff]) <;> omega))

theorem fresh_valid (old inputs : Fin n → Word) (partner : Fin n → Fin n) :
    Graph.Ordered.Valid (freshGraph old inputs partner) barrierEdge := by
  apply Graph.Ordered.valid_of_certificate (upper := barrierEdge) (rank := fun i => (slotOf i).val)
  exact {
    sources := ⟨by by_slots⟩
    co := ⟨by by_slots, by by_slots, by by_slots, by by_slots, by by_slots⟩
    edge_included := by by_slots
    upper_trans := by by_slots
    upper_irrefl := by by_slots
    coherence_cause := by by_slots
    no_future := by by_slots
    no_stale := by by_slots
    location_rank := by by_slots
  }

/-- Without barrier order, all readers can choose the old partner word when
there are no own-slot reads. This is a relational graph witness, not an SC run. -/
theorem stale_without_barrier (old inputs : Fin n → Word) (partner : Fin n → Fin n)
    (other : ∀ lane, partner lane ≠ lane) : (staleGraph old inputs partner).Valid := by
  apply Graph.valid_of_certificate (upper := localUpper) (rank := staleRank)
  exact {
    sources := ⟨by by_slots⟩
    co := ⟨by by_slots, by by_slots, by by_slots, by by_slots, by by_slots⟩
    edge_included := by by_slots
    upper_trans := by by_slots
    upper_irrefl := by by_slots
    coherence_cause := by by_slots
    no_future := by by_slots
    no_stale := by by_slots
    location_rank := by by_slots
  }

/-- Source identity, not just coincident equal values, excludes the old graph. -/
theorem stale_with_barrier_invalid (old inputs : Fin n → Word)
    (partner : Fin n → Fin n) (lane : Fin n) :
    ¬Graph.Ordered.Valid (staleGraph old inputs partner) barrierEdge := by
  intro valid
  have h := source_after_barrier old inputs (fun lane => old (partner lane)) partner
    (witnessSource partner false) witnessCo valid lane
  simp [witnessSource] at h

theorem fresh_phase_valid (old inputs : Fin n → Word) (partner : Fin n → Fin n) :
    Graph.Ordered.Valid (freshGraph old inputs partner) (phaseOrder n).cross :=
  Graph.Ordered.valid_restrict _ (fun a b h => (cross_iff a b).mp h)
    (fresh_valid old inputs partner)

theorem read_after_phase (old inputs reads : Fin n → Word) (partner source co)
    (valid : Graph.Ordered.Valid (graph old inputs reads partner source co) (phaseOrder n).cross)
    (lane : Fin n) : reads lane = inputs (partner lane) :=
  read_after_barrier old inputs reads partner source co
    (Graph.Ordered.valid_restrict _ (fun a b h => (cross_iff a b).mpr h) valid) lane

/-- A selected two-warp launch with 32 lanes per warp, not a universal PTX
claim about the machine-dependent WARP_SZ constant. -/
def partner64 (lane : Fin 64) : Fin 64 :=
  ⟨(lane.val + 32) % 64, Nat.mod_lt _ (by decide)⟩

def warp32 (lane : Fin 64) : Fin 2 :=
  ⟨lane.val / 32, by have := lane.isLt; omega⟩

def twoWarps : Barrier.WarpPartition 64 2 where
  warpOf := warp32
  inhabited := by
    intro warp
    refine ⟨⟨32*warp.val, by have := warp.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp [warp32]

theorem partner64_other (lane : Fin 64) : partner64 lane ≠ lane := by
  intro same
  have h := congrArg Fin.val same
  simp only [partner64] at h
  have := lane.isLt
  omega

theorem partner64_other_warp (lane : Fin 64) : warp32 (partner64 lane) ≠ warp32 lane := by
  intro same
  have h := congrArg Fin.val same
  simp only [warp32, partner64] at h
  have := lane.isLt
  omega

theorem partner64_involution (lane : Fin 64) : partner64 (partner64 lane) = lane := by
  apply Fin.ext
  simp only [partner64]
  have := lane.isLt
  omega

theorem two_warp_graphs (old inputs : Fin 64 → Word) :
    Graph.Ordered.Valid (freshGraph old inputs partner64) (phaseOrder 64).cross ∧
    (staleGraph old inputs partner64).Valid ∧
    ¬Graph.Ordered.Valid (staleGraph old inputs partner64) barrierEdge :=
  ⟨fresh_phase_valid old inputs partner64, stale_without_barrier old inputs partner64 partner64_other,
    stale_with_barrier_invalid old inputs partner64 0⟩

end Ptx.SharedBarrierMemory
