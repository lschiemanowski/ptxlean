import Ptx.ScalarTraceMemory
import Ptx.ComputedPublicationWitness

/-! Recover the computed publication family from the reusable projection. There
is no independently supplied event table in this construction. -/
namespace Ptx.Scalar.ComputedPublication.Projected
open Ptx.TraceMemory

def initialWords (initial : Initial) : List (TraceMemory.Initial 1) :=
  [⟨⟨0,0⟩,initial.x⟩, ⟨⟨0,1⟩,initial.y⟩, ⟨⟨0,2⟩,initial.old⟩, ⟨⟨0,3⟩,0⟩]

def events (initial : Initial) (order : LoadOrder) (left right flag payload : Word) :
    List Ptx.Occurrence :=
  TraceMemory.events (initialWords initial) [0,1]
    (fun thread => if thread = 0 then (producerRun initial left right).trace
      else (consumerRun initial order flag payload).trace)
    (fun thread => Ordered.access (if thread = 0 then producer else consumer order))

theorem events_unique (initial order left right flag payload) :
    ((events initial order left right flag payload).map TraceMemory.identity).Nodup := by
  apply TraceMemory.events_unique
  · simp [initialWords, List.nodup_cons, Location.mk.injEq]
  · decide

theorem events_recover (initial order left right flag payload) :
    events initial order left right flag payload =
      ComputedPublication.events initial order left right flag payload := by
  simp only [events, TraceMemory.events, List.flatMap_cons, List.flatMap_nil,
    Nat.reduceEqDiff, ↓reduceIte, List.append_nil]
  rw [Ordered.projection_recover, Ordered.projection_recover]
  simp [ComputedPublication.events, Ordered.events, producerRun, consumerRun,
    initialWords, TraceMemory.Initial.occurrence, Location.code, MemoryWitness.initialEvents]

def graph (initial : Initial) (order : LoadOrder) (left right flag payload : Word)
    (source : Fin 10 → Fin 10) (co : Fin 10 → Fin 10 → Bool) : Graph 10 :=
  ⟨fun i => (events initial order left right flag payload)[i.val]'(by
      rw [events_recover, events_eq]; simp [table]), source, co⟩

theorem graph_recover (initial order left right flag payload source co) :
    graph initial order left right flag payload source co =
      ComputedPublication.graph initial order left right flag payload source co := by
  unfold graph ComputedPublication.graph
  congr 1
  funext i
  simp [events_recover]

theorem publication (initial left right flag payload source co)
    (valid : (graph initial .acquire left right flag payload source co).Valid)
    (seen : (consumerRun initial .acquire flag payload).state.regs 0 = 1) :
    (consumerRun initial .acquire flag payload).status = .halted ∧
    (consumerRun initial .acquire flag payload).state.regs 1 = initial.x + initial.y := by
  rw [graph_recover] at valid
  exact publication_observed initial left right flag payload source co valid seen

theorem successful_witness (initial : Initial) :
    (graph initial .acquire initial.x initial.y 1 (initial.x+initial.y)
      successSource witnessCo).Valid ∧
    (producerRun initial initial.x initial.y).status = .halted ∧
    (consumerRun initial .acquire 1 (initial.x+initial.y)).status = .halted ∧
    (∀ a, ¬Path (valueEdge (graph initial .acquire initial.x initial.y 1
      (initial.x+initial.y) successSource witnessCo)) a a) := by
  rw [graph_recover]
  have h := run_results initial .acquire initial.x initial.y 1 (initial.x+initial.y)
  exact ⟨success_valid initial, h.1, h.2.2.1, success_value_acyclic initial⟩

theorem relaxed_witness (initial : Initial) (different : initial.old ≠ initial.x+initial.y) :
    (graph initial .relaxed initial.x initial.y 1 initial.old staleSource witnessCo).Valid ∧
    (consumerRun initial .relaxed 1 initial.old).status = .halted ∧
    (consumerRun initial .relaxed 1 initial.old).state.regs 1 ≠ initial.x+initial.y ∧
    (∀ a, ¬Path (valueEdge (graph initial .relaxed initial.x initial.y 1 initial.old
      staleSource witnessCo)) a a) := by
  rw [graph_recover]
  have h := ComputedPublication.relaxed_counterexample initial different
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem memory_safe (initial order left right flag payload source co) (i : Fin 10) :
    AccessSafe 4 ((graph initial order left right flag payload source co).event i).effect := by
  rw [graph_recover]
  exact graph_memory_safe _ _ _ _ _ _ _ _ i

end Ptx.Scalar.ComputedPublication.Projected
