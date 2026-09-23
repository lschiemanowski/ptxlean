import Ptx.ComputedPublicationMachine
import Ptx.Publication

/-! Actual scalar computed-data publication. Graph.Valid supplies necessary
memory constraints, not a complete admission rule for arbitrary dependent PTX.
This program's inputs have only initialization writes and the consumer writes
nothing, so its computed values cannot be circularly justified. -/
namespace Ptx.Scalar.ComputedPublication

open Ordered

structure Initial where
  x : Word
  y : Word
  old : Word
  registers : Nat → Nat → Word
  addresses : Nat → Nat → Scalar.Address
  predicates : Nat → Nat → Bool

def start (initial : Initial) (thread : Nat) : State :=
  ⟨0, initial.registers thread, initial.addresses thread, initial.predicates thread,
    [initial.x, initial.y, initial.old, 0]⟩

def producer : List Ordered.Instr :=
  [⟨.always, .load .relaxed 0 (.imm 0)⟩,
   ⟨.always, .load .relaxed 1 (.imm 4)⟩,
   ⟨.always, .add 2 (.reg 0) (.reg 1)⟩,
   ⟨.always, .store .relaxed (.imm 8) 2⟩,
   ⟨.always, .mov 3 (.imm 1)⟩,
   ⟨.always, .store .release (.imm 12) 3⟩,
   ⟨.always, .exit⟩]

def consumer (order : LoadOrder) : List Ordered.Instr :=
  [⟨.always, .load order 0 (.imm 12)⟩,
   ⟨.always, .load .relaxed 1 (.imm 8)⟩,
   ⟨.always, .exit⟩]

def reads (first second : Word) (position : Nat) : Option Word :=
  if position = 0 then some first else if position = 1 then some second else none

def producerRun (initial : Initial) (left right : Word) : RunResult :=
  Ordered.run 7 (reads left right) producer (start initial 0)

def consumerRun (initial : Initial) (order : LoadOrder) (flag payload : Word) : RunResult :=
  Ordered.run 3 (reads flag payload) (consumer order) (start initial 1)

def events (initial : Initial) (order : LoadOrder) (left right flag payload : Word) :
    List Ptx.Occurrence :=
  MemoryWitness.initialEvents [initial.x, initial.y, initial.old, 0] ++
    Ordered.events 7 (reads left right) producer (start initial 0) 0 ++
    Ordered.events 3 (reads flag payload) (consumer order) (start initial 1) 1

def table (initial : Initial) (order : LoadOrder) (left right flag payload : Word) :
    List Ptx.Occurrence :=
  [⟨none,0,⟨.init,0,initial.x⟩⟩,
   ⟨none,1,⟨.init,1,initial.y⟩⟩,
   ⟨none,2,⟨.init,2,initial.old⟩⟩,
   ⟨none,3,⟨.init,3,0⟩⟩,
   ⟨some 0,0,⟨.load .relaxed,0,left⟩⟩,
   ⟨some 0,1,⟨.load .relaxed,1,right⟩⟩,
   ⟨some 0,3,⟨.store .relaxed,2,left+right⟩⟩,
   ⟨some 0,5,⟨.store .release,3,1⟩⟩,
   ⟨some 1,0,⟨.load order,3,flag⟩⟩,
   ⟨some 1,1,⟨.load .relaxed,2,payload⟩⟩]

/-- The event table is derived from actual fetch/guard/register execution. -/
theorem events_eq (initial order left right flag payload) :
    events initial order left right flag payload = table initial order left right flag payload := by
  simp [events, table, MemoryWitness.initialEvents, Ordered.events, Ordered.run,
    Ordered.erase, Ordered.Instr.erase, Ordered.Op.erase, Ordered.label,
    producer, consumer, start, runWith, stepWith, eval, Guard.eval, Operand64.eval,
    Operand32.eval, BinOp.eval, update, addressIndex, reads, occurrence]

def graph (initial : Initial) (order : LoadOrder) (left right flag payload : Word)
    (source : Fin 10 → Fin 10) (co : Fin 10 → Fin 10 → Bool) : Graph 10 :=
  ⟨fun i => (events initial order left right flag payload).get
    ⟨i.val, by rw [events_eq]; simp [table]⟩, source, co⟩

theorem graph_event (initial order left right flag payload source co) (i : Fin 10) :
    (graph initial order left right flag payload source co).event i =
      (table initial order left right flag payload).get ⟨i.val, by simp [table]⟩ := by
  simp [graph, events_eq]

@[simp] theorem graph_source (initial order left right flag payload source co) :
    (graph initial order left right flag payload source co).source = source := rfl

@[simp] theorem event0 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 0 = ⟨none,0,⟨.init,0,initial.x⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event1 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 1 = ⟨none,1,⟨.init,1,initial.y⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event2 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 2 = ⟨none,2,⟨.init,2,initial.old⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event3 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 3 = ⟨none,3,⟨.init,3,0⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event4 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 4 = ⟨some 0,0,⟨.load .relaxed,0,left⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event5 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 5 = ⟨some 0,1,⟨.load .relaxed,1,right⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event6 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 6 = ⟨some 0,3,⟨.store .relaxed,2,left+right⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event7 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 7 = ⟨some 0,5,⟨.store .release,3,1⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event8 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 8 = ⟨some 1,0,⟨.load order,3,flag⟩⟩ := by
  rw [graph_event]; rfl

@[simp] theorem event9 (initial : Initial) (order left right flag payload source co) :
    (graph initial order left right flag payload source co).event 9 = ⟨some 1,1,⟨.load .relaxed,2,payload⟩⟩ := by
  rw [graph_event]; rfl

theorem fin_cases (i : Fin 10) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega

/-- Input-only locations force the actual loaded register values. No assumption
of the sum, publication result or dependency axiom appears here. -/
theorem input_sources (initial order left right flag payload source co)
    (sources : (graph initial order left right flag payload source co).Sources) :
    left = initial.x ∧ right = initial.y := by
  constructor
  · have h := sources.compatible 4 (by simp [Graph.read])
    simp only [graph_source, event4] at h
    rcases fin_cases (source 4) with he | he | he | he | he | he | he | he | he | he
    all_goals rw [he] at h
    all_goals simp [Graph.write, Graph.sameAddress] at h
    exact h.symm
  · have h := sources.compatible 5 (by simp [Graph.read])
    simp only [graph_source, event5] at h
    rcases fin_cases (source 5) with he | he | he | he | he | he | he | he | he | he
    all_goals rw [he] at h
    all_goals simp [Graph.write, Graph.sameAddress] at h
    exact h.symm

/-- Completing the actual scalar runs writes the candidate sum and retains
consumer observations in registers zero and one. -/
theorem run_results (initial order left right flag payload) :
    (producerRun initial left right).status = .halted ∧
    (producerRun initial left right).state.memory = [initial.x, initial.y, left+right, 1] ∧
    (consumerRun initial order flag payload).status = .halted ∧
    (consumerRun initial order flag payload).state.regs 0 = flag ∧
    (consumerRun initial order flag payload).state.regs 1 = payload := by
  simp [producerRun, consumerRun, Ordered.run, Ordered.erase, Ordered.Instr.erase,
    Ordered.Op.erase, producer, consumer, start, runWith, stepWith, eval,
    Guard.eval, Operand64.eval, Operand32.eval, BinOp.eval, update, addressIndex,
    reads, occurrence]

/-- Quantifies over every compatible source/coherence choice. Reading flag one
with acquire ordering excludes the initial payload, even when it equals the sum. -/
theorem publication (initial left right payload source co)
    (valid : (graph initial .acquire left right 1 payload source co).Valid) :
    payload = initial.x + initial.y := by
  let g := graph initial .acquire left right 1 payload source co
  obtain ⟨hx, hy⟩ := input_sources _ _ _ _ _ _ _ _ valid.sources
  have flagSource : source 8 = 7 := by
    have h := valid.sources.compatible 8 (by simp [Graph.read])
    simp only [graph_source, event8] at h
    rcases fin_cases (source 8) with he | he | he | he | he | he | he | he | he | he
    all_goals try { exact he }
    all_goals rw [he] at h
    all_goals simp [Graph.write, Graph.sameAddress] at h
  have sync : g.sync 7 8 := by
    apply Graph.direct_sync
    · simp [g]
    · simp [g, Graph.release]
    · simp [g, Graph.acquire]
    · exact flagSource
    · simp [g, Graph.sameAddress]
  have cause : g.cause 6 9 := by
    apply Graph.publication_cause g 6 7 8 9
    · simp [g, Graph.po]
    · simp [g, Graph.po]
    · exact sync
    · simp [g, Graph.sameAddress]
  have choices : source 9 = 2 ∨ source 9 = 6 := by
    have h := valid.sources.compatible 9 (by simp [Graph.read])
    simp only [graph_source, event9] at h
    rcases fin_cases (source 9) with he | he | he | he | he | he | he | he | he | he
    all_goals try { exact Or.inl he }
    all_goals try { exact Or.inr he }
    all_goals rw [he] at h
    all_goals simp [Graph.write, Graph.sameAddress] at h
  have sourced : g.source 9 = 6 := by
    apply Graph.source_of_initial_or_write g valid 2 6 9
    · simp [g, Graph.initial]
    · simp [g, Graph.write]
    · simp [g, Graph.read]
    · simp [g, Graph.sameAddress]
    · decide
    · simp [g, Graph.sameAddress]
    · exact cause
    · exact choices
  have value := Graph.value_of_source g valid.sources 6 9 (by simp [g, Graph.read]) sourced
  simpa [g, hx, hy] using value

/-- The guarantee concerns actual completed scalar register observations. -/
theorem publication_observed (initial left right flag payload source co)
    (valid : (graph initial .acquire left right flag payload source co).Valid)
    (seen : (consumerRun initial .acquire flag payload).state.regs 0 = 1) :
    (consumerRun initial .acquire flag payload).status = .halted ∧
    (consumerRun initial .acquire flag payload).state.regs 1 = initial.x + initial.y := by
  have results := run_results initial .acquire left right flag payload
  have flagOne : flag = 1 := results.2.2.2.1.symm.trans seen
  subst flag
  exact ⟨results.2.2.1, results.2.2.2.2.trans (publication _ _ _ _ _ _ valid)⟩

end Ptx.Scalar.ComputedPublication
