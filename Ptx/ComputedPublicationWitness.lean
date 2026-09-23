import Ptx.ComputedPublication

/-! Concrete graph and local execution witnesses. Value-grounding is proved
separately; validity alone is not promoted into general dependent PTX semantics. -/
namespace Ptx.Scalar.ComputedPublication

set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def witnessCo (a b : Fin 10) : Bool := (a == 2 && b == 6) || (a == 3 && b == 7)
def successSource (i : Fin 10) : Fin 10 :=
  if i = 5 then 1 else if i = 8 then 7 else if i = 9 then 6 else 0

def staleSource (i : Fin 10) : Fin 10 :=
  if i = 5 then 1 else if i = 8 then 7 else if i = 9 then 2 else 0

def success (initial : Initial) : Graph 10 :=
  graph initial .acquire initial.x initial.y 1 (initial.x+initial.y) successSource witnessCo

def stale (initial : Initial) : Graph 10 :=
  graph initial .relaxed initial.x initial.y 1 initial.old staleSource witnessCo

def successUpper (a b : Fin 10) : Prop := 4 ≤ a.val ∧ a.val < b.val

def staleUpper (a b : Fin 10) : Prop :=
  (4 ≤ a.val ∧ a.val < b.val ∧ b.val ≤ 7) ∨ (a = 8 ∧ b = 9)

def staleRank (i : Fin 10) : Nat :=
  if i = 6 ∨ i = 8 then 2 else if i = 7 ∨ i = 9 then 1 else 0

local macro "finite_check" : tactic => `(tactic|
  (simp [Graph.baseEdge, Graph.sync, Graph.releasePattern, Graph.acquirePattern,
    Graph.observation, Graph.rf, Graph.morallyStrong, Graph.initial, Graph.release,
    Graph.acquire, Graph.po, Graph.sameAddress, Graph.read, Graph.write,
    Graph.coherence, Graph.upperCause, Graph.locationEdge, Graph.communication,
    success, stale, graph, events_eq, table, successSource, staleSource, witnessCo,
    successUpper, staleUpper, staleRank,
    Fin.forall_fin_succ, Fin.exists_fin_succ] <;>
    first | trivial | (constructor <;> trivial) | decide))

/-- Every input pair has a compatible successful graph, without fixed input
values or a hypothesized output result. -/
theorem success_valid (initial : Initial) : (success initial).Valid := by
  apply Graph.valid_of_certificate (upper := successUpper) (rank := Fin.val)
  exact {
    sources := ⟨by finite_check⟩
    co := ⟨by finite_check, by finite_check, by finite_check, by finite_check, by finite_check⟩
    edge_included := by finite_check
    upper_trans := by finite_check
    upper_irrefl := by finite_check
    coherence_cause := by finite_check
    no_future := by finite_check
    no_stale := by finite_check
    location_rank := by finite_check
  }

/-- Only the consumer flag qualifier changes. Candidate values still come from
actual local scalar computations and a concrete compatible read-source choice. -/
theorem stale_valid (initial : Initial) : (stale initial).Valid := by
  apply Graph.valid_of_certificate (upper := staleUpper) (rank := staleRank)
  exact {
    sources := ⟨by finite_check⟩
    co := ⟨by finite_check, by finite_check, by finite_check, by finite_check, by finite_check⟩
    edge_included := by finite_check
    upper_trans := by finite_check
    upper_irrefl := by finite_check
    coherence_cause := by finite_check
    no_future := by finite_check
    no_stale := by finite_check
    location_rank := by finite_check
  }

/-- Value edges include actual read-source choices and the producer's two input
loads feeding the computed payload store. The flag value is a literal moved into
a register; the consumer has no store. This is this program's dependency graph,
not a proposed general PTX no-thin-air axiom. -/
def valueEdge (g : Graph 10) (a b : Fin 10) : Prop :=
  g.rf a b ∨ ((a = 4 ∨ a = 5) ∧ b = 6)

theorem success_values_grounded (initial : Initial) :
    ∀ a b, valueEdge (success initial) a b → a.val < b.val := by
  simp [valueEdge, Graph.rf, Graph.read, success, graph, events_eq, table,
    successSource, Fin.forall_fin_succ]

theorem stale_values_grounded (initial : Initial) :
    ∀ a b, valueEdge (stale initial) a b → a.val < b.val := by
  simp [valueEdge, Graph.rf, Graph.read, stale, graph, events_eq, table,
    staleSource, Fin.forall_fin_succ]

theorem success_value_acyclic (initial : Initial) (a : Fin 10) :
    ¬Path (valueEdge (success initial)) a a := by
  intro path
  exact Nat.lt_irrefl _ (Path.rank_increases Fin.val (success_values_grounded initial) path)

theorem stale_value_acyclic (initial : Initial) (a : Fin 10) :
    ¬Path (valueEdge (stale initial)) a a := by
  intro path
  exact Nat.lt_irrefl _ (Path.rank_increases Fin.val (stale_values_grounded initial) path)

/-- The producer's two values sourced from initialization agree exactly with
its ordinary concrete arena run, including every register and trace occurrence. -/
theorem producer_concrete (initial : Initial) :
    producerRun initial initial.x initial.y = Scalar.run 7 (Ordered.erase producer) (start initial 0) := by
  simp [producerRun, Ordered.run, Scalar.run, Ordered.erase, Ordered.Instr.erase,
    Ordered.Op.erase, producer, start, runWith, stepWith, eval, Guard.eval,
    Operand64.eval, Operand32.eval, BinOp.eval, update, addressIndex, reads]

/-- The finite witness includes both actual completed scalar derivations, graph
validity and absence of circular value justification. No scheduler is assumed. -/
theorem successful_execution (initial : Initial) :
    Scalar.Runs (Ordered.erase producer) (reads initial.x initial.y) (start initial 0)
      (producerRun initial initial.x initial.y) ∧
    Scalar.Runs (Ordered.erase (consumer .acquire)) (reads 1 (initial.x+initial.y)) (start initial 1)
      (consumerRun initial .acquire 1 (initial.x+initial.y)) ∧
    (producerRun initial initial.x initial.y).status = .halted ∧
    (consumerRun initial .acquire 1 (initial.x+initial.y)).status = .halted ∧
    (consumerRun initial .acquire 1 (initial.x+initial.y)).state.regs 0 = 1 ∧
    (consumerRun initial .acquire 1 (initial.x+initial.y)).state.regs 1 = initial.x+initial.y ∧
    (success initial).Valid ∧
    (∀ a, ¬Path (valueEdge (success initial)) a a) := by
  have results := run_results initial .acquire initial.x initial.y 1 (initial.x+initial.y)
  exact ⟨Ordered.run_sound _ _ _ _, Ordered.run_sound _ _ _ _, results.1,
    results.2.2.1, results.2.2.2.1, results.2.2.2.2,
    success_valid initial, success_value_acyclic initial⟩

/-- Old payload is a distinguishing result exactly when it differs from the
computed sum. This premise establishes inequality, not graph permission. -/
theorem relaxed_counterexample (initial : Initial) (different : initial.old ≠ initial.x+initial.y) :
    Scalar.Runs (Ordered.erase producer) (reads initial.x initial.y) (start initial 0)
      (producerRun initial initial.x initial.y) ∧
    Scalar.Runs (Ordered.erase (consumer .relaxed)) (reads 1 initial.old) (start initial 1)
      (consumerRun initial .relaxed 1 initial.old) ∧
    (producerRun initial initial.x initial.y).status = .halted ∧
    (consumerRun initial .relaxed 1 initial.old).status = .halted ∧
    (consumerRun initial .relaxed 1 initial.old).state.regs 0 = 1 ∧
    (consumerRun initial .relaxed 1 initial.old).state.regs 1 ≠ initial.x+initial.y ∧
    (stale initial).Valid ∧
    (∀ a, ¬Path (valueEdge (stale initial)) a a) := by
  have results := run_results initial .relaxed initial.x initial.y 1 initial.old
  exact ⟨Ordered.run_sound _ _ _ _, Ordered.run_sound _ _ _ _, results.1,
    results.2.2.1, results.2.2.2.1, by simpa only [results.2.2.2.2] using different,
    stale_valid initial, stale_value_acyclic initial⟩

/-- Every candidate emitted byte address is aligned and in the four-word arena,
independently of graph validity and of all proposed loaded values. -/
theorem producer_safe (initial left right) :
    ∀ occ ∈ (producerRun initial left right).trace,
      ∀ effect, occ.memory = some effect →
        ValidAddress [initial.x, initial.y, initial.old, 0] effect.address :=
  Ordered.run_safe _ _ _ _

theorem consumer_safe (initial order flag payload) :
    ∀ occ ∈ (consumerRun initial order flag payload).trace,
      ∀ effect, occ.memory = some effect →
        ValidAddress [initial.x, initial.y, initial.old, 0] effect.address :=
  Ordered.run_safe _ _ _ _

/-- Graph words retain the full aligned four-byte footprint of the scalar accesses. -/
theorem graph_memory_safe (initial order left right flag payload source co) (i : Fin 10) :
    AccessSafe 4 ((graph initial order left right flag payload source co).event i).effect := by
  apply access_safe_of_index_lt
  rcases fin_cases i with h | h | h | h | h | h | h | h | h | h
  all_goals subst i; simp

end Ptx.Scalar.ComputedPublication
