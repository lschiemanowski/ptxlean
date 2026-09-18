import Ptx.MessagePassingOutcomes

/-! Boundary and malformed-candidate regressions for the executable checker.
Each result is a kernel-checked proposition, not an unchecked test assertion. -/
namespace Ptx.CheckerExamples

/-- An empty relation must not acquire identity edges. -/
theorem empty_relation (a b : Fin 3) :
    reachable (fun _ _ : Fin 3 => false) a b = false := by
  revert a b
  decide

theorem singleton_loop : reachable (fun _ _ : Fin 1 => true) 0 0 = true := by decide

def cycleEdges (a b : Fin 3) : Bool := b.val == (a.val + 1) % 3

/-- In particular, nonempty cycles make every diagonal reachable. -/
theorem cycle_reachable : ∀ a b : Fin 3, reachable cycleEdges a b = true := by decide

def emptyGraph : Graph 0 := ⟨Fin.elim0, Fin.elim0, fun _ _ => false⟩
def initializedGraph : Graph 1 :=
  ⟨fun _ => ⟨none, 0, ⟨.init, 0, 0⟩⟩, fun _ => 0, fun _ _ => false⟩
def sourceIsRead : Graph 1 :=
  ⟨fun _ => ⟨some 0, 0, ⟨.load .relaxed, 0, 0⟩⟩, fun _ => 0, fun _ _ => false⟩

theorem empty_graph_accepted : emptyGraph.check = true := by decide
theorem initialized_graph_accepted : initializedGraph.check = true := by decide
theorem read_cannot_source_itself : sourceIsRead.check = false := by decide

def reflexiveCo : Graph 1 := { initializedGraph with co := fun _ _ => true }
theorem reflexive_coherence_rejected : reflexiveCo.check = false := by decide

open MessagePassing

/-- Same address, wrong value: flag=1 cannot source initialization. -/
def wrongValue : Graph 6 := graph .acquire 1 7 (outcomeSource false true) witnessCo
/-- Wrong address: the flag load cannot source the payload write. -/
def wrongAddress : Graph 6 := graph .acquire 1 7 (fun _ => a) witnessCo
/-- Correct read sources cannot rescue a coherence relation omitting initialization order. -/
def missingCo : Graph 6 := graph .acquire 1 7 successSource (fun _ _ => false)

theorem wrong_value_rejected : wrongValue.check = false := by decide
theorem wrong_address_rejected : wrongAddress.check = false := by decide
theorem missing_initial_coherence_rejected : missingCo.check = false := by decide

/-- Translate Boolean rejection into the unchanged semantic predicate. -/
theorem wrong_value_invalid : ¬wrongValue.Valid :=
  (Graph.check_false_iff _).mp wrong_value_rejected

/-- Two distinct threads each acquire before releasing; each load sources the
other thread's release. This produces a genuine cyclic base order. Synthetic
Graph inputs are intentional here: the checker accepts any finite graph. -/
def cyclicBase : Graph 4 :=
  ⟨fun i => [⟨some 0, 0, ⟨.load .acquire, 0, 1⟩⟩,
             ⟨some 0, 1, ⟨.store .release, 0, 1⟩⟩,
             ⟨some 1, 0, ⟨.load .acquire, 0, 1⟩⟩,
             ⟨some 1, 1, ⟨.store .release, 0, 1⟩⟩].get i,
   fun i => if i = 0 then 3 else 1,
   fun i j => i == 1 && j == 3⟩

theorem base_cycle_detected : cyclicBase.baseCheck 0 0 = true := by decide
theorem base_cycle_rejected : cyclicBase.check = false := by decide

end Ptx.CheckerExamples
