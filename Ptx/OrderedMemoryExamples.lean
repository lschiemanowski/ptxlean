import Ptx.OrderedMemory

/-! Algebraic distinguishing examples, not an execution-origin certificate. -/
namespace Ptx.Graph.Ordered.Examples

def graph (fresh : Bool) : Graph 3 where
  event := fun i => match i.val with
    | 0 => ⟨none, 0, ⟨.init, 0, 0⟩⟩
    | 1 => ⟨some 0, 0, ⟨.store .relaxed, 0, 1⟩⟩
    | _ => ⟨some 1, 0, ⟨.load .relaxed, 0, if fresh then 1 else 0⟩⟩
  source := fun _ => if fresh then 1 else 0
  co := fun a b => a == 0 && b == 1

def extra (a b : Fin 3) : Prop := a = 1 ∧ b = 2

def rank (fresh : Bool) (i : Fin 3) : Nat :=
  if fresh then i.val else if i = 1 then 2 else if i = 2 then 1 else 0

set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

local macro "finite_check" : tactic => `(tactic|
  simp [Fin.forall_fin_succ, Fin.exists_fin_succ, baseEdge, Graph.baseEdge,
    Graph.sync, Graph.releasePattern, Graph.acquirePattern, Graph.observation,
    Graph.rf, Graph.morallyStrong, Graph.initial, Graph.release, Graph.acquire,
    Graph.po, Graph.sameAddress, Graph.read, Graph.write, Graph.coherence,
    Graph.upperCause, Graph.locationEdge, Graph.communication, graph, extra, rank])

theorem unordered_valid (fresh : Bool) : (graph fresh).Valid := by
  apply Graph.valid_of_certificate (upper := fun _ _ => False) (rank := rank fresh)
  cases fresh
  all_goals
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

theorem ordered_fresh_valid : Valid (graph true) extra := by
  apply valid_of_certificate (upper := extra) (rank := rank true)
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

theorem ordered_stale_invalid : ¬Valid (graph false) extra := by
  intro h
  exact h.no_stale 1 2 (by finite_check) (by finite_check) (by finite_check)
    (extra_cause _ _ _ _ (by finite_check) (by finite_check)) (by finite_check)

theorem extension_distinguishes :
    (graph false).Valid ∧ (graph true).Valid ∧
      ¬Valid (graph false) extra ∧ Valid (graph true) extra :=
  ⟨unordered_valid false, unordered_valid true, ordered_stale_invalid, ordered_fresh_valid⟩

end Ptx.Graph.Ordered.Examples
