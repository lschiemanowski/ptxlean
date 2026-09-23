import Ptx.OrderedMemory
import Ptx.CollectiveOrder

/-! Compose a structural completed-phase certificate with memory constraints.
The instruction/control origin of that certificate is a separate obligation.
The acyclicity result below establishes one validity field, not all of them.
-/
namespace Ptx.CollectiveMemory

variable {n : Nat} {Participant Phase : Type}
variable (g : Graph n) (c : CollectiveOrder.Certificate (Fin n) Participant Phase)

theorem base_acyclic
    (ordinary : ∀ a b, g.baseEdge a b → c.memoryPos a < c.memoryPos b)
    (a : Fin n) : ¬Graph.Ordered.base g c.cross a a :=
  c.projected_acyclic g.baseEdge ordinary a

theorem cross_cause (a b : Fin n) (phase : Phase) (ta tb : Participant)
    (before : c.Before a phase ta) (after : c.After b phase tb)
    (same : g.sameAddress a b) : Graph.Ordered.cause g c.cross a b :=
  Graph.Ordered.extra_cause g c.cross a b ⟨phase, ta, tb, before, after⟩ same

theorem source_after_phase (valid : Graph.Ordered.Valid g c.cross)
    (w r : Fin n) (phase : Phase) (tw tr : Participant)
    (before : c.Before w phase tw) (after : c.After r phase tr)
    (written : g.write w) (readAt : g.read r) (same : g.sameAddress w r)
    (latest : ∀ v, g.write v → g.sameAddress v r → v ≠ w → g.coherence v w) :
    g.source r = w :=
  Graph.Ordered.source_of_latest g c.cross valid w r written readAt same
    (cross_cause g c w r phase tw tr before after same) latest

theorem value_after_phase (valid : Graph.Ordered.Valid g c.cross)
    (w r : Fin n) (phase : Phase) (tw tr : Participant)
    (before : c.Before w phase tw) (after : c.After r phase tr)
    (written : g.write w) (readAt : g.read r) (same : g.sameAddress w r)
    (latest : ∀ v, g.write v → g.sameAddress v r → v ≠ w → g.coherence v w) :
    (g.event r).effect.value = (g.event w).effect.value :=
  Graph.value_of_source g valid.sources w r readAt
    (source_after_phase g c valid w r phase tw tr before after written readAt same latest)

end Ptx.CollectiveMemory
