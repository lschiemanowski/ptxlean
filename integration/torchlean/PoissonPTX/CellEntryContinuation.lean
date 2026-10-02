import PoissonPTX.CellEntryVisibility
import PoissonPTX.CellEntryLaunch
import PoissonPTX.CellGatherPreservation

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Resume the actual prefix state. Only the instruction-counter origin changes;
registers, bytes, predicates and the completed barrier state are retained. -/
def continuation (s : State 32) : Concurrent.WithTail.State 32 :=
  ⟨resume s,s.live,fun _ => false⟩

variable {cfg : Concurrent.Config 32} {bases : Space → Word} {cell : BitVec 32}
  {width : Nat} {cells source : Word} {s t : State 32}
  {events : List (Concurrent.Event 32)} {indices : List (Fin 32 × IndexSources.Access)}
  {memory : Space → Memory} {chosen : Nat → Fin 8 → Sources.Origin Nat}
  {selected : Nat → Fin 4 → Sources.Origin Nat}

/- These are the entry theorem's execution, input representation and safety
premises, shared by the producer lemmas below. None asserts a store or answer. -/
variable (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
  (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
  (words : Concurrent.Visibility.Compatible memory events chosen)
  (indexSources : IndexSources.Compatible (memory .global) events indices selected)
  (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
  (positive : 0<width) (fits : width*width<2^32)
  (space : (bases .shared).toNat+7*width*width*8≤2^64)
  (valid : ∀ u : Fin 32, u.val<width*width →
    CellGather.Valid (Local.beforeGather (CellPrologue.threadContext bases cell u) width (lane s u)) width cells source)

include run aligned initial words indexSources pcs done positive fits space valid

/-- A read by the actual arithmetic/output continuation sees the gathered
word. Both store ordering and preservation of the gathered slot are derived
from the two real runs; no visibility or read-value premise is supplied.
The prefix input-source restriction is still explicit at this modular boundary. -/
theorem continuation_read {later : List (Concurrent.Event 32)} {r : Nat}
    (lo : 2≤width) (hi : width≤5)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (continuation t) later final)
    (reset : s.core.barrier=Ptx.Barrier.reset generation)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (owner : Fin 32) (active : owner.val<width*width)
    (observed : later[r]?=some (.data reader access))
    (read : access.data.store=false) (shared : access.space=.shared)
    (address : access.data.address=(bases .shared).toNat+owner.val*8) :
    access.data.value=Producers.value bases cell width cells source s owner := by
  obtain ⟨launch⟩ := arithmetic_launch run aligned initial words indexSources pcs owner
    (by rw [done]; omega) positive fits space (fun u h => valid u (by simpa only [context_lane] using h))
  apply Producers.read_gathered run aligned initial words indexSources pcs done positive fits space valid
    reset joint performed owner active observed read shared address
  intro writer a member store sharedStore
  exact Concurrent.CellConsumer.WithOutput.preserves_gather launch lo hi body member store sharedStore owner active

end PtxTorchLean.Poisson.PTX.CellEntry
