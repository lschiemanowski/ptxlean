import PoissonPTX.CellEntryContinuation
import PoissonPTX.CellEntryProducerChecks

namespace PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks
open Ptx Checks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def key : Barrier.Key := ⟨1,0,0,20⟩
theorem completion : result.events[40]?=some (.barrier (.completion key)) := by decide +kernel

/-- Every real active producer precedes its own arrival and the final release. -/
theorem ordered_producers (owner : Fin 32) (active : owner.val<4) :
    ∃ (w a : Nat) (wa : Concurrent.Access), result.events[w]?=some (.data owner wa) ∧
      wa.data.store=true ∧ result.events[a]?=some (.barrier (.arrival key owner)) ∧ w<a ∧ a<40 := by
  obtain ⟨w,wa,hw,store,_⟩ := ProducerChecks.actual_producer owner active
  obtain ⟨a,ha,first,last⟩ := store_before_completion actual_run (by rfl) hw store completion
  exact ⟨w,a,wa,hw,store,ha,first,last⟩

def read (value : Word) : Concurrent.Event 32 := .data 1 ⟨.shared,⟨99,false,256,value⟩⟩

/-- A later reader of lane zero's slot must see the gathered -2 bit pattern.
This checks the visibility interface on the actual nonzero prefix; it does not
claim that the appended observation is itself a fetched arithmetic execution. -/
theorem observed_value (value : Word)
    (compatible : Concurrent.Visibility.Compatible initial (result.events++[read value]) source)
    (performed : Concurrent.Visibility.Performed (result.events++[read value]) source) :
    value=0xc000000000000000 := by
  have h := Producers.read_gathered actual_run ProducerChecks.aligned (by intro u; rfl)
    Checks.compatible index_compatible (by intro u; rfl) completed.1
    (by decide) (by decide) (by decide) ProducerChecks.valid (by rfl)
    compatible performed (0 : Fin 32) (by decide)
    (r:=0) (by rfl) (by rfl) (by rfl) (by rfl)
    (by intro writer a member store shared; simp [read] at member; rcases member with ⟨rfl,rfl⟩; cases store)
  have valueKnown : Producers.value bases 1 2 0 64 start 0=0xc000000000000000 := by decide +kernel
  exact h.trans valueKnown

/-- Leaving the old shared byte pattern in place after the barrier violates
at least one of the necessary source constraints; it is not admitted silently. -/
theorem stale_read_rejected :
    ¬(Concurrent.Visibility.Compatible initial (result.events++[read 0x5a5a5a5a5a5a5a5a]) source ∧
      Concurrent.Visibility.Performed (result.events++[read 0x5a5a5a5a5a5a5a5a]) source) := by
  rintro ⟨compatible,performed⟩
  have bad := observed_value _ compatible performed
  contradiction

end PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks
