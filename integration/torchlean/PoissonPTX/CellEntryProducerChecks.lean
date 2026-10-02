import PoissonPTX.CellEntryProducers
import PoissonPTX.CellEntryChecks

namespace PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks
open Checks

theorem aligned : Concurrent.Aligned start.core := by
  intro thread waiting
  simp [start,Ptx.Barrier.reset] at waiting

theorem valid : ∀ u : Fin 32, u.val<4 →
    CellGather.Valid (Local.beforeGather (CellPrologue.threadContext bases 1 u) 2 (lane start u)) 2 0 64 := by
  unfold CellGather.Valid
  decide +kernel

/-- Instantiate store occurrence and exact byte-backed value on the nonzero
run; the store list is an output of the theorem, not a fixture premise. -/
theorem actual_producer (owner : Fin 32) (active : owner.val<4) :
    ∃ (position : Nat) (access : Concurrent.Access), result.events[position]?=some (.data owner access) ∧
      access.data.store=true ∧ access.space=.shared ∧ access.data.pc=19 ∧
      access.data.address=256+owner.val*8 ∧
      access.data.value=Producers.value bases 1 2 0 64 start owner :=
  Producers.producer actual_run aligned (by intro u; rfl) compatible index_compatible
    (by intro u; rfl) completed.1 (by decide) (by decide) (by decide) valid owner active

theorem padding_has_no_store (owner : Fin 32) (inactive : 4≤owner.val) :
    ¬Wrote result.events owner := by
  rintro ⟨access,member,store,_⟩
  have live := store_active actual_run aligned (by intro u; rfl) compatible index_compatible
    (by rfl) (by decide) (by decide) member store
  change (CellPrologue.threadContext bases 1 owner).lane.toNat<2*2 at live
  rw [context_lane] at live
  omega

theorem independent_slots (left : Concurrent.Event.data a wa∈result.events) (leftStore : wa.data.store=true)
    (right : Concurrent.Event.data b wb∈result.events) (rightStore : wb.data.store=true) (different : a≠b) :
    Sources.Disjoint wa.data.address wb.data.address :=
  Producers.different_writers actual_run aligned (by intro u; rfl) compatible index_compatible
    (by intro u; rfl) completed.1 (by decide) (by decide) (by decide) valid left leftStore right rightStore different

end PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks
