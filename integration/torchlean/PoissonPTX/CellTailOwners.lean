import PoissonPTX.CellTailBounds

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
open CellMiddle

/-- Threads of a single cell have disjoint output words, derived from their
launch lane IDs and a common cell ID, including possible padding addresses. -/
theorem output_disjoint
    (launch : Numeric.Launch width bases start.core) (hi : width≤5)
    (bounds : OutputBounds width output start)
    (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (a b : Fin 32) (different : a≠b) :
    (CellFinal.location (start.core.lanes a) width output).toNat+8≤
      (CellFinal.location (start.core.lanes b) width output).toNat ∨
    (CellFinal.location (start.core.lanes b) width output).toNat+8≤
      (CellFinal.location (start.core.lanes a) width output).toNat := by
  apply Output.distinct_outputs _ _ hi (bounds a).1 (bounds b).1 (bounds a).2 (bounds b).2
  · rw [launch.global,launch.global]
  · rw [cells,cells,launch.lane_nat,launch.lane_nat]
    intro eq
    apply different
    apply Fin.ext
    omega

/-- Byte ranges of actual global stores by distinct threads are disjoint.
No unique-writer or store-address event assumption is used. -/
theorem stores_disjoint
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (observedA : Event.data a aa∈events) (observedB : Event.data b ab∈events)
    (storeA : aa.data.store=true) (globalA : aa.space=.global)
    (storeB : ab.data.store=true) (globalB : ab.space=.global) (different : a≠b) :
    aa.data.address+8≤ab.data.address ∨ ab.data.address+8≤aa.data.address := by
  rw [Address.store_address lo hi run launch.aligned launch.pcs observedA storeA globalA,
    Address.store_address lo hi run launch.aligned launch.pcs observedB storeB globalB]
  exact output_disjoint launch hi bounds cells a b different

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
