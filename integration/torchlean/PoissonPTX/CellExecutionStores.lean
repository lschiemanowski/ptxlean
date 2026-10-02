import PoissonPTX.CellExecution
import PoissonPTX.CellTailPadding

namespace PtxTorchLean.Poisson.PTX.CellWhole
open Concurrent.CellConsumer.WithOutput
variable {o : Operator} {values : Array Float} {cell : BitVec 32} {owner : Fin 32} {access : Concurrent.Access}

/-- Every actual global store belongs to an active coordinate of this cell.
The physical output range follows from the native entry and tail instructions;
inactive lanes cannot spill into a following cell's storage. -/
theorem Execution.global_store (execution : Execution o values cell)
    (member : Concurrent.Event.data owner access∈execution.events)
    (store : access.data.store=true) (global : access.space=.global) :
    owner.val<o.nodes.size*o.nodes.size ∧
    access.data.address=(execution.bases .global).toNat+
      (cell.toNat*(o.nodes.size*o.nodes.size)+owner.val)*8+execution.output.toNat := by
  have activeZero : (0 : Fin 32).val<o.nodes.size*o.nodes.size := by have := execution.positive; change 0<o.nodes.size*o.nodes.size; nlinarith
  have past : 20<(execution.final.core.lanes (0 : Fin 32)).pc := by have := execution.finished 0 activeZero; omega
  obtain ⟨before,after,ready,localFinal,eventEq,first,done,site,finalEq,body⟩ :=
    executions execution.run execution.aligned execution.pcs execution.running 0 past
  rw [eventEq] at member
  rcases List.mem_append.mp member with prefixMember | bodyMember
  · exact False.elim (CellEntry.no_global_store first prefixMember store global)
  obtain ⟨event,localMember,eq⟩ := List.mem_map.mp bodyMember
  cases event with
  | barrier => simp [Relocate.event] at eq
  | data thread recorded =>
    simp only [Relocate.event,Concurrent.Event.data.injEq] at eq
    obtain ⟨rfl,rfl⟩ := eq
    change recorded.data.store=true at store
    change recorded.space=.global at global
    obtain ⟨launch⟩ := CellEntry.Control.launch first execution.aligned execution.pcs done
      execution.positive (by have := execution.small; omega) execution.space
    have bounds := output_bounds first execution.aligned execution.pcs done execution.positive
      (by have := execution.small; omega) execution.bounds
    have control := CellEntry.Control.from_run first execution.aligned
      (fun u => CellEntry.Control.initial (s:=CellEntry.lane (entry execution.start) u) (execution.pcs u))
      execution.positive (by have := execution.small; omega)
    have cellReg : ((CellEntry.continuation (entry ready)).core.lanes thread).regs 15=cell.setWidth 64 := by
      exact (control thread).2.2.2.1 (by change 4≤(ready.core.lanes thread).pc; rw [done]; decide)
    have baseReg : ((CellEntry.continuation (entry ready)).core.lanes thread).regs 0=execution.bases .global := launch.global thread
    have laneNat : (((CellEntry.continuation (entry ready)).core.lanes thread).regs 14).toNat=thread.val := launch.lane_nat thread
    refine ⟨Padding.access_active execution.lo execution.hi body launch.aligned launch.pcs localMember,?_⟩
    change recorded.data.address=_
    rw [Address.store_address execution.lo execution.hi body launch.aligned launch.pcs localMember store global,
      CellFinal.location_exact _ execution.hi (bounds thread).1 (bounds thread).2,
      baseReg,laneNat,cellReg]
    have small : cell.toNat<2^64 := by have := cell.isLt; omega
    simp only [BitVec.toNat_setWidth,Nat.mod_eq_of_lt small]

/-- Publication preserves all bytes outside this cell's actual output plane,
including all immutable assembly tables and every other cell's output plane. -/
theorem Execution.outside (execution : Execution o values cell) (memory : Memory) (p : Nat)
    (apart : p<(execution.bases .global).toNat+cell.toNat*(o.nodes.size*o.nodes.size)*8+execution.output.toNat ∨
      (execution.bases .global).toNat+(cell.toNat+1)*(o.nodes.size*o.nodes.size)*8+execution.output.toNat≤p) :
    Concurrent.GlobalPublication.publish memory execution.events p=memory p := by
  apply Concurrent.GlobalPublication.outside
  intro owner access member global store
  obtain ⟨active,located⟩ := execution.global_store member store global
  rw [located]
  rcases apart with left | right
  · left; omega
  · right
    have next : cell.toNat*(o.nodes.size*o.nodes.size)+owner.val+1≤(cell.toNat+1)*(o.nodes.size*o.nodes.size) := by
      rw [Nat.add_mul]; omega
    omega

end PtxTorchLean.Poisson.PTX.CellWhole
