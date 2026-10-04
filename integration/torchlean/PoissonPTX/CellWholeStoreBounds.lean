import PoissonPTX.CellExecutionStores

namespace PtxTorchLean.Poisson.PTX.CellWhole
open Concurrent.CellConsumer.WithOutput

/-- Actual global stores need output-address bounds only for active lanes.
No coefficient tensor, numerical result or padding-lane address is assumed. -/
theorem global_store_active
    (run : Runs cfg bases cell width cells source output ctx start events indices final)
    (aligned : Concurrent.Aligned start.core) (pcs : ∀ u, (start.core.lanes u).pc=0)
    (running : ∀ u, start.halted u=false) (lo : 2≤width) (hi : width≤5)
    (space : (bases .shared).toNat+7*width*width*8≤2^64)
    (finished : ∀ u : Fin 32, u.val<width*width → 21+(front width).length+5≤(final.core.lanes u).pc)
    (bounds : ∀ u : Fin 32, u.val<width*width →
      cell.toNat*(width*width)+u.val<2^32 ∧
      (bases .global).toNat+(cell.toNat*(width*width)+u.val)*8+output.toNat<2^64)
    (member : Concurrent.Event.data owner access∈events)
    (store : access.data.store=true) (global : access.space=.global) :
    owner.val<width*width ∧
    access.data.address=(bases .global).toNat+(cell.toNat*(width*width)+owner.val)*8+output.toNat := by
  have positive : 0<width := by omega
  have small : width*width<2^32 := by nlinarith
  have past : 20<(final.core.lanes (0 : Fin 32)).pc := by
    have := finished 0 (by change 0<width*width; nlinarith)
    omega
  obtain ⟨before,after,ready,localFinal,eventEq,first,done,site,finalEq,body⟩ :=
    executions run aligned pcs running 0 past
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
    obtain ⟨launch⟩ := CellEntry.Control.launch first aligned pcs done positive small space
    have control := CellEntry.Control.from_run first aligned
      (fun u => CellEntry.Control.initial (s:=CellEntry.lane (entry start) u) (pcs u)) positive small
    have cellReg : ((CellEntry.continuation (entry ready)).core.lanes thread).regs 15=cell.setWidth 64 := by
      exact (control thread).2.2.2.1 (by change 4≤(ready.core.lanes thread).pc; rw [done]; decide)
    have baseReg : ((CellEntry.continuation (entry ready)).core.lanes thread).regs 0=bases .global := launch.global thread
    have laneNat : (((CellEntry.continuation (entry ready)).core.lanes thread).regs 14).toNat=thread.val := launch.lane_nat thread
    have active := Padding.access_active lo hi body launch.aligned launch.pcs localMember
    have bound := bounds thread active
    have cellSmall : cell.toNat<2^64 := by have := cell.isLt; omega
    refine ⟨active,?_⟩
    change recorded.data.address=_
    rw [Address.store_address lo hi body launch.aligned launch.pcs localMember store global,
      CellFinal.location_exact _ hi ?_ ?_,baseReg,laneNat,cellReg]
    · simp only [BitVec.toNat_setWidth,Nat.mod_eq_of_lt cellSmall]
    · simpa only [laneNat,cellReg,BitVec.toNat_setWidth,Nat.mod_eq_of_lt cellSmall] using bound.1
    · simpa only [baseReg,laneNat,cellReg,BitVec.toNat_setWidth,Nat.mod_eq_of_lt cellSmall] using bound.2

end PtxTorchLean.Poisson.PTX.CellWhole
