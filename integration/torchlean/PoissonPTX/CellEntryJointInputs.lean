import PoissonPTX.CellEntryWordInputs
import PoissonPTX.CellEntryContinuation

namespace PtxTorchLean.Poisson.PTX.CellEntry.Control

/-- Array allocation, initial connectivity and physical input/output separation
supply the launch-only bounds used by source admission. -/
def InputLayout.of_gather
    (layout : CellGather.Layout (Local.beforeGather ctx width s) width cells source)
    (initial : s.core.global=memory)
    (cellsBefore : cells.toNat+layout.cellCount*(width*width)*4≤output.toNat)
    (sourceBefore : source.toNat+layout.pointCount*8≤output.toNat)
    (noWrap : ctx.arena.toNat+output.toNat≤2^64) :
    InputLayout memory ctx width cells source output := by
  have wide (v : BitVec 32) : (v.setWidth 64).toNat=v.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt]; have := v.isLt; omega
  have ids : ((Local.beforeGather ctx width s).regs 15).toNat=ctx.cell.toNat ∧
      ((Local.beforeGather ctx width s).regs 14).toNat=ctx.lane.toNat := by
    simp [Local.beforeGather,CellPrologue.finish,advance,wide]
  have base : ctx.arena.toNat=s.core.globalStart := by
    simpa only [Local.beforeGather,CellPrologue.finish,advance,Function.update_self,
      Function.update_of_ne (by decide : (0 : Nat)≠17),
      Function.update_of_ne (by decide : (0 : Nat)≠16),
      Function.update_of_ne (by decide : (0 : Nat)≠15),
      Function.update_of_ne (by decide : (0 : Nat)≠14)] using layout.globalBase
  have inside := CellGather.index_inside layout
  rw [ids.1,ids.2] at inside
  refine ⟨layout.pointCount,lt_trans inside layout.indexFits,by omega,sourceBefore,noWrap,?_⟩
  have good := layout.connectivity (ctx.cell.toNat*(width*width)+ctx.lane.toNat) inside
  simpa only [Local.beforeGather,CellPrologue.finish,advance,initial,← base] using good

/-- Derive both prefix source contracts from a single joint source account.
The continuation's store fence is obtained from its actual fetched execution. -/
theorem joint_sources {later : List (Concurrent.Event 32)}
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program width cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (pcs : ∀ u, (s.core.lanes u).pc=0)
    (done : ∀ u, (t.core.lanes u).pc=21) (lo : 2≤width) (hi : width≤5)
    (space : (bases .shared).toNat+7*width*width*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<width*width →
      InputLayout (memory .global) (CellPrologue.threadContext bases cell u) width cells source output)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (continuation t) later final)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds width output (continuation t))
    (indicesJoint : IndexSources.Compatible (memory .global) (events++later) indices indexChoices)
    (wordsJoint : Concurrent.Visibility.Compatible memory (events++later) wordChoices) :
    Concurrent.Visibility.Compatible memory events (fun _ _ => .initial) ∧
      IndexSources.Compatible (memory .global) events indices (fun _ _ => .initial) := by
  have positive : 0<width := by omega
  have fits : width*width<2^32 := by nlinarith
  obtain ⟨launch⟩ := launch run aligned pcs done positive fits space
  have lower (owner : Fin 32) (access : Concurrent.Access)
      (member : Concurrent.Event.data owner access∈later) (store : access.data.store=true)
      (global : access.space=.global) := output_fence lo hi launch body bounds member store global
  have inputs (u : Fin 32) (live : (CellPrologue.threadContext bases cell u).lane.toNat<width*width) := layout u (by simpa only [context_lane] using live)
  have values := joint_indices run aligned pcs positive fits inputs (fun _ => rfl) lower indicesJoint
  exact ⟨joint_words run aligned pcs positive fits values inputs (fun _ => rfl) lower wordsJoint,
    indices_compatible values⟩

end PtxTorchLean.Poisson.PTX.CellEntry.Control
