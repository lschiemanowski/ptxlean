import PoissonPTX.CellWholeSources
import PoissonPTX.CellWholeBounds

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- A single absolute-counter entry execution publishes the TorchLean cell
calculation. Its prefix/body split, input admission and source-history change
are conclusions of the proof. Coefficients remain represented input tables;
publication is a mathematical merge of actual global stores. -/
theorem tensor (o : Operator) (values : Array Float)
    (run : Runs cfg bases cell o.nodes.size cells source output bodyContext start events indices final)
    (aligned : Concurrent.Aligned start.core) (initial : ∀ u, (start.core.lanes u).global=memory .global)
    (pcs : ∀ u, (start.core.lanes u).pc=0) (running : ∀ u, start.halted u=false)
    (positive : 0<o.nodes.size) (small : o.nodes.size*o.nodes.size≤32)
    (space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      CellGather.Layout (CellEntry.Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (CellEntry.lane (entry start) u))
        o.nodes.size cells source)
    (cellsBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
      cells.toNat+(layout u active).cellCount*(o.nodes.size*o.nodes.size)*4≤output.toNat)
    (sourceBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
      source.toNat+(layout u active).pointCount*8≤output.toNat)
    (connectivity : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → ∀ k<o.nodes.size*o.nodes.size,
      (read32 (start.core.lanes u).global ((start.core.lanes u).globalStart+cells.toNat+
        (cell.toNat*(o.nodes.size*o.nodes.size)+k)*4)).toNat=(o.mesh.cells[cell.toNat]!)[k]!)
    (contents : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size), ∀ k<(layout u active).pointCount,
      decode (read64 (start.core.lanes u).global ((start.core.lanes u).globalStart+source.toNat+k*8))=values[k]!)
    (lo : 2≤o.nodes.size) (hi : o.nodes.size≤5)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (bounds : OutputLayout bases cell o.nodes.size output)
    (offset : Concurrent.CellConsumer.Coefficients.extent o.nodes.size≤output.toNat)
    (jointIndices : IndexSources.Compatible (memory .global) events indices indexChoices)
    (joint : Concurrent.Visibility.Compatible memory events allSources)
    (performed : Concurrent.Visibility.Performed events allSources)
    (finished : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      21+(Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤(final.core.lanes u).pc) :
    Concurrent.CellConsumer.WithOutput.Publication.tensor o.nodes.size (bases .global) (cell.setWidth 64) output
      (Concurrent.GlobalPublication.publish outputMemory events)=localAction
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global 0)
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (o.nodes.size*o.nodes.size*8+32))
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (2*(o.nodes.size*o.nodes.size*8+32)))
        (Poisson.gather o values cell.toNat) := by
  have live : (0 : Fin 32).val<o.nodes.size*o.nodes.size := by change 0<o.nodes.size*o.nodes.size; nlinarith
  have past : 20<(final.core.lanes (0 : Fin 32)).pc := by have := finished 0 live; omega
  obtain ⟨before,after,ready,localFinal,eventEq,first,done,site,finalEq,body⟩ :=
    executions run aligned pcs running 0 past
  obtain ⟨wordSources,performs,indexSources⟩ := sources first aligned pcs done body
    (by rw [← eventEq]; exact joint) (by rw [← eventEq]; exact performed)
    (by rw [← eventEq]; exact jointIndices)
  have outputBounds := output_bounds first aligned pcs done positive (by omega) bounds
  have complete (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size) :
      (Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤(localFinal.core.lanes u).pc := by
    have h := finished u active
    rw [finalEq] at h
    change 21+(Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤
      (localFinal.core.lanes u).pc+21 at h
    omega
  have result := CellEntry.joint_cell_tensor o values first aligned initial pcs done positive small space
    layout cellsBefore sourceBefore connectivity contents lo hi body reset outputBounds offset
    indexSources wordSources performs (List.Perm.refl after) complete (outputMemory:=outputMemory)
  obtain ⟨renameKey,related⟩ := histories first aligned pcs done body
  have published : Concurrent.GlobalPublication.publish outputMemory events=
      Concurrent.GlobalPublication.publish outputMemory after := by
    rw [eventEq,← Concurrent.Relabel.published related,Concurrent.GlobalPublication.append,
      Concurrent.GlobalPublication.no_stores (fun owner access member store => CellEntry.no_global_store first member store)]
  rw [published]
  exact result

end PtxTorchLean.Poisson.PTX.CellWhole
