import PoissonPTX.CellCoefficientRepresentation

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Full native-counter cell execution computes the particular represented
TorchLean operator, including its own coefficient tables. -/
theorem operator_tensor (o : Operator) (values : Array Float)
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
    (coefficients : CoefficientRepresentation.Represents o bases memory)
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
      (Concurrent.GlobalPublication.publish outputMemory events)=localAction o.b o.d o.w (Poisson.gather o values cell.toNat) := by
  rw [← CoefficientRepresentation.calculation coefficients]
  exact tensor o values run aligned initial pcs running positive small space layout cellsBefore
    sourceBefore connectivity contents lo hi reset bounds offset jointIndices joint performed finished

end PtxTorchLean.Poisson.PTX.CellWhole
