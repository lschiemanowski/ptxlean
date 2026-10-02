import PoissonPTX.CellEntryRebase
import PoissonPTX.CellEntryPublishedTensor

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- A gathered input vector and decoded coefficient tables determine the actual
cell result through the real prefix, barrier and numerical/output execution.
The two executions and prefix admission are still explicit modular premises. -/
theorem cell_result (o : Operator) (values : Array Float)
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program o.nodes.size cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
    (positive : 0<o.nodes.size) (small : o.nodes.size*o.nodes.size≤32)
    (space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      CellGather.Layout (Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (lane s u))
        o.nodes.size cells source)
    (connectivity : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → ∀ k<o.nodes.size*o.nodes.size,
      (read32 (s.core.lanes u).global ((s.core.lanes u).globalStart+cells.toNat+
        (cell.toNat*(o.nodes.size*o.nodes.size)+k)*4)).toNat=(o.mesh.cells[cell.toNat]!)[k]!)
    (contents : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size), ∀ k<(layout u active).pointCount,
      decode (read64 (s.core.lanes u).global ((s.core.lanes u).globalStart+source.toNat+k*8))=values[k]!)
    (lo : 2≤o.nodes.size) (hi : o.nodes.size≤5)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front o.nodes.size)
      (CellFinal.tail o.nodes.size output) (continuation t) later final)
    (reset : s.core.barrier=Ptx.Barrier.reset generation)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds o.nodes.size output (continuation t))
    (offset : Concurrent.CellConsumer.Coefficients.extent o.nodes.size≤output.toNat)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (thread : Fin 32) (i j : Fin o.nodes.size) (coordinate : thread.val=i.val*o.nodes.size+j.val)
    (finished : (Concurrent.CellConsumer.program o.nodes.size).length≤(final.core.lanes thread).pc) :
    decode ((final.core.lanes thread).regs 11)=Spec.get2 (localAction
      (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global 0)
      (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (o.nodes.size*o.nodes.size*8+32))
      (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (2*(o.nodes.size*o.nodes.size*8+32)))
      (Poisson.gather o values cell.toNat)) i j := by
  have result := body_result run aligned initial words indexSources pcs done positive (by omega) space
    (fun u h => CellGather.valid_of_layout (layout u h)) lo hi small body reset bounds offset
    joint performed thread i j coordinate finished
  rw [publication_torchlean o values run aligned initial words indexSources pcs done positive small space
    layout connectivity contents] at result
  exact result

/-- Whole-cell output publication after the actual gather and arithmetic runs. -/
theorem cell_tensor (o : Operator) (values : Array Float)
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program o.nodes.size cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (words : Concurrent.Visibility.Compatible memory events chosen)
    (indexSources : IndexSources.Compatible (memory .global) events indices selected)
    (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
    (positive : 0<o.nodes.size) (small : o.nodes.size*o.nodes.size≤32)
    (space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      CellGather.Layout (Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (lane s u))
        o.nodes.size cells source)
    (connectivity : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → ∀ k<o.nodes.size*o.nodes.size,
      (read32 (s.core.lanes u).global ((s.core.lanes u).globalStart+cells.toNat+
        (cell.toNat*(o.nodes.size*o.nodes.size)+k)*4)).toNat=(o.mesh.cells[cell.toNat]!)[k]!)
    (contents : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size), ∀ k<(layout u active).pointCount,
      decode (read64 (s.core.lanes u).global ((s.core.lanes u).globalStart+source.toNat+k*8))=values[k]!)
    (lo : 2≤o.nodes.size) (hi : o.nodes.size≤5)
    (body : Concurrent.WithTail.Runs cfg bodyContext (Concurrent.CellConsumer.WithOutput.front o.nodes.size)
      (CellFinal.tail o.nodes.size output) (continuation t) later final)
    (reset : s.core.barrier=Ptx.Barrier.reset generation)
    (bounds : Concurrent.CellConsumer.WithOutput.OutputBounds o.nodes.size output (continuation t))
    (offset : Concurrent.CellConsumer.Coefficients.extent o.nodes.size≤output.toNat)
    (joint : Concurrent.Visibility.Compatible memory (events++later) allSources)
    (performed : Concurrent.Visibility.Performed (events++later) allSources)
    (permutation : order.Perm later)
    (finished : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      (Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤(final.core.lanes u).pc) :
    Concurrent.CellConsumer.WithOutput.Publication.tensor o.nodes.size (bases .global) (cell.setWidth 64) output
      (Concurrent.GlobalPublication.publish outputMemory order)=localAction
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global 0)
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (o.nodes.size*o.nodes.size*8+32))
        (Concurrent.CellMiddle.Numeric.initialTensor o.nodes.size bases memory .global (2*(o.nodes.size*o.nodes.size*8+32)))
        (Poisson.gather o values cell.toNat) := by
  have result := published_result run aligned initial words indexSources pcs done positive (by omega) space
    (fun u h => CellGather.valid_of_layout (layout u h)) lo hi small body reset bounds offset
    joint performed permutation finished (outputMemory:=outputMemory)
  rw [publication_torchlean o values run aligned initial words indexSources pcs done positive small space
    layout connectivity contents] at result
  exact result

end PtxTorchLean.Poisson.PTX.CellEntry
