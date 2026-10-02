import PoissonPTX.CellEntryJointInputs
import PoissonPTX.CellEntryCorrespondence

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- The published tensor follows from joint word/index source constraints.
Prefix input admission is derived from actual control, loads and output stores,
using array separation; it is no longer an additional premise. -/
theorem joint_cell_tensor (o : Operator) (values : Array Float)
    (run : Runs cfg (CellPrologue.threadContext bases cell) (program o.nodes.size cells source) s events indices t)
    (aligned : Concurrent.Aligned s.core) (initial : ∀ u, (s.core.lanes u).global=memory .global)
    (pcs : ∀ u, (s.core.lanes u).pc=0) (done : ∀ u, (t.core.lanes u).pc=21)
    (positive : 0<o.nodes.size) (small : o.nodes.size*o.nodes.size≤32)
    (space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64)
    (layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
      CellGather.Layout (Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (lane s u))
        o.nodes.size cells source)
    (cellsBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
      cells.toNat+(layout u active).cellCount*(o.nodes.size*o.nodes.size)*4≤output.toNat)
    (sourceBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
      source.toNat+(layout u active).pointCount*8≤output.toNat)
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
    (jointIndices : IndexSources.Compatible (memory .global) (events++later) indices indexChoices)
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
  obtain ⟨launch⟩ := Control.launch run aligned pcs done positive (by omega) space
  have noWrap : (bases .global).toNat+output.toNat≤2^64 := by
    have bound := (bounds (0 : Fin 32)).2
    have arena : ((continuation t).core.lanes (0 : Fin 32)).regs 0=bases .global := launch.global _
    rw [arena] at bound
    omega
  have inputs (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size) :=
    Control.InputLayout.of_gather (layout u active) (initial u)
      (cellsBefore u active) (sourceBefore u active) noWrap
  obtain ⟨words,indexSources⟩ := Control.joint_sources run aligned pcs done lo hi space inputs
    body bounds jointIndices joint
  exact cell_tensor o values run aligned initial words indexSources pcs done positive small space
    layout connectivity contents lo hi body reset bounds offset joint performed permutation finished

end PtxTorchLean.Poisson.PTX.CellEntry
