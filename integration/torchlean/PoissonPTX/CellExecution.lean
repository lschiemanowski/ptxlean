import PoissonPTX.CellOperatorCorrespondence

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- The explicit inputs and execution evidence for one cell entry. There is
no desired tensor or output-value field. Necessary memory-source admission is
kept distinct from fetched execution and the represented input coefficients. -/
structure Execution (o : Operator) (values : Array Float) (cell : BitVec 32) where
  cfg : Concurrent.Config 32
  bases : Space → Word
  (cells source output : Word)
  bodyContext : Fin 32 → Kernel.Context
  memory : Space → Memory
  (start final : State)
  events : List (Concurrent.Event 32)
  indices : List (Fin 32 × IndexSources.Access)
  allSources : Nat → Fin 8 → Sources.Origin Nat
  indexChoices : Nat → Fin 4 → Sources.Origin Nat
  generation : Nat
  run : Runs cfg bases cell o.nodes.size cells source output bodyContext start events indices final
  aligned : Concurrent.Aligned start.core
  initial : ∀ u, (start.core.lanes u).global=memory .global
  pcs : ∀ u, (start.core.lanes u).pc=0
  running : ∀ u, start.halted u=false
  positive : 0<o.nodes.size
  small : o.nodes.size*o.nodes.size≤32
  space : (bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64
  layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
    CellGather.Layout (CellEntry.Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (CellEntry.lane (entry start) u))
      o.nodes.size cells source
  cellsBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
    cells.toNat+(layout u active).cellCount*(o.nodes.size*o.nodes.size)*4≤output.toNat
  sourceBefore : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size),
    source.toNat+(layout u active).pointCount*8≤output.toNat
  connectivity : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → ∀ k<o.nodes.size*o.nodes.size,
    (read32 (start.core.lanes u).global ((start.core.lanes u).globalStart+cells.toNat+
      (cell.toNat*(o.nodes.size*o.nodes.size)+k)*4)).toNat=(o.mesh.cells[cell.toNat]!)[k]!
  contents : ∀ (u : Fin 32) (active : u.val<o.nodes.size*o.nodes.size), ∀ k<(layout u active).pointCount,
    decode (read64 (start.core.lanes u).global ((start.core.lanes u).globalStart+source.toNat+k*8))=values[k]!
  coefficients : CoefficientRepresentation.Represents o bases memory
  lo : 2≤o.nodes.size
  hi : o.nodes.size≤5
  reset : start.core.barrier=Ptx.Barrier.reset generation
  bounds : OutputLayout bases cell o.nodes.size output
  offset : Concurrent.CellConsumer.Coefficients.extent o.nodes.size≤output.toNat
  jointIndices : IndexSources.Compatible (memory .global) events indices indexChoices
  joint : Concurrent.Visibility.Compatible memory events allSources
  performed : Concurrent.Visibility.Performed events allSources
  finished : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
    21+(Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤(final.core.lanes u).pc

variable {o : Operator} {values : Array Float} {cell : BitVec 32}

/-- A proved consequence of the recorded execution; the output memory before
publication is arbitrary because active stores are derived from completion. -/
theorem Execution.tensor (execution : Execution o values cell) (outputMemory : Memory) :
    Concurrent.CellConsumer.WithOutput.Publication.tensor o.nodes.size (execution.bases .global) (cell.setWidth 64) execution.output
      (Concurrent.GlobalPublication.publish outputMemory execution.events)=
        localAction o.b o.d o.w (Poisson.gather o values cell.toNat) :=
  operator_tensor o values execution.run execution.aligned execution.initial execution.pcs execution.running
    execution.positive execution.small execution.space execution.layout execution.cellsBefore execution.sourceBefore
    execution.connectivity execution.contents execution.coefficients execution.lo execution.hi execution.reset
    execution.bounds execution.offset execution.jointIndices execution.joint execution.performed execution.finished

end PtxTorchLean.Poisson.PTX.CellWhole
