import PoissonPTX.CellExecutionStores

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Input representation, fetched execution and completion before assigning
read sources. This lets address separation be established without assuming the
source-admission result it will later justify. No output value is a field. -/
structure Candidate (o : Operator) (values : Array Float) (cell : BitVec 32) where
  cfg : Concurrent.Config 32
  bases : Space → Word
  (cells source output : Word)
  bodyContext : Fin 32 → Kernel.Context
  memory : Space → Memory
  (start final : State)
  events : List (Concurrent.Event 32)
  indices : List (Fin 32 × IndexSources.Access)
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
  finished : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
    21+(Concurrent.CellConsumer.WithOutput.front o.nodes.size).length+5≤(final.core.lanes u).pc

variable {o : Operator} {values : Array Float} {cell : BitVec 32}

def Candidate.withSources (candidate : Candidate o values cell)
    (allSources : Nat → Fin 8 → Sources.Origin Nat)
    (indexChoices : Nat → Fin 4 → Sources.Origin Nat)
    (jointIndices : IndexSources.Compatible (candidate.memory .global) candidate.events candidate.indices indexChoices)
    (joint : Concurrent.Visibility.Compatible candidate.memory candidate.events allSources)
    (performed : Concurrent.Visibility.Performed candidate.events allSources) : Execution o values cell where
  cfg := candidate.cfg
  bases := candidate.bases
  cells := candidate.cells
  source := candidate.source
  output := candidate.output
  bodyContext := candidate.bodyContext
  memory := candidate.memory
  start := candidate.start
  final := candidate.final
  events := candidate.events
  indices := candidate.indices
  generation := candidate.generation
  run := candidate.run
  aligned := candidate.aligned
  initial := candidate.initial
  pcs := candidate.pcs
  running := candidate.running
  positive := candidate.positive
  small := candidate.small
  space := candidate.space
  layout := candidate.layout
  cellsBefore := candidate.cellsBefore
  sourceBefore := candidate.sourceBefore
  connectivity := candidate.connectivity
  contents := candidate.contents
  coefficients := candidate.coefficients
  lo := candidate.lo
  hi := candidate.hi
  reset := candidate.reset
  bounds := candidate.bounds
  offset := candidate.offset
  finished := candidate.finished
  allSources := allSources
  indexChoices := indexChoices
  jointIndices := jointIndices
  joint := joint
  performed := performed

open Concurrent.CellConsumer.WithOutput
theorem Candidate.global_store (execution : Candidate o values cell)
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


end PtxTorchLean.Poisson.PTX.CellWhole
