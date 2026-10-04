import PoissonPTX.CellWholeExists
import PoissonPTX.CellExecution

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Input bytes, launch geometry and their TorchLean representation. No run,
completion, source assignment or desired output is part of this interface. -/
structure Inputs (o : Operator) (values : Array Float) (cell : BitVec 32) where
  cfg : Concurrent.Config 32
  bases : Space → Word
  (cells source output : Word)
  bodyContext : Fin 32 → Kernel.Context
  memory : Space → Memory
  start : CellEntry.State 32
  generation : Nat
  initial : ∀ u, (start.core.lanes u).global=memory .global
  pcs : ∀ u, (start.core.lanes u).pc=0
  layout : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size →
    CellGather.Layout (CellEntry.Local.beforeGather (CellPrologue.threadContext bases cell u) o.nodes.size (CellEntry.lane start u))
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
  site : start.core.site=none
  physical : ∀ u, Concurrent.CellConsumer.Witness.Allocation o.nodes.size bases (start.core.lanes u)
  outputAligned : output.toNat%8=0
  outputFits : ∀ u : Fin 32, u.val<o.nodes.size*o.nodes.size → (cell.toNat*(o.nodes.size*o.nodes.size)+u.val)*8+output.toNat+8≤(start.core.lanes u).globalBytes

/-- Record which physical input an execution realizes. -/
def Inputs.Realizes (input : Inputs o values cell) (execution : Execution o values cell) : Prop :=
  execution.cfg=input.cfg ∧ execution.bases=input.bases ∧ execution.cells=input.cells ∧
  execution.source=input.source ∧ execution.output=input.output ∧ execution.bodyContext=input.bodyContext ∧
  execution.memory=input.memory ∧ execution.start=begin input.start

/-- Construct the execution evidence needed by the universal correspondence
theorem from arbitrary represented valid inputs. -/
theorem Inputs.exists_execution (input : Inputs o values cell) :
    ∃ execution : Execution o values cell, input.Realizes execution := by
  have positive : 0<o.nodes.size := by have := input.lo; omega
  have small : o.nodes.size*o.nodes.size≤32 := by have := input.hi; nlinarith
  have space : (input.bases .shared).toNat+7*o.nodes.size*o.nodes.size*8≤2^64 := by
    have allocation := input.physical (0 : Fin 32) .shared
    change (input.start.core.lanes 0).sharedStart=(input.bases .shared).toNat ∧ _ at allocation
    have extent := allocation.2.2.1
    change 7*o.nodes.size*o.nodes.size*8≤(input.start.core.lanes 0).sharedBytes at extent
    have nowrap := allocation.2.2.2
    change (input.start.core.lanes 0).sharedStart+(input.start.core.lanes 0).sharedBytes≤2^64 at nowrap
    omega
  obtain ⟨final,events,indices,run,recorded,indexWords,halted,done,barrier,site⟩ :=
    exists_recorded input.cfg input.bodyContext input.start input.memory input.lo input.hi input.pcs input.reset input.site
      input.initial input.physical (by
        intro u active
        have live : u.val<o.nodes.size*o.nodes.size := by simpa only [CellEntry.context_lane] using active
        exact CellGather.valid_of_layout (input.layout u live))
      input.outputAligned (fun u => (input.bounds u).1) input.outputFits
  obtain ⟨joint,performed,jointIndices⟩ := recorded_sources recorded indexWords
  let execution : Execution o values cell := {
    cfg:=input.cfg, bases:=input.bases, cells:=input.cells, source:=input.source, output:=input.output,
    bodyContext:=input.bodyContext, memory:=input.memory, start:=begin input.start, final:=final,
    events:=events, indices:=indices, allSources:=Concurrent.ByteHistory.sources events,
    indexChoices:=fun _ _ => .initial, generation:=input.generation,
    run:=run, aligned:=by intro u waiting; simp [begin,input.reset,Ptx.Barrier.reset] at waiting,
    initial:=input.initial, pcs:=input.pcs, running:=fun _ => rfl, positive:=positive, small:=small, space:=space,
    layout:=input.layout, cellsBefore:=input.cellsBefore, sourceBefore:=input.sourceBefore,
    connectivity:=input.connectivity, contents:=input.contents, coefficients:=input.coefficients,
    lo:=input.lo, hi:=input.hi, reset:=input.reset, bounds:=input.bounds, offset:=input.offset,
    jointIndices:=jointIndices, joint:=joint, performed:=performed,
    finished:=by intro u _; rw [done]; omega }
  exact ⟨execution,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Finite execution existence and numerical correspondence together. The
published values follow from the actual run, not from an input equality. -/
theorem Inputs.exists_corresponding (input : Inputs o values cell) (outputMemory : Memory) :
    ∃ execution : Execution o values cell, input.Realizes execution ∧
      Concurrent.CellConsumer.WithOutput.Publication.tensor o.nodes.size (input.bases .global)
        (cell.setWidth 64) input.output (Concurrent.GlobalPublication.publish outputMemory execution.events)=
          localAction o.b o.d o.w (Poisson.gather o values cell.toNat) := by
  obtain ⟨execution,realizes⟩ := input.exists_execution
  refine ⟨execution,realizes,?_⟩
  simpa only [realizes.2.1,realizes.2.2.2.2.1] using execution.tensor outputMemory

end PtxTorchLean.Poisson.PTX.CellWhole
