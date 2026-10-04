import PoissonPTX.CellExecutionExists
import PoissonPTX.CellGridExists

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- A finite mesh launch described only by input storage and representation.
Each block owns its shared allocation; all blocks use the same global input
memory and contiguous output array. -/
structure InputFamily (o : Operator) (values : Array Float) where
  (base cells source output : Word)
  memory : Memory
  small : o.mesh.cells.size≤2^32
  input : ∀ block : Fin o.mesh.cells.size, Inputs o values (BitVec.ofNat 32 block.val)
  sameInitial : ∀ block, (input block).memory .global=memory
  sameCTA : ∀ block, (input block).cfg.cta=block.val
  sameBase : ∀ block, (input block).bases .global=base
  sameCells : ∀ block, (input block).cells=cells
  sameSource : ∀ block, (input block).source=source
  sameOutput : ∀ block, (input block).output=output

/-- Construct all cell runs and a joint admitted grid from represented input
bytes. No per-cell execution or completed tensor is assumed. -/
theorem InputFamily.exists_grid (inputs : InputFamily o values) :
    ∃ family : Family o values,
      (∀ block, (inputs.input block).Realizes (family.execution block)) ∧
      ∃ grid : CellGrid.Admitted o values, grid.candidates=family.candidates := by
  classical
  choose execution realizes using fun block => (inputs.input block).exists_execution
  let family : Family o values := {
    base:=inputs.base, output:=inputs.output, memory:=inputs.memory, small:=inputs.small,
    execution:=execution,
    sameInitial:=by intro block; rw [(realizes block).2.2.2.2.2.2.1]; exact inputs.sameInitial block,
    sameCTA:=by intro block; rw [(realizes block).1]; exact inputs.sameCTA block,
    sameBase:=by intro block; rw [(realizes block).2.1]; exact inputs.sameBase block,
    sameOutput:=by intro block; exact (realizes block).2.2.2.2.1.trans (inputs.sameOutput block) }
  obtain ⟨grid,same⟩ := CellGrid.family_exists family inputs.cells inputs.source
    (by intro block; exact (realizes block).2.2.1.trans (inputs.sameCells block))
    (by intro block; exact (realizes block).2.2.2.1.trans (inputs.sameSource block))
  exact ⟨family,realizes,grid,same⟩

end PtxTorchLean.Poisson.PTX.CellWhole
