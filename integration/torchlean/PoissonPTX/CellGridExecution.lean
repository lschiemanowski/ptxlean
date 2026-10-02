import PoissonPTX.CellGridAdmission
import PoissonPTX.CellGridFamily

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- One actual interleaved launch, tied to the input layouts and complete local
executions used for address reasoning. Neither the chosen sources nor the
computed cell outputs are assumed correct by this record. -/
structure Execution (o : Operator) (values : Array Float) where
  candidates : Candidates o values
  launch : Launch o.mesh.cells.size
  width : launch.width=o.nodes.size
  configs : ∀ block, (candidates.candidate block).cfg=config block
  bases : ∀ block, (candidates.candidate block).bases=launch.bases block
  cells : ∀ block, (candidates.candidate block).cells=launch.cells
  source : ∀ block, (candidates.candidate block).source=launch.source
  output : ∀ block, (candidates.candidate block).output=launch.output
  contexts : ∀ block, (candidates.candidate block).bodyContext=launch.context block
  events : List (Event o.mesh.cells.size)
  indices : List (Index o.mesh.cells.size)
  run : Runs launch (fun block => (candidates.candidate block).start) events indices
    (fun block => (candidates.candidate block).final)
  projected : ∀ block, forBlock block events=(candidates.candidate block).events
  indexProjected : ∀ block, forBlock block indices=(candidates.candidate block).indices

/-- Admission retains the one grid history, including private shared sources
and performed writes across each block's actual barriers. -/
structure Admitted (o : Operator) (values : Array Float) extends Execution o values where
  wordSource : Sources o.mesh.cells.size
  indexSource : IndexChoices o.mesh.cells.size
  words : Compatible candidates.memory (fun block => (candidates.candidate block).memory .shared) events wordSource
  indexes : IndexCompatible candidates.memory events indices indexSource
  performed : Performed events wordSource

variable {o : Operator} {values : Array Float}

def Admitted.family (grid : Admitted o values) : CellWhole.Family o values :=
  grid.candidates.withSources grid.events grid.indices grid.projected grid.indexProjected
    grid.wordSource grid.indexSource grid.words grid.indexes grid.performed

/-- The value theorem is about the chronological global stores of the actual
interleaved run; no whole-block serialization of publication is needed. -/
theorem Admitted.entry (grid : Admitted o values) (cell : Fin o.mesh.cells.size)
    (i j : Fin o.nodes.size) :
    decode (read64 (publish grid.candidates.memory grid.events) (grid.family.address cell i j))=
      Correspondence.entries (localAction o.b o.d o.w (gather o values cell.val)) i j := by
  exact family_entry grid.family grid.events grid.projected cell i j

theorem Admitted.before (grid : Admitted o values) (p : Nat)
    (before : p<grid.candidates.base.toNat+grid.candidates.output.toNat) :
    publish grid.candidates.memory grid.events p=grid.candidates.memory p :=
  family_before grid.family grid.events grid.projected grid.candidates.memory p before

end PtxTorchLean.Poisson.PTX.CellGrid
