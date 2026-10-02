import PoissonPTX.CellGridExecution

namespace PtxTorchLean.Poisson.PTX.CellWhole
variable {o : Operator} {values : Array Float} {cell : BitVec 32}

/-- Forget source evidence while retaining the exact same fetched execution. -/
def Execution.candidate (execution : Execution o values cell) : Candidate o values cell where
  cfg := execution.cfg
  bases := execution.bases
  cells := execution.cells
  source := execution.source
  output := execution.output
  bodyContext := execution.bodyContext
  memory := execution.memory
  start := execution.start
  final := execution.final
  events := execution.events
  indices := execution.indices
  generation := execution.generation
  run := execution.run
  aligned := execution.aligned
  initial := execution.initial
  pcs := execution.pcs
  running := execution.running
  positive := execution.positive
  small := execution.small
  space := execution.space
  layout := execution.layout
  cellsBefore := execution.cellsBefore
  sourceBefore := execution.sourceBefore
  connectivity := execution.connectivity
  contents := execution.contents
  coefficients := execution.coefficients
  lo := execution.lo
  hi := execution.hi
  reset := execution.reset
  bounds := execution.bounds
  offset := execution.offset
  finished := execution.finished

/-- The candidate family keeps the original inputs, states, events and layouts. -/
def Family.candidates (family : Family o values) : CellGrid.Candidates o values :=
  ⟨family.base,family.output,family.memory,family.small,
    fun block => (family.execution block).candidate,
    family.sameInitial,family.sameCTA,family.sameBase,family.sameOutput⟩

end PtxTorchLean.Poisson.PTX.CellWhole
