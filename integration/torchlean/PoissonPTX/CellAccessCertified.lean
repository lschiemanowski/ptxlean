import PoissonPTX.CellAccessBoundsQ1
import PoissonPTX.CellAccessBoundsQ2
import PoissonPTX.CellAccessBoundsQ3
import PoissonPTX.CellAccessBoundsQ4

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness

theorem access_bounds (lo : 2≤width) (hi : width≤5) : AccessBounds width := by
  interval_cases width
  · exact bounds_q1
  · exact bounds_q2
  · exact bounds_q3
  · exact bounds_q4

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
