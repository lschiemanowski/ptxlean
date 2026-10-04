import PoissonPTX.CellAccessQ4Row0
import PoissonPTX.CellAccessQ4Row1
import PoissonPTX.CellAccessQ4Row2
import PoissonPTX.CellAccessQ4Row3
import PoissonPTX.CellAccessQ4Row4
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
theorem certificate_q4 : Certificate 5 := by
  intro lane
  fin_cases lane
  · exact certificate_q4_row0 ⟨0,by decide⟩
  · exact certificate_q4_row0 ⟨1,by decide⟩
  · exact certificate_q4_row0 ⟨2,by decide⟩
  · exact certificate_q4_row0 ⟨3,by decide⟩
  · exact certificate_q4_row0 ⟨4,by decide⟩
  · exact certificate_q4_row1 ⟨0,by decide⟩
  · exact certificate_q4_row1 ⟨1,by decide⟩
  · exact certificate_q4_row1 ⟨2,by decide⟩
  · exact certificate_q4_row1 ⟨3,by decide⟩
  · exact certificate_q4_row1 ⟨4,by decide⟩
  · exact certificate_q4_row2 ⟨0,by decide⟩
  · exact certificate_q4_row2 ⟨1,by decide⟩
  · exact certificate_q4_row2 ⟨2,by decide⟩
  · exact certificate_q4_row2 ⟨3,by decide⟩
  · exact certificate_q4_row2 ⟨4,by decide⟩
  · exact certificate_q4_row3 ⟨0,by decide⟩
  · exact certificate_q4_row3 ⟨1,by decide⟩
  · exact certificate_q4_row3 ⟨2,by decide⟩
  · exact certificate_q4_row3 ⟨3,by decide⟩
  · exact certificate_q4_row3 ⟨4,by decide⟩
  · exact certificate_q4_row4 ⟨0,by decide⟩
  · exact certificate_q4_row4 ⟨1,by decide⟩
  · exact certificate_q4_row4 ⟨2,by decide⟩
  · exact certificate_q4_row4 ⟨3,by decide⟩
  · exact certificate_q4_row4 ⟨4,by decide⟩
theorem bounds_q4 : AccessBounds 5 := certificate_bounds certificate_q4
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
