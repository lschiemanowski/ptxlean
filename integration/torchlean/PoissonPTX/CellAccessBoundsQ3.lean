import PoissonPTX.CellAccessQ3Row0
import PoissonPTX.CellAccessQ3Row1
import PoissonPTX.CellAccessQ3Row2
import PoissonPTX.CellAccessQ3Row3
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
theorem certificate_q3 : Certificate 4 := by
  intro lane
  fin_cases lane
  · exact certificate_q3_row0 ⟨0,by decide⟩
  · exact certificate_q3_row0 ⟨1,by decide⟩
  · exact certificate_q3_row0 ⟨2,by decide⟩
  · exact certificate_q3_row0 ⟨3,by decide⟩
  · exact certificate_q3_row1 ⟨0,by decide⟩
  · exact certificate_q3_row1 ⟨1,by decide⟩
  · exact certificate_q3_row1 ⟨2,by decide⟩
  · exact certificate_q3_row1 ⟨3,by decide⟩
  · exact certificate_q3_row2 ⟨0,by decide⟩
  · exact certificate_q3_row2 ⟨1,by decide⟩
  · exact certificate_q3_row2 ⟨2,by decide⟩
  · exact certificate_q3_row2 ⟨3,by decide⟩
  · exact certificate_q3_row3 ⟨0,by decide⟩
  · exact certificate_q3_row3 ⟨1,by decide⟩
  · exact certificate_q3_row3 ⟨2,by decide⟩
  · exact certificate_q3_row3 ⟨3,by decide⟩
theorem bounds_q3 : AccessBounds 4 := certificate_bounds certificate_q3
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
