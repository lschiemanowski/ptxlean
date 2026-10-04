import PoissonPTX.CellAccessCertificate
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem certificate_q2 : Certificate 3 := by decide +kernel
theorem bounds_q2 : AccessBounds 3 := certificate_bounds certificate_q2
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
