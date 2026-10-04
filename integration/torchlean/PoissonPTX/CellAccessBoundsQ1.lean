import PoissonPTX.CellAccessCertificate
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem certificate_q1 : Certificate 2 := by decide +kernel
theorem bounds_q1 : AccessBounds 2 := certificate_bounds certificate_q1
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
