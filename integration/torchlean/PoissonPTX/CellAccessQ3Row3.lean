import PoissonPTX.CellAccessCertificate
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem certificate_q3_row3 : ∀ col : Fin 4,
    SequenceSafe 4 (CellMiddle.Numeric.seed 4 (3*4+col.val)) (program 4) := by decide +kernel
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
