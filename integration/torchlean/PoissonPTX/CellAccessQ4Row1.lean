import PoissonPTX.CellAccessCertificate
namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
theorem certificate_q4_row1 : ∀ col : Fin 5,
    SequenceSafe 5 (CellMiddle.Numeric.seed 5 (1*5+col.val)) (program 5) := by decide +kernel
end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
