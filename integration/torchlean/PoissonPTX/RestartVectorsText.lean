import PoissonPTX.RestartVectorsEntry
import PoissonPTX.UpdateXRZText

namespace PtxTorchLean.Poisson.PTX.RestartVectors

def rendered (count : BitVec 32) (source r diagonal boundary z p : Word) : List String :=
  (entry count source r diagonal boundary z p).map UpdateXRZ.instruction

end PtxTorchLean.Poisson.PTX.RestartVectors
