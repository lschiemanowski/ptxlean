import PoissonPTX.ScalarText
import PoissonPTX.ScalarStartExists
import PoissonPTX.ScalarStartPublication
import PoissonPTX.ScalarAlphaCorrect
import PoissonPTX.ScalarBetaExists

namespace PtxTorchLean.Poisson.PTX.Scalar.Text

def start (offset : Field → Word) : List String := (Start.entry offset).map instruction
def alpha (offset : Field → Word) : List String := (Alpha.entry offset).map instruction
def beta (offset : Field → Word) : List String := (Beta.entry offset).map instruction

end PtxTorchLean.Poisson.PTX.Scalar.Text
