import PoissonQuadCLI

/-- Numerical Poisson demo; failure is a nonzero exit in single-demo mode. -/
def main (args : List String) : IO UInt32 := PtxTorchLean.Poisson.CLI.run args

#print axioms main
