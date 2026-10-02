import PoissonPTX.CellAssemblyReference
import PoissonPTX.CellAssemblyChecks

namespace PtxTorchLean.Poisson.PTX.ArrayOperator.Checks
open CellAssemblyWitness

/-- The public executable reference agrees with the nonzero cell/assembly
example; the generic proof connects every valid represented input. -/
theorem reference_nonzero : Poisson.apply operator values=.ok #[8] := by
  rw [apply_correspondence operator meshShape rfl values (by decide) (by decide +kernel)]
  decide +kernel

theorem wrong_length : Poisson.apply operator #[] = .error "expected vector of length 1, got 0" := by decide +kernel

theorem nonfinite : Poisson.apply operator #[Float.ofBits 0x7ff0000000000000] = .error "vector must be finite" := by decide +kernel

/-- Reordering rounded additions would invalidate this example. The actual
nested array loops retain the original encounter order. -/
theorem cancellation_order :
    scatter #[#[0,0,0],#[0]] #[#[9007199254740992,1,-9007199254740992],#[2]] 1=#[2] ∧
    scatter #[#[0,0,0],#[0]] #[#[9007199254740992,-9007199254740992,1],#[2]] 1=#[3] := by
  decide +kernel

end PtxTorchLean.Poisson.PTX.ArrayOperator.Checks
