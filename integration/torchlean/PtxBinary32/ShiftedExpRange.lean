import PtxBinary32.ShiftedExpProgram

/-! A bound on actual exponential outputs for the subsequent sum. This uses
the actual encoded base-two argument, independently of the natural-exp budget. -/
namespace Ptx.Binary32.ShiftedExp
open TorchLean.Floats (round32)

/-- All permitted outputs have magnitude at most two; nonnegativity is not
assumed or asserted for the conservative approximation neighborhood. -/
theorem output_range (input maximum negative shifted product output : Word) (x m : ℝ)
    (inputValue : finiteReal input=some x) (maximumValue : finiteReal maximum=some m)
    (bounds : InputBounds x m)
    (negate : Ptx.Binary32.Results .mul maximum 0xbf800000 negative)
    (shift : Ptx.Binary32.Results .add input negative shifted)
    (multiply : Ptx.Binary32.Results .mul shifted ExpArgument.constantWord product)
    (approximate : Exponential.Results product output) :
    ∃ u, finiteReal output=some u ∧ |u|≤2 := by
  have h := shift_real input maximum negative shifted x m inputValue maximumValue bounds negate shift
  have converted := ExpArgument.product_real shifted product _ h.2.1 h.2.2.1
    (ExpArgument.bounded_product_range _ h.2.2.2.1) multiply
  obtain ⟨u,value,error⟩ := Exponential.finite_error product output _ converted.1 approximate
  have positive : 0<(2:ℝ)^(round32 (round32 (x-m)*ExpArgument.constantValue)) := Real.rpow_pos_of_pos (by norm_num) _
  have upper : (2:ℝ)^(round32 (round32 (x-m)*ExpArgument.constantValue))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) converted.2
  refine ⟨u,value,?_⟩
  have magnitude := abs_le.mp error
  exact abs_le.mpr (by constructor <;> linarith)

end Ptx.Binary32.ShiftedExp

namespace Ptx.Scalar.ShiftedExp
/-- The bound concerns the destination of the actual fetched four-step sequence. -/
theorem output_range (target : Ptx.Target) (s t : Scalar.State)
    (input maximum destination : Nat) (x m : ℝ)
    (start : s.pc=0) (scratch : destination≠input)
    (inputValue : Ptx.Binary32.finiteReal (s.regs input)=some x)
    (maximumValue : Ptx.Binary32.finiteReal (s.regs maximum)=some m)
    (bounds : Ptx.Binary32.ShiftedExp.InputBounds x m)
    (run : Run target (program input maximum destination) s t) :
    ∃ u, Ptx.Binary32.finiteReal (t.regs destination)=some u ∧ |u|≤2 := by
  obtain ⟨⟨negative,shifted,product,r₀,r₁,r₂,r₃⟩,_⟩ := run_results target s t input maximum destination start scratch run
  exact Ptx.Binary32.ShiftedExp.output_range _ _ negative shifted product _ x m
    inputValue maximumValue bounds r₀ r₁ r₂ r₃
end Ptx.Scalar.ShiftedExp
