import PoissonPTX.ScalarExecution

namespace PtxTorchLean.Poisson.PTX.Scalar.Checks

/-- The pinned f64 abs rule retains a NaN's payload and sign. -/
theorem absolute_nan : absolute 0xfff8000000000042=0xfff8000000000042 := by decide +kernel

theorem absolute_subnormal : absolute 0x8000000000000001=1 := by decide +kernel

theorem absolute_negative_zero : absolute 0x8000000000000000=0 := by decide +kernel

theorem maximum_positive_zero_left : maximum 0 0x8000000000000000=decode 0 := by decide +kernel

theorem maximum_positive_zero_right : maximum 0x8000000000000000 0=decode 0 := by decide +kernel

theorem maximum_negative_zeros : maximum 0x8000000000000000 0x8000000000000000=decode 0x8000000000000000 := by decide +kernel

theorem maximum_one_nan : maximum 0xfff8000000000042 0x3ff0000000000000=decode 0x3ff0000000000000 := by decide +kernel

theorem comparison_nan_gt : Comparison.apply .gt 0xfff8000000000042 0=false := by decide +kernel

theorem comparison_nan_le : Comparison.apply .le 0 0xfff8000000000042=false := by decide +kernel

theorem sqrt_negative_zero : Float.sqrt (decode 0x8000000000000000)=decode 0x8000000000000000 := by decide +kernel

theorem sqrt_four : Float.sqrt (decode 0x4010000000000000)=decode 0x4000000000000000 := by decide +kernel

end PtxTorchLean.Poisson.PTX.Scalar.Checks
