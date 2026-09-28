import PoissonResidualInput

/-! A kernel-checked instance for an actual saved GPU result. Words come from
hardware/receipts/poisson.tar.gz, case 01-n2-q1, not from a newly fabricated solution.
The complete 27-case suite additionally executes the proved checker natively. -/
namespace PtxTorchLean.Poisson.Certificate.Checks
open Lean Input

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def recordedGpuInput : Json := Lean.Json.mkObj [
  ("B", toJson (#[4605278973629831566,4596781800971278792,4596781800971278792,4605278973629831566] : Array Nat)),
  ("D", toJson (#[13830554455654793216,4607182418800017408,13830554455654793216,4607182418800017408] : Array Nat)),
  ("W", toJson (#[4598175219545276416,4598175219545276416,4598175219545276416,4598175219545276416] : Array Nat)),
  ("load", toJson (#[4598309225256033940,4606444097742567340,4598309225256033942,4606444097742567340,4614554148567478889,4606444097742567342,4598309225256033942,4606444097742567341,4598309225256033943] : Array Nat)),
  ("n", toJson (2 : Nat)),
  ("degree", toJson (1 : Nat)),
  ("cells", toJson (#[0,1,3,4,1,2,4,5,3,4,6,7,4,5,7,8] : Array Nat)),
  ("solution", toJson (#[0,0,0,0,4608207616498243022,0,0,0,0] : Array Nat)),
  ("rtol", toJson (4457293557087583675 : Nat)),
  ("atol", toJson (0 : Nat))
]

theorem recorded_gpu_accepted : acceptedRequest recordedGpuInput = true := by decide +kernel

def wrongInteriorInput : Json := Lean.Json.mkObj [
  ("B", toJson (#[4605278973629831566,4596781800971278792,4596781800971278792,4605278973629831566] : Array Nat)),
  ("D", toJson (#[13830554455654793216,4607182418800017408,13830554455654793216,4607182418800017408] : Array Nat)),
  ("W", toJson (#[4598175219545276416,4598175219545276416,4598175219545276416,4598175219545276416] : Array Nat)),
  ("load", toJson (#[4598309225256033940,4606444097742567340,4598309225256033942,4606444097742567340,4614554148567478889,4606444097742567342,4598309225256033942,4606444097742567341,4598309225256033943] : Array Nat)),
  ("n", toJson (2 : Nat)),
  ("degree", toJson (1 : Nat)),
  ("cells", toJson (#[0,1,3,4,1,2,4,5,3,4,6,7,4,5,7,8] : Array Nat)),
  ("solution", toJson (#[0,0,0,0,0,0,0,0,0] : Array Nat)),
  ("rtol", toJson (4457293557087583675 : Nat)),
  ("atol", toJson (0 : Nat))
]

theorem wrong_interior_rejected : acceptedRequest wrongInteriorInput = false := by decide +kernel

theorem finite_word_exact : decodeWord (BitVec.ofNat 64 0x3ff0000000000000) = some 1 := by decide +kernel
theorem infinity_rejected : decodeWord (BitVec.ofNat 64 0x7ff0000000000000) = none := by decide +kernel
theorem nan_rejected : decodeWord (BitVec.ofNat 64 0x7ff8000000000001) = none := by decide +kernel

end PtxTorchLean.Poisson.Certificate.Checks
