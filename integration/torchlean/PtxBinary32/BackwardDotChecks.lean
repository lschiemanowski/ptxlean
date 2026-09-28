import PtxBinary32.BackwardDotFinite
import PtxBinary32.SoftmaxBackwardNumeric

/-! Bit-level regression examples for rounded backward arithmetic. These do not
replace the universal theorem and make no claim about physical GPU execution. -/
namespace Ptx.Binary32.BackwardDot.Checks

/-- Nontrivial saved weights, opposite incoming signs, and a balanced sum. -/
theorem cancellation : Reduction.Eval
    (.fork (.leaf (0x40000000,0x3f000000)) (.leaf (0xc0000000,0x3f000000))) 0 := by
  apply Reduction.Eval.fork (left:=0x3f800000) (right:=0xbf800000)
  · exact .leaf (by unfold Results; decide)
  · exact .leaf (by unfold Results; decide)
  · unfold Results; decide

/-- The saved weight one-half and incoming +2 give gradient +1 when the dot is zero. -/
theorem coordinate : SoftmaxBackwardNumeric.Result 0x3f000000 0x40000000 0 0x3f800000 := by
  refine ⟨0x80000000,0x40000000,?_,?_,?_⟩ <;> unfold Results <;> decide

/-- A negative-zero leaf and the dense +0 instruction need not retain its sign. -/
theorem signed_zero : Results .mul 0x80000000 0x3f000000 0x80000000 ∧
    Results .add 0x80000000 0 0 ∧ (0x80000000 : Word)≠0 := by
  unfold Results; decide

/-- The minimum subnormal is retained by a unit-weight leaf. -/
theorem subnormal : Reduction.Eval (.leaf (1,0x3f800000)) 1 :=
  .leaf (by unfold Results; decide)

end Ptx.Binary32.BackwardDot.Checks
