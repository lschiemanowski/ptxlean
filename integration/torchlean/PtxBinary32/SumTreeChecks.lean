import PtxBinary32.SumTree

/-! Kernel-checked arithmetic boundaries for the sum component. These cases do
not replace the quantified proof and do not claim execution on a GPU. -/
namespace Ptx.Binary32.SumTree.Checks

/-- Negative values are allowed by the arithmetic relation. -/
theorem signed_cancellation :
    Reduction.Eval
      (.fork (.leaf (0x3f800000,0x3f800000)) (.leaf (0x3f800000,0xbf800000))) 0 := by
  apply Reduction.Eval.fork (left:=0x3f800000) (right:=0xbf800000)
  · exact .leaf (by unfold Results; decide)
  · exact .leaf (by unfold Results; decide)
  · unfold Results; decide

/-- Exact finite real preservation does not imply preservation of the zero sign. -/
theorem zero_sign_changes : Results .add 0x80000000 0 0 ∧ (0x80000000 : Word) ≠ 0 := by
  unfold Results; decide

/-- Gradual-underflow values remain allowed at the unit-multiplication leaves. -/
theorem subnormal_leaf : Reduction.Eval (.leaf (0x3f800000,1)) 1 := .leaf (by unfold Results; decide)

theorem singleton_budget : budget 0=0 := by norm_num [budget]

theorem largest_budget : budget 10=1023/8192 ∧ budget 10<1/8 := by
  norm_num [budget]

end Ptx.Binary32.SumTree.Checks
