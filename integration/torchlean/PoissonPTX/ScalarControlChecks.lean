import PoissonPTX.ScalarBetaGuards

namespace PtxTorchLean.Poisson.PTX.Scalar.Checks

/-- Register examples exercise guard policy, not a memory-source assumption. -/
def coefficientState (a b : Word) (active broken : BitVec 32) : Flow.State :=
  ⟨{pc:=0,regs:=fun r => if r=4 then a else if r=5 then b else if r=21 then active.setWidth 64
      else if r=22 then broken.setWidth 64 else 0,
    global:=fun _ => 0,shared:=fun _ => 0,globalStart:=0,globalBytes:=0,sharedStart:=0,sharedBytes:=0},
    fun _ => false,false⟩

theorem alpha_old_broken_does_not_disable :
    Coefficient.alphaUse (coefficientState 0x3ff0000000000000 0x3ff0000000000000 1 1)=true := by decide +kernel

theorem alpha_inactive_nonfinite_is_disabled :
    Coefficient.alphaUse (coefficientState 0x7ff0000000000000 0x3ff0000000000000 0 0)=false := by decide +kernel

theorem alpha_inactive_nonfinite_does_not_mark_broken :
    Coefficient.alphaBroken (coefficientState 0x7ff0000000000000 0x3ff0000000000000 0 0)=0 := by decide +kernel

theorem alpha_active_nan_marks_broken :
    Coefficient.alphaBroken (coefficientState 0xfff8000000000042 0x3ff0000000000000 1 0)=1 := by decide +kernel

theorem alpha_zero_denominator_marks_broken :
    Coefficient.alphaBroken (coefficientState 0x8000000000000000 0x3ff0000000000000 1 0)=1 := by decide +kernel

theorem beta_negative_finite_does_not_mark_broken :
    Coefficient.betaBroken (coefficientState 0xbff0000000000000 0x3ff0000000000000 1 0)=0 := by decide +kernel

theorem beta_active_infinity_marks_broken :
    Coefficient.betaBroken (coefficientState 0x7ff0000000000000 0x3ff0000000000000 1 0)=1 := by decide +kernel

end PtxTorchLean.Poisson.PTX.Scalar.Checks
