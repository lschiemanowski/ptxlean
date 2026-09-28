import PtxBinary32.SoftmaxBackwardDot
import PtxBinary32.DenseChecks

/-! Small executable regressions of the backward dot's fetched program. These
check the software interpreter and trace replay, not GPU execution or admission
by testing. General launch correctness and admission existence are separate
proofs in SoftmaxBackwardDot. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackwardDot.Checks

private def check (label : String) (d : Nat) (bound : Sum.Bounds d)
    (p g : Fin (Sum.width d) → Word) (expected : Word) : IO Unit := do
  let before := global d p g
  let shared := List.replicate (Sum.sharedWords d) (0xdeadbeef : Word)
  let result := Reference.run (Dense.config (Sum.shape d) (Sum.denseBounds d bound)) (Sum.program d)
    (Dense.initial (Sum.shape d) before shared Dense.Checks.seeds) (Dense.Checks.schedule (Sum.shape d))
  let statuses := result.2.2.all fun status => match status with
    | .advanced | .waiting | .released | .halted => true
    | _ => false
  let done := (List.finRange (Sum.shape d).threads).all fun t =>
    (result.1.lanes t).halted && (result.1.lanes t).scalar.pc == (Sum.program d).length-1
  if !statuses || !done || result.1.global[outputIndex d]? != some expected ||
      result.1.global.take (outputIndex d) != before.take (outputIndex d) ||
      result.1.global.length != before.length || result.1.shared.length != shared.length ||
      result.1.barrier.generation != d+1 ||
      Replay.trace ⟨before,shared⟩ result.2.1 != some (Replay.arrays result.1) then
    throw (IO.userError s!"{label}: softmax backward dot interpreter regression")
  IO.println s!"Softmax backward dot interpreter check passed: {label}"

def run : IO Unit := do
  check "singleton sensitivity" 0 (by unfold Sum.Bounds; decide)
    (fun _ => 0x3f800000) (fun _ => 0xc0400000) 0xc0400000
  -- p=(1/4,1/4,1/4,1/4), g=(1,-2,3,-4), q=-1/2.
  check "signed weighted sum" 2 (by unfold Sum.Bounds; decide)
    (fun _ => 0x3e800000)
    (fun i => if i.val=0 then 0x3f800000 else if i.val=1 then 0xc0000000
      else if i.val=2 then 0x40400000 else 0xc0800000) 0xbf000000
  check "negative zero canonicalized by positive-zero bias" 0 (by unfold Sum.Bounds; decide)
    (fun _ => 0x3f800000) (fun _ => 0x80000000) 0

#eval run
end Ptx.Scalar.Parallel.SoftmaxBackwardDot.Checks
