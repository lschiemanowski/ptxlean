import PtxBinary32.SumExecution
import PtxBinary32.DenseChecks

/-! Small full-program software-interpreter regressions. These supplement the
general execution proofs; they do not run PTX on a GPU. -/
namespace Ptx.Scalar.Parallel.Sum.Checks

/-- Validate instruction outcomes, completion, exact output, input and constant
preservation, memory extents and replay of the actual generated event trace. -/
def check (label : String) (d : Nat) (bound : Bounds d)
    (input : Fin (width d) → Word) (expected : Word) : IO Unit := do
  let before := global d input
  let shared := List.replicate (sharedWords d) (0xdeadbeef : Word)
  let result := Reference.run (config d bound) (program d)
    (initial d input shared Dense.Checks.seeds) (Dense.Checks.schedule (shape d))
  let statuses := result.2.2.all fun status => match status with
    | .advanced | .waiting | .released | .halted => true
    | _ => false
  let done := (List.finRange (shape d).threads).all fun t =>
    (result.1.lanes t).halted && (result.1.lanes t).scalar.pc == (program d).length-1
  if !statuses || !done || result.1.global[outputIndex d]? != some expected ||
      result.1.global.take (outputIndex d) != before.take (outputIndex d) ||
      result.1.global.length != before.length || result.1.shared.length != shared.length ||
      result.1.barrier.generation != d+1 ||
      Replay.trace ⟨before,shared⟩ result.2.1 != some (Replay.arrays result.1) then
    throw (IO.userError s!"{label}: sum interpreter regression")
  IO.println s!"Sum interpreter check passed: {label}"

def run : IO Unit := do
  check "singleton retains one" 0 (by unfold Bounds; decide) (fun _ => 0x3f800000) 0x3f800000
  check "four positive entries" 2 (by unfold Bounds; decide) (fun i =>
    if i.val=0 then 0x3f800000 else if i.val=1 then 0x3f000000
    else if i.val=2 then 0x3e800000 else 0x3e000000) 0x3ff00000
  check "signed cancellation" 2 (by unfold Bounds; decide) (fun i =>
    if i.val=0 then 0x3f800000 else if i.val=1 then 0xbf800000
    else if i.val=2 then 0x3f000000 else 0xbf000000) 0
  check "negative singleton" 0 (by unfold Bounds; decide) (fun _ => 0xbf800000) 0xbf800000
  check "negative zero canonicalized by positive-zero bias" 0 (by unfold Bounds; decide)
    (fun _ => 0x80000000) 0

#eval run

end Ptx.Scalar.Parallel.Sum.Checks
