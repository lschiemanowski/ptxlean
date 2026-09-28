import PtxBinary32.SoftmaxBackward
import PtxBinary32.DenseChecks

/-! Software regressions of all three backward instruction programs. Inputs
here are stored forward words; these checks do not assert GPU conformance. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackward.ExecutionChecks

private def pointwise (op : Pointwise.Op) (l : Pointwise.Layout n) (positive : 0<n)
    (before : List Word) : IO (List Word) := do
  let schedule := (List.replicate (Pointwise.program op).length (List.finRange n)).flatten
  let result := Reference.run (Pointwise.config positive) (Pointwise.program op)
    (Pointwise.initial l before [] Dense.Checks.seeds) schedule
  if !(List.finRange n).all (fun t => (result.1.lanes t).halted) ||
      Replay.trace ⟨before,[]⟩ result.2.1 != some (Replay.arrays result.1) then
    throw (IO.userError "backward pointwise completion or replay failed")
  return result.1.global

private def check (label : String) (d : Nat) (bound : Sum.Bounds d)
    (p g : Fin (Sum.width d) → Word) (q : Word) (expected : List Word) : IO Unit := do
  let before := SoftmaxBackwardDot.global d p g
  let shared := List.replicate (Sum.sharedWords d) 0
  let dot := Reference.run (Dense.config (Sum.shape d) (Sum.denseBounds d bound)) (Sum.program d)
    (Dense.initial (Sum.shape d) before shared Dense.Checks.seeds) (Dense.Checks.schedule (Sum.shape d))
  if !(List.finRange (Sum.shape d).threads).all (fun t => (dot.1.lanes t).halted) ||
      dot.1.global[Sum.outputIndex d]! != q ||
      Replay.trace ⟨before,shared⟩ dot.2.1 != some (Replay.arrays dot.1) then
    throw (IO.userError s!"{label}: backward dot completion, result or replay failed")
  have positive : 0<Sum.width d := by unfold Sum.width; positivity
  let differences ← pointwise .difference (differenceLayout d bound) positive (extend d dot.1.global)
  let final ← pointwise .mul (gradientLayout d bound) positive (extend d differences)
  if final.length != 4*Sum.width d+2 || final.drop (gradientBase d) != expected ||
      final.take (2*Sum.width d) != before.take (2*Sum.width d) then
    throw (IO.userError s!"{label}: backward gradient or preserved operands mismatch")
  IO.println s!"Softmax backward interpreter check passed: {label}"

def run : IO Unit := do
  check "two outputs and a negative gradient" 1 (by norm_num [Sum.Bounds])
    (fun i => if i.val=0 then 0x3e800000 else 0x3f400000)
    (fun i => if i.val=0 then 0x40000000 else 0xc0000000)
    0xbf800000 [0x3f400000,0xbf400000]
  check "constant incoming sensitivity gives zero" 1 (by norm_num [Sum.Bounds])
    (fun i => if i.val=0 then 0x3e800000 else 0x3f400000)
    (fun _ => 0x40000000) 0x40000000 [0,0]
  check "singleton backward is zero" 0 (by norm_num [Sum.Bounds])
    (fun _ => 0x3f800000) (fun _ => 0x40400000) 0x40400000 [0]

#eval run
end Ptx.Scalar.Parallel.SoftmaxBackward.ExecutionChecks
