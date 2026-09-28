import PtxBinary32.PointwiseLaunch
import PtxBinary32.DenseChecks

/-! Interpreter regressions, not proofs by evaluation or hardware tests. The
stage-wise schedule interleaves every lane at every fetched instruction. -/
namespace Ptx.Scalar.Parallel.Pointwise.DifferenceChecks

private def layout : Layout 4 where
  prefixWords := 8
  left t := t.val
  right t := 4+t.val
  leftBound t := by have := t.isLt; omega
  rightBound t := by have := t.isLt; omega
  small := by decide

private def check (label : String) (schedule : List (Fin 4)) : IO Unit := do
  -- 3-1=2, -2-1=-3, 1-3=-2, 0-0=0.
  let before : List Word := [0x40400000,0xc0000000,0x3f800000,0,
    0x3f800000,0x3f800000,0x40400000,0, 0,0,0,0]
  let expected : List Word := [0x40000000,0xc0400000,0xc0000000,0]
  let cfg := config (by decide : 0<4)
  let result := Reference.run cfg (program .difference)
    (initial layout before [] Dense.Checks.seeds) schedule
  if !(List.finRange 4).all (fun t => (result.1.lanes t).halted) ||
      result.1.global.drop 8 != expected || result.1.global.take 8 != before.take 8 ||
      Replay.trace ⟨before,[]⟩ result.2.1 != some (Replay.arrays result.1) then
    throw (IO.userError s!"pointwise difference {label}: result or replay mismatch")
  IO.println s!"Pointwise difference interpreter check passed: {label}"

def run : IO Unit := do
  check "instruction-wise interleaving" ((List.replicate (program .difference).length (List.finRange 4)).flatten)
  check "reverse lane order" ((List.finRange 4).reverse.flatMap (List.replicate (program .difference).length))

#eval run
end Ptx.Scalar.Parallel.Pointwise.DifferenceChecks
