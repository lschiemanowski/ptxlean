import PtxHardwareDense

namespace Ptx.Hardware.Dense.Checks
open Lean Ptx.Scalar Ptx.Scalar.Parallel

theorem reject_unsupported_local : instruction (.localStep (.plain (.unsupported "new-op"))) =
    .error "unsupported local instruction" := by decide

theorem reject_memory_as_local : instruction (.localStep (.plain (.load 0 (.reg 0)))) =
    .error "unsupported local instruction" := by decide

theorem reject_arithmetic_as_memory : instruction (.memory .global (.plain (.mov32 0 (.reg 0)))) =
    .error "unsupported memory instruction" := by decide

theorem reject_other_barrier : instruction (.sync 1) = .error "unsupported barrier" := by decide

/-- Malformed shapes and words cannot reach the emitted program or reference. -/
def run : IO Unit := do
  let requests := [
    "{\"rows\":1,\"columns\":3,\"depth\":1,\"words\":[]}",
    "{\"rows\":1,\"columns\":0,\"depth\":11,\"words\":[0]}",
    "{\"rows\":1,\"columns\":0,\"depth\":0,\"words\":[]}",
    "{\"rows\":1,\"columns\":0,\"depth\":0,\"words\":[4294967296]}"]
  for text in requests do
    match Json.parse text >>= exportCase with
    | .ok _ => throw (IO.userError "invalid export request accepted")
    | .error _ => pure ()
  IO.println "Dense hardware export rejection checks passed"

#eval run
end Ptx.Hardware.Dense.Checks
