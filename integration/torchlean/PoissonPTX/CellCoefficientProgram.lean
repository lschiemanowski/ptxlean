import PoissonPTX.CellConsumerRun

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients
open CellMiddle Symbolic
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

/-- Exclusive end of B, D and W, including the gaps between these tables. -/
def extent (width : Nat) : Nat := 2*(width*width*8+32)+width*width*8

def checkAt (width lane pc : Nat) : Prop :=
  match (program width)[pc]? with
  | some (.data (.load64 .global _ addr)) =>
    match Numeric.extract (operand (atPC .addresses (program width) (Numeric.seed width lane) pc) addr) with
    | some (.global,off) => off.toNat+8≤extent width
    | _ => False
  | _ => True
instance : Decidable (checkAt width lane pc) := by
  unfold checkAt; split
  · split <;> infer_instance
  · infer_instance

def Checked (width : Nat) : Prop := ∀ lane : Fin (width*width), ∀ pc : Fin (program width).length,
  checkAt width lane.val pc.val
instance : Decidable (Checked width) := by unfold Checked; infer_instance

theorem checked (width : Nat) (lo : 2≤width) (hi : width≤5) : Checked width := by
  interval_cases width <;> decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients
