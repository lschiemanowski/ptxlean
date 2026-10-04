import PoissonPTX.CellCoefficientProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle Symbolic

def extent (width : Nat) : Space → Nat
  | .global => Coefficients.extent width
  | .shared => 7*width*width*8

/-- A finite address-only certificate: each actual arithmetic load/store names
an aligned offset inside the allocated coefficient or shared-plane region. -/
def accessCheck (width lane pc : Nat) : Prop :=
  match (program width)[pc]? with
  | some (.data (.load64 space _ address)) | some (.data (.store64 space address _)) =>
    match Numeric.extract (operand (atPC .addresses (program width) (Numeric.seed width lane) pc) address) with
    | some (sp,off) => sp=space ∧ off.toNat%8=0 ∧ off.toNat+8≤extent width space
    | none => False
  | _ => True

instance : Decidable (accessCheck width lane pc) := by
  unfold accessCheck
  split
  · split <;> infer_instance
  · split <;> infer_instance
  · infer_instance

def AccessBounds (width : Nat) : Prop :=
  ∀ lane : Fin (width*width), ∀ pc : Fin (program width).length, accessCheck width lane.val pc.val

instance : Decidable (AccessBounds width) := by unfold AccessBounds; infer_instance

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
