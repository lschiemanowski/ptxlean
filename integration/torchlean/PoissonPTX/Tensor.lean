import PoissonPTX.ResidualKernel
import NN.Spec.Core.Tensor.Constructors
import NN.Spec.Core.TensorOps

namespace PtxTorchLean.Poisson.PTX.Kernel.Residual
open TorchLean

/-- Tensor view of the exact byte addresses selected by a launched thread. The
entry theorem supplies the allocation/alignment conditions for its selected cell. -/
def view (memory : Memory) (layout : Fin n → Nat) : Tensor Float [n] :=
  Tensor.ofFn fun i => decode (read64 memory (layout i))

/-- The result is a coordinate of the actual TorchLean binary64 subtraction
specification. The two address equalities concern the input layout, not outputs. -/
theorem torchlean_coordinate (ctx : Context) (s final : State)
    (count : BitVec 32) (rhs ap output : Word) (i : Fin n)
    (leftLayout rightLayout : Fin n → Nat)
    (leftAddress : leftLayout i = (address (setup ctx s count).core 12 rhs).toNat)
    (rightAddress : rightLayout i = (address (setup ctx s count).core 12 ap).toNat)
    (pc : s.core.pc = 0) (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat)
    (execution : Run ctx (program count rhs ap output) s final) :
    decode (read64 final.core.global (address (setup ctx s count).core 12 output).toNat) =
      (Tensor.subSpec (view s.core.global leftLayout) (view s.core.global rightLayout)) (i,PUnit.unit) := by
  have h := (fetched_correct ctx s final count rhs ap output pc running hl hr ha ho execution).1
  simpa [Tensor.subSpec,Tensor.map2Spec,Tensor.Internal.Rep.zipWith_apply,view,leftAddress,rightAddress] using h

end PtxTorchLean.Poisson.PTX.Kernel.Residual
