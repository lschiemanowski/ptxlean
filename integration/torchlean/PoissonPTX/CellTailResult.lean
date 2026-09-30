import PoissonPTX.CellTailProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
open CellMiddle Correspondence

/-- The arithmetic run, retained occurrences and register relation are derived
from one interleaved execution. The remaining output-address obligation is
explicit: every actual global store is beyond the coefficient region. -/
theorem result_under_store_bounds
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (nowrap : (bases .global).toNat+Coefficients.extent width≤2^64)
    (writes : ∀ (w : Nat) (writer : Fin 32) (wa : Access), events[w]?=some (.data writer wa) →
      wa.data.store=true → wa.space=.global →
      (bases .global).toNat+Coefficients.extent width≤wa.data.address)
    (compatible : Visibility.Compatible initial events original)
    (performed : Visibility.Performed events original)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (program width).length≤(final.core.lanes thread).pc) :
    decode ((final.core.lanes thread).regs 11)=Spec.get2 (localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0)) i j := by
  obtain ⟨small,shadow,run',embedding,omitted,related⟩ :=
    arithmetic_filtered lo hi run launch.aligned launch.pcs
  have last := related.2.2 thread
  simp only [show ¬(final.core.lanes thread).pc<(program width).length by omega,ite_false] at last
  rw [last.2]
  apply Output.projected_arithmetic launch lo hi run' embedding nowrap
  · intro w writer wa observed store missing
    have kind := omitted w (.data writer wa) observed missing
    exact ⟨kind.1,writes w writer wa observed store kind.1⟩
  · exact compatible
  · exact performed
  · exact lane
  · exact last.1

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
