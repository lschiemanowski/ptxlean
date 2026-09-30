import PoissonPTX.CellTailStores
import PoissonPTX.CellTailResult

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
open CellMiddle Correspondence
variable {n : Nat}

/-- Launch-only integer bounds. They concern the low-word index and widened
byte-address calculation, not later event addresses or computed values.
The current interface conservatively requires these for padding lanes too;
it does not require their unused output words to be allocated. -/
def OutputBounds (width : Nat) (output : Word) (start : WithTail.State n) : Prop :=
  ∀ t, let s := start.core.lanes t
    (s.regs 15).toNat*(width*width)+(s.regs 14).toNat<2^32 ∧
    (s.regs 0).toNat+((s.regs 15).toNat*(width*width)+(s.regs 14).toNat)*8+output.toNat<2^64

instance : Decidable (OutputBounds width output start) := by
  unfold OutputBounds
  infer_instance

/-- Discharge the actual-store fence using only launch registers, nonwrapping
integer arithmetic and the chosen coefficient/output layout. -/
theorem store_bounds {w : Nat} {owner : Fin 32} {a : Access} (lo : 2≤width) (hi : width≤5)
    (launch : Numeric.Launch width bases start.core)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat)
    (observed : events[w]?=some (.data owner a)) (store : a.data.store=true) (global : a.space=.global) :
    (bases .global).toNat+Coefficients.extent width≤a.data.address := by
  rw [Address.store_address lo hi run launch.aligned launch.pcs (List.mem_of_getElem? observed) store global]
  have h := Output.after_coefficients (start.core.lanes owner) hi (bounds owner).1 (bounds owner).2 offset
  simpa [launch.global owner] using h

/-- The output-layout bounds also establish that the coefficient region does
not wrap. No separate bound on later read events is assumed. -/
theorem coefficient_nowrap (launch : Numeric.Launch width bases start.core)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat) :
    (bases .global).toNat+Coefficients.extent width≤2^64 := by
  have h := (bounds (0 : Fin 32)).2
  rw [launch.global] at h
  omega

/-- Correspondence from one combined execution and launch/layout conditions.
There is no premise asserting bounds for its actual global-store events. -/
theorem result_from_launch
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat)
    (compatible : Visibility.Compatible initial events original)
    (performed : Visibility.Performed events original)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (program width).length≤(final.core.lanes thread).pc) :
    decode ((final.core.lanes thread).regs 11)=Spec.get2 (localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0)) i j :=
  result_under_store_bounds launch lo hi run (coefficient_nowrap launch bounds offset)
    (fun _ _ _ observed store global => store_bounds lo hi launch run bounds offset observed store global)
    compatible performed thread i j lane finished

/-- The same execution's actual per-lane stored bytes have the TorchLean value.
This does not replace the separate publication of all writers into one global
byte memory or prove host-visible completion. -/
theorem stored_from_launch
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat)
    (compatible : Visibility.Compatible initial events original)
    (performed : Visibility.Performed events original)
    (thread : Fin 32) (i j : Fin width) (lane : thread.val=i.val*width+j.val)
    (finished : (front width).length+5≤(final.core.lanes thread).pc) :
    decode (read64 (final.core.lanes thread).global
      (CellFinal.location (start.core.lanes thread) width output).toNat)=Spec.get2 (localAction
        (Numeric.initialTensor width bases initial .global 0)
        (Numeric.initialTensor width bases initial .global (width*width*8+32))
        (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width bases initial .shared 0)) i j := by
  have active : thread.val<width*width := by
    have row := i.isLt; have col := j.isLt
    rw [lane]; nlinarith
  rw [Address.stored_word lo hi run launch.aligned launch.pcs thread active finished]
  exact result_from_launch launch lo hi run bounds offset compatible performed thread i j lane
    (by rw [front_length] at finished; omega)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput
