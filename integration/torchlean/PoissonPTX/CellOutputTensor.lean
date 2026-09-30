import PoissonPTX.CellOutputPublication

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
open CellMiddle Correspondence
variable {cell output : Word} {width : Nat} {cfg : Config 32} {ctx : Fin 32 → Kernel.Context}
  {start final : WithTail.State 32} {events order : List (Event 32)}

/-- Read one cell's contiguous row-major binary64 output array. -/
def tensor (width : Nat) (base cell output : Word) (memory : Memory) : Mat Float width width :=
  matrix fun i j => decode (read64 memory
    (base.toNat+cell.toNat*(width*width)*8+output.toNat+(i.val*width+j.val)*8))

/-- The array offset agrees with the address calculated by the actual tail. -/
theorem location_entry (launch : Numeric.Launch width bases start.core) (hi : width≤5)
    (bounds : OutputBounds width output start) (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (owner : Fin 32) (i j : Fin width) (lane : owner.val=i.val*width+j.val) :
    (CellFinal.location (start.core.lanes owner) width output).toNat=
      (bases .global).toNat+cell.toNat*(width*width)*8+output.toNat+(i.val*width+j.val)*8 := by
  rw [CellFinal.location_exact _ hi (bounds owner).1 (bounds owner).2,
    launch.global,cells,launch.lane_nat,lane]
  omega

/-- The published global bytes contain the TorchLean value at every active
coordinate, independent of the order in which the actual records are merged. -/
theorem published_entry
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat)
    (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (compatible : Visibility.Compatible initial events original)
    (performed : Visibility.Performed events original) (permutation : order.Perm events)
    (owner : Fin 32) (i j : Fin width) (lane : owner.val=i.val*width+j.val)
    (finished : (front width).length+5≤(final.core.lanes owner).pc) :
    decode (read64 (GlobalPublication.publish memory order)
      ((bases .global).toNat+cell.toNat*(width*width)*8+output.toNat+(i.val*width+j.val)*8))=
      Spec.get2 (localAction
        (Numeric.initialTensor width bases initial .global 0)
        (Numeric.initialTensor width bases initial .global (width*width*8+32))
        (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
        (Numeric.initialTensor width bases initial .shared 0)) i j := by
  rw [←location_entry launch hi bounds cells owner i j lane,
    published_word launch lo hi run bounds cells permutation owner
      (by rw [lane]; exact row_major_bound i j) finished]
  exact result_from_launch launch lo hi run bounds offset compatible performed owner i j lane
    (by rw [front_length] at finished; omega)

/-- Whole-tensor correspondence for a completed cell. Completeness of its
store records is derived from the execution, not supplied by the caller.
This is not a proof of host visibility or of full PTX memory admission. -/
theorem published_tensor
    (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (offset : Coefficients.extent width≤output.toNat)
    (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (compatible : Visibility.Compatible initial events original)
    (performed : Visibility.Performed events original) (permutation : order.Perm events)
    (finished : ∀ t : Fin 32, t.val<width*width → (front width).length+5≤(final.core.lanes t).pc) :
    tensor width (bases .global) cell output (GlobalPublication.publish memory order)=localAction
      (Numeric.initialTensor width bases initial .global 0)
      (Numeric.initialTensor width bases initial .global (width*width*8+32))
      (Numeric.initialTensor width bases initial .global (2*(width*width*8+32)))
      (Numeric.initialTensor width bases initial .shared 0) := by
  apply TorchLean.Tensor.Internal.Rep.ext
  intro coordinate
  rcases coordinate with ⟨i,j,remaining⟩
  cases remaining
  have active := row_major_bound i j
  have fits : i.val*width+j.val<32 := by nlinarith
  have entry := published_entry launch lo hi run bounds offset cells compatible performed permutation
    ⟨i.val*width+j.val,fits⟩ i j rfl (finished _ active) (memory:=memory)
  simpa [tensor,matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,
    TorchLean.Tensor.unstack,TorchLean.Tensor.item] using entry

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
