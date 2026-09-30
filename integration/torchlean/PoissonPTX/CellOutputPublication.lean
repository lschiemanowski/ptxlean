import PoissonPTX.CellOutputOccurrence
import PoissonPTX.GlobalPublication

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
open CellMiddle Correspondence
variable {cell : Word} {cfg : Config 32} {ctx : Fin 32 → Kernel.Context}
  {start final : WithTail.State 32} {events order : List (Event 32)}

/-- Every global record either writes this owner's exact final word or is
disjoint from it. Both alternatives follow from the actual execution. -/
theorem safe_records (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (owner : Fin 32) :
    GlobalPublication.Safe events (CellFinal.location (start.core.lanes owner) width output).toNat
      ((final.core.lanes owner).regs 11) := by
  intro writer a member global store
  have address := Address.store_address lo hi run launch.aligned launch.pcs member store global
  by_cases same : writer=owner
  · subst writer
    exact Or.inl ⟨address,store_value lo hi run launch.aligned launch.pcs member store global⟩
  · apply Or.inr
    rw [address]
    exact output_disjoint launch hi bounds cells writer owner same

/-- A completed active lane contributes a real store record with the required
address and value. Publication completeness is proved, not assumed. -/
theorem present_record (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (owner : Fin 32) (active : owner.val<width*width)
    (finished : (front width).length+5≤(final.core.lanes owner).pc) :
    GlobalPublication.Present events (CellFinal.location (start.core.lanes owner) width output).toNat
      ((final.core.lanes owner).regs 11) := by
  obtain ⟨a,member,store,global⟩ := completed_wrote lo hi run launch.aligned launch.pcs active finished
  exact ⟨owner,a,member,global,store,
    Address.store_address lo hi run launch.aligned launch.pcs member store global,
    store_value lo hi run launch.aligned launch.pcs member store global⟩

/-- Any permutation of the actual history publishes the same completed output
word. Memory-source constraints still refer to the original execution order. -/
theorem published_word (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (bounds : OutputBounds width output start) (cells : ∀ t, (start.core.lanes t).regs 15=cell)
    (permutation : order.Perm events) (owner : Fin 32) (active : owner.val<width*width)
    (finished : (front width).length+5≤(final.core.lanes owner).pc) :
    read64 (GlobalPublication.publish memory order)
      (CellFinal.location (start.core.lanes owner) width output).toNat=(final.core.lanes owner).regs 11 :=
  GlobalPublication.permuted_word permutation (safe_records launch lo hi run bounds cells owner)
    (present_record launch lo hi run owner active finished)

/-- Bytes outside all possible output words are unchanged by publication.
The condition concerns launch geometry, not a supplied store trace. -/
theorem published_outside (launch : Numeric.Launch width bases start.core) (lo : 2≤width) (hi : width≤5)
    (run : WithTail.Runs cfg ctx (front width) (CellFinal.tail width output) start events final)
    (permutation : order.Perm events)
    (outside : ∀ t, p<(CellFinal.location (start.core.lanes t) width output).toNat ∨
      (CellFinal.location (start.core.lanes t) width output).toNat+8≤p) :
    GlobalPublication.publish memory order p=memory p := by
  apply GlobalPublication.outside
  intro owner a member global store
  rw [Address.store_address lo hi run launch.aligned launch.pcs (permutation.mem_iff.mp member) store global]
  exact outside owner

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication
