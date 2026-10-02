import PoissonPTX.CellExecutionStores

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Cell execution evidence with a common contiguous output array. This is a
family of actual CTA executions, not yet a model of arbitrary grid scheduling
or cross-launch visibility. Each member's tensor is derived from its run. -/
structure Family (o : Operator) (values : Array Float) where
  (base output : Word)
  memory : Memory
  small : o.mesh.cells.size≤2^32
  execution : ∀ i : Fin o.mesh.cells.size, Execution o values (BitVec.ofNat 32 i.val)
  sameInitial : ∀ i, (execution i).memory .global=memory
  sameCTA : ∀ i, (execution i).cfg.cta=i.val
  sameBase : ∀ i, (execution i).bases .global=base
  sameOutput : ∀ i, (execution i).output=output

variable {o : Operator} {values : Array Float}

def Family.address (family : Family o values) (cell : Fin o.mesh.cells.size) (i j : Fin o.nodes.size) : Nat :=
  family.base.toNat+family.output.toNat+(cell.val*(o.nodes.size*o.nodes.size)+i.val*o.nodes.size+j.val)*8

theorem Family.cell_nat (family : Family o values) (i : Fin o.mesh.cells.size) :
    (BitVec.ofNat 32 i.val).toNat=i.val := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt family.small)]

/-- Numerical output of an executed cell at its actual contiguous array slot. -/
theorem Family.entry (family : Family o values) (memory : Memory)
    (cell : Fin o.mesh.cells.size) (i j : Fin o.nodes.size) :
    decode (read64 (Concurrent.GlobalPublication.publish memory (family.execution cell).events) (family.address cell i j))=
      Correspondence.entries (localAction o.b o.d o.w (Poisson.gather o values cell.val)) i j := by
  have tensor := (family.execution cell).tensor memory
  have atEntry := congrArg (fun a => Spec.get2 a i j) tensor
  rw [family.cell_nat] at atEntry
  have wide : ((BitVec.ofNat 32 cell.val).setWidth 64).toNat=cell.val := by
    rw [BitVec.toNat_setWidth,family.cell_nat,Nat.mod_eq_of_lt]
    have := cell.isLt; have := family.small; omega
  simpa [Concurrent.CellConsumer.WithOutput.Publication.tensor,Correspondence.entries,
    matrix,Spec.get2,Spec.get,TorchLean.Tensor.getScalar,
    TorchLean.Tensor.unstack,TorchLean.Tensor.item,family.sameBase,family.sameOutput,wide,
    Family.address,Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using atEntry

/-- Byte separation of distinct cell planes, including the final byte of a
coordinate. This uses active coordinates, not all 32 possible lane addresses. -/
theorem different_plane {cell other coordinate area k : Nat} (different : cell≠other) (inside : coordinate<area) (byte : k<8) :
    (cell*area+coordinate)*8+k<other*area*8 ∨
      (other+1)*area*8≤(cell*area+coordinate)*8+k := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · left
    have bound := Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right area (Nat.succ_le_of_lt before))
    nlinarith
  · right
    have bound := Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right area (Nat.succ_le_of_lt after))
    nlinarith

/-- Publishing another cell's actual writes preserves this cell's output word. -/
theorem Family.other_preserves (family : Family o values) (memory : Memory)
    (cell other : Fin o.mesh.cells.size) (different : cell≠other) (i j : Fin o.nodes.size) :
    read64 (Concurrent.GlobalPublication.publish memory (family.execution other).events) (family.address cell i j)=
      read64 memory (family.address cell i j) := by
  apply Sources.word_eq_of_bytes
  intro k
  simp only [Sources.byte_read64]
  apply (family.execution other).outside
  rw [family.sameBase,family.sameOutput,family.cell_nat]
  have apart := different_plane (cell:=cell.val) (other:=other.val)
    (fun eq => different (Fin.ext eq)) (Correspondence.row_major_bound i j) k.isLt
  unfold Family.address
  rcases apart with left | right
  · left; omega
  · right; omega

/-- Merge complete cell histories in a chosen cell order. The family retains
each actual history; this operation only defines mathematical publication. -/
def Family.publish (family : Family o values) (memory : Memory) : List (Fin o.mesh.cells.size) → Memory
  | [] => memory
  | cell::rest => Concurrent.GlobalPublication.publish (family.publish memory rest) (family.execution cell).events

/-- Any order containing a cell publishes its TorchLean tensor, since every
other cell's actual writes are disjoint. Repetition is harmless as well. -/
theorem Family.published_entry (family : Family o values) (memory : Memory)
    (order : List (Fin o.mesh.cells.size)) (cell : Fin o.mesh.cells.size) (included : cell∈order)
    (i j : Fin o.nodes.size) :
    decode (read64 (family.publish memory order) (family.address cell i j))=
      Correspondence.entries (localAction o.b o.d o.w (Poisson.gather o values cell.val)) i j := by
  induction order with
  | nil => simp at included
  | cons other rest ih =>
    by_cases same : other=cell
    · subst other; exact family.entry _ cell i j
    · rw [Family.publish,family.other_preserves _ cell other (Ne.symm same) i j]
      exact ih ((List.mem_cons.mp included).resolve_left (Ne.symm same))

end PtxTorchLean.Poisson.PTX.CellWhole
