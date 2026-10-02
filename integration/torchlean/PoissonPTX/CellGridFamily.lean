import PoissonPTX.CellGridPublication
import PoissonPTX.CellFamily

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Membership refers to the actual tagged occurrence in the joint history. -/
theorem mem_forBlock (block : Fin count) (events : List (Fin count × α)) (a : α) :
    a∈forBlock block events ↔ (block,a)∈events := by
  induction events with
  | nil => simp [forBlock]
  | cons head rest ih =>
    obtain ⟨owner,value⟩ := head
    by_cases own : owner=block
    · subst owner; simp [forBlock,ih]
    · simp [forBlock,own,Ne.symm own,ih]

/-- Different cells' active coordinates occupy disjoint eight-byte slots. -/
theorem cell_words_disjoint {cell other coordinate index area : Nat}
    (different : cell≠other) (inside : coordinate<area) (active : index<area) :
    (other*area+index)*8+8≤(cell*area+coordinate)*8 ∨
      (cell*area+coordinate)*8+8≤(other*area+index)*8 := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · right
    have bound := Nat.mul_le_mul_right area (Nat.succ_le_of_lt before)
    nlinarith
  · left
    have bound := Nat.mul_le_mul_right area (Nat.succ_le_of_lt after)
    nlinarith

/-- This theorem permits arbitrary chronological interleaving of complete cell
histories. It does not replace the separate requirement that these histories
come from an actual grid run with admitted read sources. -/
theorem family_entry (family : CellWhole.Family o values)
    (events : List (Event o.mesh.cells.size))
    (projected : ∀ cell, forBlock cell events=(family.execution cell).events)
    (cell : Fin o.mesh.cells.size) (i j : Fin o.nodes.size) :
    decode (read64 (publish family.memory events) (family.address cell i j))=
      Correspondence.entries (localAction o.b o.d o.w (gather o values cell.val)) i j := by
  rw [publication_word events cell family.memory (family.address cell i j) ?_,projected]
  exact family.entry family.memory cell i j
  intro other owner access member different global store
  have localMember : Concurrent.Event.data owner access∈(family.execution other).events := by
    rw [← projected]
    exact (mem_forBlock other events _).mpr member
  obtain ⟨active,address⟩ := (family.execution other).global_store localMember store global
  rw [family.sameBase,family.sameOutput,family.cell_nat] at address
  rw [address]
  have apart := cell_words_disjoint (fun eq => different (Fin.ext eq.symm))
    (Correspondence.row_major_bound i j) active
  unfold CellWhole.Family.address
  rcases apart with before | after
  · left; omega
  · right; omega

/-- Every actual global store in a family-backed grid history lies in the cell
output array. In particular, publishing interleaved stores preserves all bytes
below that array, including uploaded assembly metadata. -/
theorem family_before (family : CellWhole.Family o values)
    (events : List (Event o.mesh.cells.size))
    (projected : ∀ cell, forBlock cell events=(family.execution cell).events)
    (memory : Memory) (p : Nat) (before : p<family.base.toNat+family.output.toNat) :
    publish memory events p=memory p := by
  apply Concurrent.GlobalPublication.outside
  intro owner access member global store
  obtain ⟨tagged,member,same⟩ := List.mem_map.mp member
  obtain ⟨cell,event⟩ := tagged
  cases same
  have localMember : Concurrent.Event.data owner access∈(family.execution cell).events := by
    rw [← projected]
    exact (mem_forBlock cell events _).mpr member
  have address := ((family.execution cell).global_store localMember store global).2
  rw [family.sameBase,family.sameOutput] at address
  left
  omega

end PtxTorchLean.Poisson.PTX.CellGrid
