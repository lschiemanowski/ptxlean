import PoissonPTX.CellFamily
import PoissonPTX.AssemblyRowRepresentation

namespace PtxTorchLean.Poisson.PTX.CellWhole
variable {o : Operator} {values : Array Float}

/-- Immutable fields below the contiguous cell-output array are preserved by
publication of every actual cell history. This matches the host arena layout. -/
theorem Family.before (family : Family o values) (memory : Memory)
    (order : List (Fin o.mesh.cells.size)) (p : Nat)
    (before : p<family.base.toNat+family.output.toNat) : family.publish memory order p=memory p := by
  induction order with
  | nil => rfl
  | cons cell rest ih =>
    rw [Family.publish,(family.execution cell).outside,ih]
    left
    rw [family.sameBase,family.sameOutput]
    omega

theorem Family.input_word32 (family : Family o values) (memory : Memory)
    (order : List (Fin o.mesh.cells.size)) (address : Nat)
    (before : address+4≤family.base.toNat+family.output.toNat) :
    read32 (family.publish memory order) address=read32 memory address := by
  apply IndexSources.word_eq_of_bytes
  intro k
  simp only [IndexSources.byte_read32]
  apply family.before
  have := k.isLt
  omega

/-- Integer assembly metadata survives the preceding cell publication. Thus
checking the uploaded tables suffices; correct table bytes after computation
are a consequence of actual store ownership. -/
theorem Family.assembly_tables (family : Family o values) (memory : Memory)
    (order : List (Fin o.mesh.cells.size)) (a : Assembly.Arena n)
    (base : a.base=family.base)
    (offsetsBefore : a.offsets.toNat+(n+1)*4≤family.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤family.output.toNat)
    (encoded : a.RowsEncoded memory rows) : a.RowsEncoded (family.publish memory order) rows := by
  refine ⟨encoded.count,encoded.size,?_,?_,encoded.bounded⟩
  · intro i inside
    unfold Assembly.Arena.offset
    rw [family.input_word32]
    · exact encoded.offsets i inside
    · rw [base]; omega
  · intro k inside
    unfold Assembly.Arena.entryIndex
    rw [family.input_word32]
    · exact encoded.entries k inside
    · rw [base]; omega

end PtxTorchLean.Poisson.PTX.CellWhole
