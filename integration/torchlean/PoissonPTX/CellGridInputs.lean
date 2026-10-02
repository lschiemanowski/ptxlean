import PoissonPTX.CellGridExecution
import PoissonPTX.AssemblyRowRepresentation

namespace PtxTorchLean.Poisson.PTX.CellGrid
variable {o : Operator} {values : Array Float}

theorem Admitted.input_word32 (grid : Admitted o values) (address : Nat)
    (before : address+4≤grid.candidates.base.toNat+grid.candidates.output.toNat) :
    read32 (publish grid.candidates.memory grid.events) address=read32 grid.candidates.memory address := by
  apply IndexSources.word_eq_of_bytes
  intro k
  simp only [IndexSources.byte_read32]
  apply grid.before
  have := k.isLt
  omega

/-- Checking the uploaded assembly tables is sufficient: actual interleaved
cell stores preserve their bytes. -/
theorem Admitted.assembly_tables (grid : Admitted o values) (a : Assembly.Arena n)
    (base : a.base=grid.candidates.base)
    (offsetsBefore : a.offsets.toNat+(n+1)*4≤grid.candidates.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤grid.candidates.output.toNat)
    (encoded : a.RowsEncoded grid.candidates.memory rows) :
    a.RowsEncoded (publish grid.candidates.memory grid.events) rows := by
  refine ⟨encoded.count,encoded.size,?_,?_,encoded.bounded⟩
  · intro i inside
    unfold Assembly.Arena.offset
    rw [grid.input_word32]
    · exact encoded.offsets i inside
    · rw [base]; omega
  · intro k inside
    unfold Assembly.Arena.entryIndex
    rw [grid.input_word32]
    · exact encoded.entries k inside
    · rw [base]; omega

end PtxTorchLean.Poisson.PTX.CellGrid
