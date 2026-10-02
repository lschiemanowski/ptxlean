import PoissonPTX.AssemblyRowRepresentation

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Finite validation of the actual input-table bytes against ordered rows.
The check inspects integer metadata only; it cannot certify an output sum. -/
def Arena.checkRows (a : Arena n) (memory : Memory) (rows : List (List Nat)) : Bool :=
  decide (rows.length=n) && decide (rows.flatten.length=a.entryCount) &&
    (List.range (n+1)).all (fun i => decide (a.offset memory i=CompressedRows.offset rows i)) &&
    (List.range a.entryCount).all (fun k => decide (a.entryIndex memory k=rows.flatten[k]?.getD 0)) &&
    rows.all (fun row => row.all (fun index => decide (index<a.elementCount)))

variable {n : Nat} {a : Arena n} {memory : Memory} {rows : List (List Nat)}

/-- A successful finite check provides the input contract needed by the
universal PTX assembly theorem. -/
theorem Arena.checkRows_sound (checked : a.checkRows memory rows=true) : a.RowsEncoded memory rows := by
  simp only [Arena.checkRows,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  rcases checked with ⟨⟨⟨⟨count,size⟩,offsets⟩,entries⟩,bounded⟩
  refine ⟨count,size,?_,?_,bounded⟩
  · intro i inside; exact offsets i (List.mem_range.mpr (by omega))
  · intro k inside; exact entries k (List.mem_range.mpr inside)

theorem Arena.checkRows_complete (represented : a.RowsEncoded memory rows) : a.checkRows memory rows=true := by
  simp only [Arena.checkRows,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨⟨⟨⟨represented.count,represented.size⟩,?_⟩,?_⟩,represented.bounded⟩
  · intro i inside; exact represented.offsets i (by have := List.mem_range.mp inside; omega)
  · intro k inside; exact represented.entries k (List.mem_range.mp inside)

end PtxTorchLean.Poisson.PTX.Assembly
