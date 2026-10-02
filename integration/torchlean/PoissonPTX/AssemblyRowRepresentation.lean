import PoissonPTX.AssemblyCompressedRows
import PoissonPTX.AssemblyParallelExists

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Input integer representation of concatenated rows. Offsets and indices
are decoded from the actual initial bytes, independently of any sum or output.
The entry-array length is fixed by the serialized row lists. -/
structure Arena.RowsEncoded (a : Arena n) (memory : Memory) (rows : List (List Nat)) : Prop where
  count : rows.length=n
  size : rows.flatten.length=a.entryCount
  offsets : ∀ i≤n, a.offset memory i=CompressedRows.offset rows i
  entries : ∀ k<a.entryCount, a.entryIndex memory k=rows.flatten[k]?.getD 0
  bounded : ∀ row∈rows, ∀ index∈row, index<a.elementCount

variable {n : Nat} {a : Arena n} {memory : Memory} {rows : List (List Nat)}

/-- Table decoding discharges the assembly cursor and contribution-index
safety premises. It does not posit a loop state or expected output. -/
theorem Arena.RowsEncoded.contents (represented : a.RowsEncoded memory rows) : a.Contents memory := by
  constructor
  · intro i inside
    rw [represented.offsets i (by omega),represented.offsets (i+1) (by omega),
      CompressedRows.offset_next rows i (by rw [represented.count]; exact inside)]
    omega
  · intro i inside
    rw [represented.offsets (i+1) (by omega),← represented.size]
    exact CompressedRows.offset_le_length rows (i+1)
  · intro k inside
    change a.entryIndex memory k<a.elementCount
    rw [represented.entries k inside]
    have valid : k<rows.flatten.length := by rw [represented.size]; exact inside
    have member : rows.flatten[k]?.getD 0∈rows.flatten := by simp only [List.getElem?_eq_getElem valid,Option.getD_some]; exact List.getElem_mem valid
    obtain ⟨row,rowMember,inRow⟩ := List.mem_flatten.mp member
    exact represented.bounded row rowMember _ inRow

/-- The two physical offsets and intervening entry words recover the exact
ordered row, including empty lists and repeated cell indices. -/
theorem Arena.RowsEncoded.row (represented : a.RowsEncoded memory rows) (i : Fin n) :
    a.row memory i=rows[i.val]'(by rw [represented.count]; exact i.isLt) := by
  have inside : i.val<rows.length := by rw [represented.count]; exact i.isLt
  unfold Arena.row
  rw [represented.offsets i.val (by have := i.isLt; omega),represented.offsets (i.val+1) (by have := i.isLt; omega)]
  rw [← CompressedRows.reconstruct rows i.val inside]
  apply List.map_congr_left
  intro k member
  apply represented.entries
  obtain ⟨lower,upper⟩ := List.mem_range'.mp member
  have next := CompressedRows.offset_next rows i.val inside
  have last := CompressedRows.offset_le_length rows (i.val+1)
  rw [← represented.size]
  omega

/-- Ordered lists for all mesh nodes. Filtering retains the encounter order
used by the host's element-major connectivity scan. -/
def nodeRows (nodes : Nat) (locations : List (Nat × Nat)) : List (List Nat) :=
  (List.finRange nodes).map fun i => Rows.selected locations i.val

theorem nodeRows_get (i : Fin n) : (nodeRows n locations)[i.val]'(by simp [nodeRows])=Rows.selected locations i.val := by
  simp [nodeRows]

/-- Serialized table representation supplies the ordered-row premise of the
actual parallel scatter theorem. -/
theorem Arena.RowsEncoded.selected (represented : a.RowsEncoded memory (nodeRows n locations)) (i : Fin n) :
    a.row memory i=Rows.selected locations i.val := by
  rw [represented.row i]
  exact nodeRows_get i

end PtxTorchLean.Poisson.PTX.Assembly
