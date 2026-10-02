import PoissonPTX.AssemblyRows

namespace PtxTorchLean.Poisson.PTX.Assembly.CompressedRows

/-- Start of row `i` in the concatenated contribution lists. The final offset
is the total number of entries. No sorting or floating-point work occurs. -/
def offset : List (List Nat) → Nat → Nat
  | _,0 => 0
  | [],_+1 => 0
  | row::rows,i+1 => row.length+offset rows i

theorem offset_le_length (rows : List (List Nat)) (i : Nat) :
    offset rows i≤rows.flatten.length := by
  induction rows generalizing i with
  | nil => cases i <;> simp [offset]
  | cons row rows ih =>
    cases i with
    | zero => simp [offset]
    | succ i => simpa only [offset,List.flatten_cons,List.length_append] using Nat.add_le_add_left (ih i) row.length

theorem offset_next (rows : List (List Nat)) (i : Nat) (inside : i<rows.length) :
    offset rows (i+1)=offset rows i+rows[i].length := by
  induction rows generalizing i with
  | nil => simp at inside
  | cons row rows ih =>
    cases i with
    | zero => simp [offset]
    | succ i => simpa [offset,Nat.add_assoc] using congrArg (row.length+·) (ih i (by simpa using inside))

theorem entry (rows : List (List Nat)) (i : Nat) (inside : i<rows.length)
    (k : Nat) (inRow : k<rows[i].length) :
    rows.flatten[offset rows i+k]?=rows[i][k]? := by
  induction rows generalizing i with
  | nil => simp at inside
  | cons row rows ih =>
    cases i with
    | zero => simpa [offset] using List.getElem?_append_left (l₁:=row) (l₂:=rows.flatten) inRow
    | succ i =>
      simp only [offset,List.flatten_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left,Nat.add_assoc] using ih i (by simpa using inside) inRow

theorem range_inside (rows : List (List Nat)) (i : Nat) (inside : i<rows.length)
    (k : Nat) (inRow : k<rows[i].length) : offset rows i+k<rows.flatten.length := by
  have next := offset_next rows i inside
  have limit := offset_le_length rows (i+1)
  omega

/-- Reading a row by its two offsets and following the concatenated entry
array reconstructs exactly the original ordered list. Empty rows are allowed. -/
theorem reconstruct (rows : List (List Nat)) (i : Nat) (inside : i<rows.length) :
    ((List.range' (offset rows i) (offset rows (i+1)-offset rows i)).map
      (fun k => rows.flatten[k]?.getD 0))=rows[i] := by
  rw [offset_next rows i inside,Nat.add_sub_cancel_left]
  apply List.ext_getElem
  · simp
  · intro k left right
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul]
    rw [entry rows i inside k right]
    simp [List.getElem?_eq_getElem right]

end PtxTorchLean.Poisson.PTX.Assembly.CompressedRows
