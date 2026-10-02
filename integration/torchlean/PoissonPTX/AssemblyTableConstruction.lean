import PoissonPTX.AssemblyRowRepresentation

namespace PtxTorchLean.Poisson.PTX.Assembly.Rows

/-- The host's encounter-order construction: append each contribution slot to
the list belonging to its mesh node. -/
def insert (rows : Nat → List Nat) (item : Nat × Nat) : Nat → List Nat :=
  Function.update rows item.1 (rows item.1++[item.2])

def scan (locations : List (Nat × Nat)) : Nat → List Nat :=
  locations.foldl insert (fun _ => [])

theorem scan_from (locations : List (Nat × Nat)) (rows : Nat → List Nat) (node : Nat) :
    locations.foldl insert rows node=rows node++selected locations node := by
  induction locations generalizing rows with
  | nil => simp [selected]
  | cons item rest ih =>
    simp only [List.foldl_cons,ih]
    by_cases same : item.1=node
    · subst node; simp [insert,selected,List.append_assoc]
    · simp [insert,selected,same,Ne.symm same]

/-- Appending contributions while scanning connectivity constructs exactly the
filtered ordered list used in the assembly correspondence theorem. -/
theorem scan_selected : scan locations node=selected locations node := by
  simpa [scan] using scan_from locations (fun _ => []) node

theorem selected_bound (locations : List (Nat × Nat))
    (bounded : ∀ item∈locations, item.2<count) (index : Nat) (member : index∈selected locations node) :
    index<count := by
  obtain ⟨item,selected,eq⟩ := List.mem_map.mp member
  subst index
  exact bounded item (List.mem_filter.mp selected).1

end PtxTorchLean.Poisson.PTX.Assembly.Rows

namespace PtxTorchLean.Poisson.PTX.Assembly

theorem nodeRows_bound (locations : List (Nat × Nat))
    (bounded : ∀ item∈locations, item.2<count) (row : List Nat) (selected : row∈nodeRows n locations)
    (index : Nat) (member : index∈row) : index<count := by
  obtain ⟨i,_,eq⟩ := List.mem_map.mp selected
  subst row
  exact Rows.selected_bound locations bounded index member

end PtxTorchLean.Poisson.PTX.Assembly
