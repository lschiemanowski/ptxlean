import PoissonPTX.AssemblyRowRepresentation

namespace PtxTorchLean.Poisson.PTX.Assembly.MeshRows
open Correspondence

/-- Element-major, row-major connectivity, paired with the exact flat
cell-value slot used by the PTX element output and assembly input. -/
def locations (mesh : Connectivity e w v) : List (Nat × Nat) :=
  (List.finRange e).flatMap fun element =>
    (List.finRange w).flatMap fun i =>
      (List.finRange w).map fun j =>
        ((mesh.node element i j).val,element.val*(w*w)+i.val*w+j.val)

/-- Converting bounded mesh-node indices to natural indices does not change
which accumulator is updated or the order of floating-point additions. -/
theorem scatter_indices (xs : List (Fin v × Float)) (one : Nat → Float) (two : Fin v → Float)
    (same : ∀ i, one i.val=two i) (i : Fin v) :
    (xs.map (fun item => (item.1.val,item.2))).foldl scatterStep one i.val=
      xs.foldl scatterStep two i := by
  induction xs generalizing one two with
  | nil => exact same i
  | cons item rest ih =>
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    intro j
    by_cases equal : j=item.1
    · subst j; simp [scatterStep,same]
    · have different : j.val≠item.1.val := fun h => equal (Fin.ext h)
      simp [scatterStep,Function.update_of_ne,equal,different,same]

/-- A cell-value representation premise concerns the input bytes of the next
kernel. It is supplied by publication of the cell execution, rather than by an
assumed assembled output. -/
theorem contributions_eq (mesh : Connectivity e w v) (values : Nat → Float)
    (locals : Fin e → Grid Float w)
    (represented : ∀ element i j, values (element.val*(w*w)+i.val*w+j.val)=locals element i j) :
    Rows.contributions (locations mesh) values=
      (Correspondence.contributions mesh locals).map (fun item => (item.1.val,item.2)) := by
  simp only [Rows.contributions,locations,Correspondence.contributions,List.map_flatMap,List.map_map,Function.comp_def]
  congr 1
  funext element
  congr 1
  funext i
  congr 1
  funext j
  rw [represented]

/-- Assembly recovers the complete tensor operator in exactly its original
rounded scatter order. It does not replace the operation by a real-arithmetic
or reassociated sum. -/
theorem operator_sum (mesh : Connectivity e w v) (values : Nat → Float)
    (b d weight : Mat Float w w) (input : Fin v → Float)
    (represented : ∀ element i j, values (element.val*(w*w)+i.val*w+j.val)=
      entries (localAction b d weight (matrix (gathered mesh input element))) i j)
    (node : Fin v) :
    (Rows.contributions (locations mesh) values).foldl scatterStep (fun _ => 0) node.val=
      tensorOperator mesh b d weight input node := by
  rw [contributions_eq mesh values _ represented,scatter_indices _ _ _ (by intro i; rfl)]
  simp only [tensorOperator,tensorContributions,Array.getElem_ofFn]

end PtxTorchLean.Poisson.PTX.Assembly.MeshRows
