import PoissonPTX.OperatorArray

namespace PtxTorchLean.Poisson.PTX.ArrayOperator
open Correspondence

theorem range_product (m n : Nat) :
    List.range (m*n)=(List.range m).flatMap (fun i => (List.range n).map (fun j => i*n+j)) := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_mul,List.range_add,List.range_succ,List.flatMap_append,← ih]

theorem finRange_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem <;> simp

theorem localValues_entry (o : Operator) (values : Array Float)
    (e : Fin o.mesh.cells.size) (i j : Fin o.nodes.size) :
    ((localValues o values)[e.val]!)[i.val*o.nodes.size+j.val]! =
      entries (localAction o.b o.d o.w (gather o values e.val)) i j := by
  have inside := row_major_bound i j
  obtain ⟨row,col⟩ := Concurrent.CellMiddle.Numeric.row_col i j
  simp [localValues,flat,e.isLt,inside,row,col,entries]

/-- The imperative array loops enumerate exactly the same contributions as the
shape-safe tensor definition, including element and local row-major order. -/
theorem contributions_tensor (o : Operator) (shape : OperatorMesh o) (values : Array Float) :
    contributions o.mesh.cells (localValues o values)=
      (Correspondence.contributions shape.connectivity (fun e => entries (localAction o.b o.d o.w (gather o values e.val)))).map
        (fun item => (item.1.val,item.2)) := by
  simp only [contributions,Correspondence.contributions,List.map_flatMap,List.map_map,Function.comp_def]
  rw [← finRange_values o.mesh.cells.size,List.flatMap_map]
  congr 1
  funext e
  rw [shape.width e.val e.isLt,range_product]
  simp only [List.map_flatMap,List.map_map]
  rw [← finRange_values o.nodes.size,List.flatMap_map]
  congr 1
  funext i
  simp only [List.map_map]
  congr 1
  funext j
  simp only [Function.comp_def,localValues_entry]
  rfl

end PtxTorchLean.Poisson.PTX.ArrayOperator
