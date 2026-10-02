import PoissonPTX.OperatorArrayRows

namespace PtxTorchLean.Poisson.PTX.ArrayOperator
open Correspondence

@[simp] theorem result_size (o : Operator) (values : Array Float) :
    (result o values).size=o.mesh.points.size := by
  simp [result,scatter_fold,fold_size]

/-- The executable array result is the same rounded operator as the tensor
specification, without any reassociation of floating-point additions. -/
theorem result_get (o : Operator) (shape : OperatorMesh o) (same : o.q.size=o.nodes.size)
    (values : Array Float) (node : Fin o.mesh.points.size) :
    (result o values)[node.val]! = shape.operator same values node := by
  unfold result
  rw [scatter_fold,fold_get _ _ (fun _ => 0) (by intro i hi; simpa using (show (Array.replicate o.mesh.points.size (0 : Float))[i]! = 0 by simp_all)) node.val (by simpa using node.isLt)]
  rw [contributions_tensor o shape values,Assembly.MeshRows.scatter_indices _ _ _ (by intro i; rfl)]
  simp only [OperatorMesh.operator,tensorOperator,tensorContributions,Array.getElem_ofFn]
  simp_rw [CoefficientRepresentation.local_action,← shape.gather]

theorem result_tensor (o : Operator) (shape : OperatorMesh o) (same : o.q.size=o.nodes.size)
    (values : Array Float) : result o values=Array.ofFn (shape.operator same values) := by
  apply Array.ext
  · simp
  · intro i hi hj
    have inside : i<o.mesh.points.size := by simpa using hi
    have value := result_get o shape same values ⟨i,inside⟩
    simpa only [getElem!_pos (result o values) i hi,Array.getElem_ofFn] using value

/-- Agreement with the public executable TorchLean reference entry, retaining
its input checks and naming the represented operator's actual connectivity. -/
theorem apply_correspondence (o : Operator) (shape : OperatorMesh o) (same : o.q.size=o.nodes.size)
    (values : Array Float) (size : values.size=o.mesh.points.size)
    (finite : values.all Float.isFinite=true) :
    Poisson.apply o values=.ok (Array.ofFn (shape.operator same values)) := by
  rw [apply_valid o values size finite,result_tensor o shape same values]

end PtxTorchLean.Poisson.PTX.ArrayOperator
