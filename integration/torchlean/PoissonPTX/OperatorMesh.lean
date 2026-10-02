import PoissonPTX.AssemblyMeshRows
import PoissonPTX.CellCoefficientRepresentation

namespace PtxTorchLean.Poisson.PTX

/-- The actual array connectivity has the shape and bounds required by the
shape-safe tensor specification. Nodes are decoded from these input arrays;
there is no separately supplied mathematical mesh. -/
structure OperatorMesh (o : Operator) : Prop where
  width : ∀ e<o.mesh.cells.size, o.mesh.cells[e]!.size=o.nodes.size*o.nodes.size
  nodes : ∀ e<o.mesh.cells.size, ∀ k<o.nodes.size*o.nodes.size, (o.mesh.cells[e]!)[k]!<o.mesh.points.size

variable {o : Operator}

def OperatorMesh.connectivity (shape : OperatorMesh o) :
    Correspondence.Connectivity o.mesh.cells.size o.nodes.size o.mesh.points.size where
  node := fun element i j => ⟨(o.mesh.cells[element.val]!)[i.val*o.nodes.size+j.val]!,
    shape.nodes element.val element.isLt _ (Correspondence.row_major_bound i j)⟩

def OperatorMesh.input (values : Array Float) : Fin o.mesh.points.size → Float := fun i => values[i.val]!

/-- The TorchLean cell gather reads the same actual connectivity and input
array entries as the bounded mesh adapter. -/
theorem OperatorMesh.gather (shape : OperatorMesh o) (values : Array Float) (element : Fin o.mesh.cells.size) :
    Poisson.gather o values element.val=matrix (Correspondence.gathered shape.connectivity (OperatorMesh.input values) element) := rfl

/-- Tensor formulation of the represented operator. Equality of quadrature
and cell dimensions is explicit, as required by this emitted PTX fragment. -/
def OperatorMesh.operator (shape : OperatorMesh o) (same : o.q.size=o.nodes.size) (values : Array Float) :
    Fin o.mesh.points.size → Float :=
  Correspondence.tensorOperator shape.connectivity
    (CoefficientRepresentation.rows same o.b) (CoefficientRepresentation.rows same o.d)
    (CoefficientRepresentation.square same o.w) (OperatorMesh.input values)

end PtxTorchLean.Poisson.PTX
