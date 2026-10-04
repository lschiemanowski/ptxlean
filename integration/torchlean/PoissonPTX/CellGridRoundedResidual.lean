import PoissonPTX.CellGridRoundedAssembly
import PoissonPTX.FreshResidualRoundedCorrect

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Actual cell publication, complete rounded assembly and complete rounded
residual execution yield the rounded residual of the same represented operator.
There is no supplied residual value or assumed preservation of input bytes. -/
theorem rounded_residual_correspondence {o : Operator} {values : Array Float}
    {words : List (Concurrent.Event (Rounded.count o.mesh.points.size))}
    {indices : List (Fin (Rounded.count o.mesh.points.size) × IndexSources.Access)}
    {final : Fin (Rounded.count o.mesh.points.size) → Flow.State}
    (grid : Admitted o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=grid.candidates.base) (element : a.element=grid.candidates.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤grid.candidates.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤grid.candidates.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤grid.candidates.output.toNat)
    (tables : a.RowsEncoded grid.candidates.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation)
    (regs : Fin (Rounded.count o.mesh.points.size) → Registers)
    (run : Flow.Parallel.Runs (Rounded.context a.base)
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible
      (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices indexSource)
    (done : ∀ i, (final i).halted=true)
    (r : Weak.Residual.Parallel.Arena o.mesh.points.size)
    (layout : ResidualLayout grid a r)
    (residualRegs : Fin (Rounded.count o.mesh.points.size) → Registers)
    {residualWords : List (Concurrent.Event (Rounded.count o.mesh.points.size))}
    {residualIndices : List (Fin (Rounded.count o.mesh.points.size) × IndexSources.Access)}
    {residualFinal : Fin (Rounded.count o.mesh.points.size) → Flow.State}
    (residualRun : Flow.Parallel.Runs (Rounded.context r.base) (FreshResidual.Arena.program r)
      (fun i => FreshResidual.Arena.start r
        (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (residualRegs i))
      residualWords residualIndices residualFinal)
    (residualCompatible : Concurrent.Visibility.Compatible
      (fun space => match space with
        | .global => Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words
        | .shared => fun _ => 0) residualWords residualSource)
    (residualDone : ∀ i, (residualFinal i).halted=true)
    (node : Fin o.mesh.points.size) :
    decode (read64 (Concurrent.GlobalPublication.publish
      (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) residualWords)
      (r.base.toNat+node.val*8+r.output.toNat))=
      decode (read64 grid.candidates.memory (r.base.toNat+node.val*8+r.rhs.toNat)) -
        (if mask=true ∧ read32 grid.candidates.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
          shape.operator same values node) := by
  have result := FreshResidual.Arena.rounded_correct residualRun residualCompatible residualDone node
  change decode (read64 _ (r.base.toNat+node.val*8+r.output.toNat))=
    decode (read64 _ (r.base.toNat+node.val*8+r.rhs.toNat))-
    decode (read64 _ (r.base.toNat+node.val*8+r.ap.toNat)) at result
  rw [result,layout.rounded_rhs_preserved regs run done node]
  have applied := rounded_assembly_operator grid shape same a base element offsetsBefore entriesBefore boundaryBefore
    tables separated regs run compatible indexCompatible done node
  have address : r.base.toNat+node.val*8+r.ap.toNat=Assembly.Snapshot.address a node := by
    rw [layout.base,layout.applied]
    simp only [Assembly.Snapshot.address]
    omega
  rw [address,applied]

end PtxTorchLean.Poisson.PTX.CellGrid
