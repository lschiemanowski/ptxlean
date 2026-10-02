import PoissonPTX.CellGridResidualInputs

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- The fresh-residual kernel reads the actual cell/assembly publication and
publishes right-hand side minus the rounded TorchLean operator. No operator
output or preserved input word is supplied as an assumption. This is a binary64
subtraction theorem, not yet the exact-real norm bound or PCG stopping theorem. -/
theorem residual_correspondence {o : Operator} {values : Array Float}
    {words : List (Concurrent.Event o.mesh.points.size)}
    {indices : List (Fin o.mesh.points.size × IndexSources.Access)}
    {final : Fin o.mesh.points.size → Flow.State}
    (grid : Admitted o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=grid.candidates.base) (element : a.element=grid.candidates.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤grid.candidates.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤grid.candidates.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤grid.candidates.output.toNat)
    (tables : a.RowsEncoded grid.candidates.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation)
    (regs : Fin o.mesh.points.size → Registers)
    (run : Flow.Parallel.Runs a.context
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible
      (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices indexSource)
    (done : ∀ i, (final i).halted=true)
    (r : Weak.Residual.Parallel.Arena o.mesh.points.size)
    (layout : ResidualLayout grid a r)
    (residualRegs : Fin o.mesh.points.size → Registers)
    (candidate : Weak.Residual.Parallel.Candidate
      (r.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) residualRegs))
    (residualSource)
    (residualCompatible : PTX.Sources.Compatible
      (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words)
      (Weak.Residual.Parallel.events
        (r.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) residualRegs) candidate)
      residualSource)
    (order : List (Fin o.mesh.points.size)) (complete : ∀ i, i∈order)
    (node : Fin o.mesh.points.size) :
    decode (read64 (Weak.Residual.Parallel.publish
        (r.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) residualRegs)
        candidate order) (r.base.toNat+node.val*8+r.output.toNat))=
      decode (read64 grid.candidates.memory (r.base.toNat+node.val*8+r.rhs.toNat)) -
        (if mask=true ∧ read32 grid.candidates.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
          shape.operator same values node) := by
  let memory := Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words
  let p := r.inputs memory residualRegs
  have result := (congrArg decode (Weak.Residual.Parallel.published_word p candidate node
      (r.output_ownership memory residualRegs) order (complete node))).trans
    (Weak.Residual.Parallel.stored_value p candidate residualSource residualCompatible
      (r.input_separation memory residualRegs) node)
  change decode (read64 _ (p.addr node r.output))=
    decode (read64 memory (p.addr node r.rhs))-decode (read64 memory (p.addr node r.ap)) at result
  simp only [p,r.addr memory residualRegs node r.output (by simp),
    r.addr memory residualRegs node r.rhs (by simp),r.addr memory residualRegs node r.ap (by simp)] at result
  rw [result]
  have rhs := layout.rhs_preserved regs run node
  have applied := assembly_operator grid shape same a base element offsetsBefore entriesBefore boundaryBefore
    tables separated regs run compatible indexCompatible done node
  have address : r.base.toNat+node.val*8+r.ap.toNat=Assembly.Snapshot.address a node := by
    rw [layout.base,layout.applied]
    simp only [Assembly.Snapshot.address]
    omega
  rw [address]
  change _=decode (read64 grid.candidates.memory _)-_
  rw [rhs,applied]

end PtxTorchLean.Poisson.PTX.CellGrid
