import PoissonPTX.CellGridRoundedResidual

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Valid physical assembly metadata admits a complete rounded execution with
the represented operator result after the actual cell grid publication. -/
theorem rounded_assembly_exists {o : Operator} {values : Array Float}
    (grid : Admitted o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=grid.candidates.base) (element : a.element=grid.candidates.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤grid.candidates.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤grid.candidates.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤grid.candidates.output.toNat)
    (tables : a.RowsEncoded grid.candidates.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation) (regs : Fin (Rounded.count o.mesh.points.size) → Registers) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs (Rounded.context a.base)
        (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
        (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible
        (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices (fun _ _ => .initial) ∧
      ∀ node, decode (read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (Assembly.Snapshot.address a node))=
        if mask=true ∧ read32 grid.candidates.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
          shape.operator same values node := by
  have encoded := grid.assembly_tables a base offsetsBefore entriesBefore tables
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible,_⟩ :=
    a.rounded_exists (publish grid.candidates.memory grid.events) regs encoded.contents separated mask
  exact ⟨words,indices,final,run,done,compatible,indexCompatible,
    rounded_assembly_operator grid shape same a base element offsetsBefore entriesBefore
      boundaryBefore tables separated regs run compatible indexCompatible done⟩

end PtxTorchLean.Poisson.PTX.CellGrid
