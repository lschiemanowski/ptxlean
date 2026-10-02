import PoissonPTX.CellGridInputs
import PoissonPTX.OperatorMesh
import PoissonPTX.AssemblyOperator

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- Actual interleaved cell stores followed by admitted assembly yield the
ordered TorchLean tensor operator. CUDA transport between launches and full PTX
memory-model admission remain outside this fragment theorem. -/
theorem assembly_operator {o : Operator} {values : Array Float}
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
    (done : ∀ i, (final i).halted=true) (node : Fin o.mesh.points.size) :
    decode (read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (Assembly.Snapshot.address a node))=
      if mask=true ∧ read32 grid.candidates.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
        shape.operator same values node := by
  rw [← grid.input_word32 (a.base.toNat+a.boundary.toNat+node.val*4)
    (by rw [base]; have := node.isLt; omega)]
  apply a.parallel_operator shape.connectivity
    (CoefficientRepresentation.rows same o.b) (CoefficientRepresentation.rows same o.d)
    (CoefficientRepresentation.square same o.w) (OperatorMesh.input values)
    run compatible indexCompatible (grid.assembly_tables a base offsetsBefore entriesBefore tables)
    separated done
  intro cell i j
  rw [CoefficientRepresentation.local_action,← shape.gather]
  have result := grid.entry cell i j
  unfold Assembly.Arena.elementValue
  rw [base,element]
  simpa only [Admitted.family,Candidates.withSources,CellWhole.Family.address,Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

/-- For any supplied actual cell executions, valid uploaded assembly metadata
admits a returning next launch with the proved operator result. Whole-cell
execution existence remains a separate obligation. -/
theorem assembly_exists {o : Operator} {values : Array Float}
    (grid : Admitted o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=grid.candidates.base) (element : a.element=grid.candidates.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤grid.candidates.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤grid.candidates.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤grid.candidates.output.toNat)
    (tables : a.RowsEncoded grid.candidates.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation) (regs : Fin o.mesh.points.size → Registers) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context
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
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible⟩ :=
    a.parallel_exists (publish grid.candidates.memory grid.events) regs encoded.contents mask
  exact ⟨words,indices,final,run,done,compatible,indexCompatible,
    assembly_operator grid shape same a base element offsetsBefore entriesBefore
      boundaryBefore tables separated regs run compatible indexCompatible done⟩

end PtxTorchLean.Poisson.PTX.CellGrid
