import PoissonPTX.CellFamilyInputs
import PoissonPTX.OperatorMesh
import PoissonPTX.AssemblyOperator

namespace PtxTorchLean.Poisson.PTX

/-- Compose proved cell executions and the actual source-admitted assembly
launch. Assembly consumes the publication of those cell histories; its input
tables are checked in the original uploaded memory and preserved by the cell
stores. Neither local cell values nor an assembled result are assumed.

The publication-to-next-launch boundary is explicit mathematical byte memory.
This theorem does not establish CUDA transport or arbitrary grid scheduling. -/
theorem cell_assembly_operator {o : Operator} {values : Array Float}
    {words : List (Concurrent.Event o.mesh.points.size)}
    {indices : List (Fin o.mesh.points.size × IndexSources.Access)}
    {final : Fin o.mesh.points.size → Flow.State}
    (family : CellWhole.Family o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (order : List (Fin o.mesh.cells.size)) (complete : ∀ i, i∈order)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=family.base) (element : a.element=family.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤family.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤family.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤family.output.toNat)
    (tables : a.RowsEncoded family.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation)
    (regs : Fin o.mesh.points.size → Registers)
    (run : Flow.Parallel.Runs a.context
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start (family.publish family.memory order) (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible
      (fun space => match space with | .global => family.publish family.memory order | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible (family.publish family.memory order) words indices indexSource)
    (done : ∀ i, (final i).halted=true) (node : Fin o.mesh.points.size) :
    decode (read64 (Concurrent.GlobalPublication.publish (family.publish family.memory order) words) (Assembly.Snapshot.address a node))=
      if mask=true ∧ read32 family.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
        shape.operator same values node := by
  rw [← family.input_word32 family.memory order (a.base.toNat+a.boundary.toNat+node.val*4)
    (by rw [base]; have := node.isLt; omega)]
  apply a.parallel_operator shape.connectivity
    (CoefficientRepresentation.rows same o.b) (CoefficientRepresentation.rows same o.d)
    (CoefficientRepresentation.square same o.w) (OperatorMesh.input values)
    run compatible indexCompatible (family.assembly_tables family.memory order a base offsetsBefore entriesBefore tables)
    separated done
  intro cell i j
  rw [CoefficientRepresentation.local_action,← shape.gather]
  have result := family.published_entry family.memory order cell (complete cell) i j
  unfold Assembly.Arena.elementValue
  rw [base,element]
  simpa only [CellWhole.Family.address,Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

/-- For any supplied actual cell executions, valid uploaded assembly metadata
admits a returning next launch with the proved operator result. Whole-cell
execution existence remains a separate obligation. -/
theorem cell_assembly_exists {o : Operator} {values : Array Float}
    (family : CellWhole.Family o values) (shape : OperatorMesh o)
    (same : o.q.size=o.nodes.size)
    (order : List (Fin o.mesh.cells.size)) (complete : ∀ i, i∈order)
    (a : Assembly.Arena o.mesh.points.size)
    (base : a.base=family.base) (element : a.element=family.output)
    (offsetsBefore : a.offsets.toNat+(o.mesh.points.size+1)*4≤family.output.toNat)
    (entriesBefore : a.entries.toNat+a.entryCount*4≤family.output.toNat)
    (boundaryBefore : a.boundary.toNat+o.mesh.points.size*4≤family.output.toNat)
    (tables : a.RowsEncoded family.memory (Assembly.nodeRows o.mesh.points.size (Assembly.MeshRows.locations shape.connectivity)))
    (separated : a.InputSeparation) (regs : Fin o.mesh.points.size → Registers) (mask : Bool) :
    ∃ words indices final,
      Flow.Parallel.Runs a.context
        (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
        (fun i => a.start (family.publish family.memory order) (regs i)) words indices final ∧
      (∀ i, (final i).halted=true) ∧
      Concurrent.Visibility.Compatible
        (fun space => match space with | .global => family.publish family.memory order | .shared => fun _ => 0)
        words (fun _ _ => .initial) ∧
      IndexSources.Compatible (family.publish family.memory order) words indices (fun _ _ => .initial) ∧
      ∀ node, decode (read64 (Concurrent.GlobalPublication.publish (family.publish family.memory order) words) (Assembly.Snapshot.address a node))=
        if mask=true ∧ read32 family.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
          shape.operator same values node := by
  have encoded := family.assembly_tables family.memory order a base offsetsBefore entriesBefore tables
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible⟩ :=
    a.parallel_exists (family.publish family.memory order) regs encoded.contents mask
  exact ⟨words,indices,final,run,done,compatible,indexCompatible,
    cell_assembly_operator family shape same order complete a base element offsetsBefore entriesBefore
      boundaryBefore tables separated regs run compatible indexCompatible done⟩

end PtxTorchLean.Poisson.PTX
