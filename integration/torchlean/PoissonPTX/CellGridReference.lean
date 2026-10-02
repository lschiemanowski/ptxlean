import PoissonPTX.CellGridAssembly
import PoissonPTX.OperatorArrayCorrespondence

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- The public executable reference returns exactly the vector published by the
actual unmasked cell/assembly composition. Input checks and execution/source
premises are explicit; no desired intermediate value is assumed. -/
theorem assembly_reference {o : Operator} {values : Array Float}
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
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element false a.boundary a.output)
      (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final)
    (compatible : Concurrent.Visibility.Compatible
      (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0) words wordSource)
    (indexCompatible : IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices indexSource)
    (done : ∀ i, (final i).halted=true)
    (size : values.size=o.mesh.points.size) (finite : values.all Float.isFinite=true) :
    Poisson.apply o values=.ok (Array.ofFn fun node : Fin o.mesh.points.size =>
      decode (read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words)
        (Assembly.Snapshot.address a node))) := by
  rw [ArrayOperator.apply_correspondence o shape same values size finite]
  congr 1
  apply congrArg Array.ofFn
  funext node
  have result := assembly_operator grid shape same a base element
    offsetsBefore entriesBefore boundaryBefore tables separated regs run compatible indexCompatible done node
  simpa only [Bool.false_eq_true,false_and,ite_false] using result.symm

end PtxTorchLean.Poisson.PTX.CellGrid
