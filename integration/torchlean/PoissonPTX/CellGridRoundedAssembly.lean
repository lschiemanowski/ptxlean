import PoissonPTX.CellGridResidualInputs
import PoissonPTX.AssemblyRoundedCorrect

namespace PtxTorchLean.Poisson.PTX.CellGrid

/-- The complete rounded assembly launch retains the connection to the
represented TorchLean operator, including its actual published boundary mask. -/
theorem rounded_assembly_operator {o : Operator} {values : Array Float}
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
    (done : ∀ i, (final i).halted=true) (node : Fin o.mesh.points.size) :
    decode (read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (Assembly.Snapshot.address a node))=
      if mask=true ∧ read32 grid.candidates.memory (a.base.toNat+a.boundary.toNat+node.val*4)≠0 then 0 else
        shape.operator same values node := by
  obtain ⟨sameWords,sameIndices⟩ := Rounded.history a.small
    (by rw [← Assembly.entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  have activeRun := Flow.Parallel.restrict_run Rounded.enough run
  have activeCompatible := Flow.Parallel.unrename_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=o.mesh.points.size)))
    (words:=words.filterMap (Flow.Parallel.restrictEvent o.mesh.points.size))
    (by rw [sameWords]; exact compatible)
  have activeIndices := Flow.Parallel.unrename_index_compatible
    (rename:=Fin.castLE (Rounded.enough (n:=o.mesh.points.size)))
    (words:=words.filterMap (Flow.Parallel.restrictEvent o.mesh.points.size))
    (indices:=indices.filterMap (Flow.Parallel.restrictIndex o.mesh.points.size))
    (by rw [sameWords,sameIndices]; exact indexCompatible)
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact assembly_operator grid shape same a base element offsetsBefore entriesBefore boundaryBefore tables separated
    (fun i => regs (i.castLE Rounded.enough)) activeRun activeCompatible activeIndices
    (fun i => done (i.castLE Rounded.enough)) node

/-- Preserve the same right-hand side across both actual publications,
including all inactive assembly lanes. -/
theorem ResidualLayout.rounded_rhs_preserved {o : Operator} {values : Array Float}
    {grid : Admitted o values} {a : Assembly.Arena o.mesh.points.size}
    {r : Weak.Residual.Parallel.Arena o.mesh.points.size}
    {words : List (Concurrent.Event (Rounded.count o.mesh.points.size))}
    {indices : List (Fin (Rounded.count o.mesh.points.size) × IndexSources.Access)}
    {final : Fin (Rounded.count o.mesh.points.size) → Flow.State}
    (layout : ResidualLayout grid a r)
    (regs : Fin (Rounded.count o.mesh.points.size) → Registers)
    (run : Flow.Parallel.Runs (Rounded.context a.base)
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final)
    (done : ∀ i, (final i).halted=true) (node : Fin o.mesh.points.size) :
    read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words)
        (r.base.toNat+node.val*8+r.rhs.toNat)=
      read64 grid.candidates.memory (r.base.toNat+node.val*8+r.rhs.toNat) := by
  obtain ⟨sameWords,_⟩ := Rounded.history a.small
    (by rw [← Assembly.entry_guarded]; exact run) (fun _ => rfl) (fun _ => rfl) done
  rw [← sameWords,Flow.Parallel.rename_publication]
  exact layout.rhs_preserved (fun i => regs (i.castLE Rounded.enough))
    (Flow.Parallel.restrict_run Rounded.enough run) node

end PtxTorchLean.Poisson.PTX.CellGrid
