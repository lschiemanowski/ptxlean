import PoissonPTX.CellGridAssembly
import PoissonPTX.AssemblyPreservation
import PoissonPTX.ParallelResidualLayout

namespace PtxTorchLean.Poisson.PTX.CellGrid
variable {o : Operator} {values : Array Float}

/-- Link the physical operator and residual arenas. Only addresses and extents
are fields; no computed residual, matrix value or memory-preservation premise. -/
structure ResidualLayout (grid : Admitted o values) (a : Assembly.Arena o.mesh.points.size)
    (r : Weak.Residual.Parallel.Arena o.mesh.points.size) : Prop where
  base : r.base=a.base
  cellBase : a.base=grid.candidates.base
  applied : r.ap=a.output
  rhsBefore : r.rhs.toNat+o.mesh.points.size*8≤grid.candidates.output.toNat
  rhsApart : a.output.toNat+o.mesh.points.size*8≤r.rhs.toNat ∨
    r.rhs.toNat+o.mesh.points.size*8≤a.output.toNat

/-- The cell grid's actual stores preserve a whole input word below its output. -/
theorem Admitted.input_word64 (grid : Admitted o values) (address : Nat)
    (before : address+8≤grid.candidates.base.toNat+grid.candidates.output.toNat) :
    read64 (publish grid.candidates.memory grid.events) address=read64 grid.candidates.memory address := by
  apply PTX.Sources.word_eq_of_bytes
  intro k
  simp only [PTX.Sources.byte_read64]
  apply grid.before
  have := k.isLt
  omega

/-- The same uploaded right-hand side survives both actual launch publications. -/
theorem ResidualLayout.rhs_preserved (layout : ResidualLayout grid a r)
    (regs : Fin o.mesh.points.size → Registers)
    (run : Flow.Parallel.Runs a.context
      (Assembly.entryCode (BitVec.ofNat 32 o.mesh.points.size) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start (publish grid.candidates.memory grid.events) (regs i)) words indices final)
    (node : Fin o.mesh.points.size) :
    read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words)
        (r.base.toNat+node.val*8+r.rhs.toNat)=
      read64 grid.candidates.memory (r.base.toNat+node.val*8+r.rhs.toNat) := by
  rw [a.parallel_preserves_word _ regs run _ ?_]
  · apply grid.input_word64
    rw [layout.base,layout.cellBase]
    have bound := layout.rhsBefore
    have inside := node.isLt
    omega
  · intro thread
    rw [layout.base]
    unfold PTX.Sources.Disjoint
    have apart := layout.rhsApart
    have hn := node.isLt
    have ht := thread.isLt
    omega

end PtxTorchLean.Poisson.PTX.CellGrid
