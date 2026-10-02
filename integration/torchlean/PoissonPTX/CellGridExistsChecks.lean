import PoissonPTX.CellGridExists
import PoissonPTX.CellGridAssembly
import PoissonPTX.CellAssemblyChecks

namespace PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks
open CellAssemblyWitness

/-- The previously kernel-checked nonzero cell now has an admitted grid
schedule; the grid is constructed, not assumed in this regression. -/
theorem nonzero_grid : ∃ grid : Admitted operator values, grid.candidates=family.candidates :=
  family_exists family 192 224 (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)

/-- Construct the nonzero grid and a returning assembly launch. Its observed
publication is eight. This reuses proved execution evidence rather than
re-expanding the large cell computation during a regression check. -/
theorem nonzero_assembly : ∃ grid : Admitted operator values, ∃ words indices final,
    Flow.Parallel.Runs arena.context (Assembly.entryCode 1 208 240 256 false 232 216)
      (fun _ => arena.start (publish grid.candidates.memory grid.events) (fun _ => 0)) words indices final ∧
    (∀ i, (final i).halted=true) ∧
    Concurrent.Visibility.Compatible
      (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0)
      words (fun _ _ => .initial) ∧
    IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices (fun _ _ => .initial) ∧
    decode (read64 (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) 216)=8 := by
  obtain ⟨grid,same⟩ := nonzero_grid
  have base : arena.base=grid.candidates.base := by rw [same]; rfl
  have output : arena.element=grid.candidates.output := by rw [same]; rfl
  have offsets : arena.offsets.toNat+(operator.mesh.points.size+1)*4≤grid.candidates.output.toNat := by rw [same]; decide
  have entries : arena.entries.toNat+arena.entryCount*4≤grid.candidates.output.toNat := by rw [same]; decide
  have boundary : arena.boundary.toNat+operator.mesh.points.size*4≤grid.candidates.output.toNat := by rw [same]; decide
  have tables : arena.RowsEncoded grid.candidates.memory
      (Assembly.nodeRows operator.mesh.points.size (Assembly.MeshRows.locations meshShape.connectivity)) := by
    rw [same]; exact arena.checkRows_sound tables_checked
  obtain ⟨words,indices,final,run,done,compatible,indexCompatible,correct⟩ :=
    assembly_exists grid meshShape rfl arena base output offsets entries boundary tables separated (fun _ _ => 0) false
  refine ⟨grid,words,indices,final,run,done,compatible,indexCompatible,?_⟩
  have value := correct ⟨0,by decide⟩
  simpa only [Assembly.Snapshot.address,
    show arena.base.toNat+arena.output.toNat+0*8=216 from rfl,
    Bool.false_eq_true,false_and,ite_false,numerical] using value

end PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks
