import PoissonPTX.CellGridResidual
import PoissonPTX.CellGridExistsChecks

namespace PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks
open CellAssemblyWitness

/-- The synthetic cell's source word doubles as a right-hand side of one.
Assembly writes eight at 216; fresh residual is stored separately at 320. -/
def residualArena : Weak.Residual.Parallel.Arena operator.mesh.points.size where
  base := 0
  rhs := 224
  ap := 216
  output := 320
  bytes := 512
  small := by decide
  aligned := by decide
  noWrap := by decide
  fields := by
    intro off h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> decide
  separated := by
    intro off h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> decide

/-- Constructed admitted cell grid, returning assembly, and actual residual
instruction execution publish one minus eight. The large cell is not evaluated
again: this uses its already checked execution theorem. -/
theorem fresh_minus_seven : ∃ grid : Admitted operator values, ∃ words indices final,
    Flow.Parallel.Runs arena.context (Assembly.entryCode 1 208 240 256 false 232 216)
      (fun _ => arena.start (publish grid.candidates.memory grid.events) (fun _ => 0)) words indices final ∧
    (∀ i, (final i).halted=true) ∧
    Concurrent.Visibility.Compatible
      (fun space => match space with | .global => publish grid.candidates.memory grid.events | .shared => fun _ => 0)
      words (fun _ _ => .initial) ∧
    IndexSources.Compatible (publish grid.candidates.memory grid.events) words indices (fun _ _ => .initial) ∧
    ∃ candidate : Weak.Residual.Parallel.Candidate
        (residualArena.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (fun _ _ => 0)),
      PTX.Sources.Compatible
        (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words)
        (Weak.Residual.Parallel.events
          (residualArena.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (fun _ _ => 0)) candidate)
        (fun _ _ => .initial) ∧
      decode (read64 (Weak.Residual.Parallel.publish
        (residualArena.inputs (Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words) (fun _ _ => 0))
        candidate [⟨0,by decide⟩]) 320)=(-7 : Float) := by
  obtain ⟨grid,same⟩ := ExistsChecks.nonzero_grid
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
  let memory := Concurrent.GlobalPublication.publish (publish grid.candidates.memory grid.events) words
  let p := residualArena.inputs memory (fun _ _ => 0)
  let candidate := Weak.Residual.Parallel.witness p
  have source := Weak.Residual.Parallel.witness_sources p
  refine ⟨grid,words,indices,final,run,done,compatible,indexCompatible,candidate,source,?_⟩
  have layout : ResidualLayout grid arena residualArena := {
    base := rfl
    cellBase := base
    applied := rfl
    rhsBefore := by rw [same]; decide
    rhsApart := by decide }
  have value := residual_correspondence grid meshShape rfl arena base output offsets entries boundary tables separated
    (fun _ _ => 0) run compatible indexCompatible done residualArena layout (fun _ _ => 0)
    candidate (fun _ _ => .initial) source [⟨0,by decide⟩] (by intro i; fin_cases i; simp) ⟨0,by decide⟩
  change decode (read64 _ 320)=_ at value
  rw [value]
  simp only [Bool.false_eq_true,false_and,ite_false,numerical,same]
  change decode (read64 CellAssemblyWitness.memory 224)-(8 : Float)=(-7 : Float)
  decide +kernel

end PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks
