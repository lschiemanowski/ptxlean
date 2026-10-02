import PoissonPTX.CellGridCandidates
import PoissonPTX.CellGridSchedule
import PoissonPTX.CellGridLiftSources

namespace PtxTorchLean.Poisson.PTX.CellGrid
variable {o : Operator} {values : Array Float}

/-- The uniform entry arguments and per-block contexts for a supplied family. -/
def familyLaunch (family : CellWhole.Family o values) (cells source : Word) : Launch o.mesh.cells.size :=
  ⟨o.nodes.size,fun block => (family.execution block).bases,cells,source,family.output,
    fun block => (family.execution block).bodyContext⟩

theorem family_config (family : CellWhole.Family o values) (block : Fin o.mesh.cells.size) :
    (family.execution block).cfg=config block := by
  have same := family.sameCTA block
  cases cfg : (family.execution block).cfg with
  | mk cta positive =>
    rw [cfg] at same
    change cta=block.val at same
    subst cta
    rfl

/-- From supplied actual cell runs and their source evidence, construct an
admitted grid. The same records, states and input layouts are retained. No grid
schedule, read value or output tensor is an additional premise. -/
theorem family_exists (family : CellWhole.Family o values) (cells source : Word)
    (sameCells : ∀ block, (family.execution block).cells=cells)
    (sameSource : ∀ block, (family.execution block).source=source) :
    ∃ grid : Admitted o values, grid.candidates=family.candidates := by
  let launch := familyLaunch family cells source
  have localRuns : ∀ block, CellWhole.Runs (config block) (launch.bases block) (BitVec.ofNat 32 block.val)
      launch.width launch.cells launch.source launch.output (launch.context block)
      (family.execution block).start (family.execution block).events (family.execution block).indices (family.execution block).final := by
    intro block
    have run := (family.execution block).run
    rw [family_config family block,sameCells,sameSource,family.sameOutput] at run
    exact run
  obtain ⟨events,indices,run,projected,indexProjected⟩ := serial_exists
    (fun block => (family.execution block).start) (fun block => (family.execution block).final)
    (fun block => (family.execution block).events) (fun block => (family.execution block).indices) localRuns
  let ws : Sources o.mesh.cells.size := fun block r k => liftSource block ((family.execution block).allSources r k)
  let ix : IndexChoices o.mesh.cells.size := fun block r k => liftSource block ((family.execution block).indexChoices r k)
  have words : Compatible family.memory (fun block => (family.execution block).memory .shared) events ws :=
    compatible_lift (fun block => (family.execution block).allSources) projected family.sameInitial
      (fun block => (family.execution block).joint)
  have indexes : IndexCompatible family.memory events indices ix := by
    apply index_compatible_lift (fun block => (family.execution block).indexChoices) projected indexProjected
    intro block
    have valid := (family.execution block).jointIndices
    rw [family.sameInitial] at valid
    exact valid
  have performed : Performed events ws :=
    performed_lift (fun block => (family.execution block).allSources) projected
      (fun block => (family.execution block).performed)
  exact ⟨{
    candidates := family.candidates
    launch := launch
    width := rfl
    configs := family_config family
    bases := fun _ => rfl
    cells := sameCells
    source := sameSource
    output := family.sameOutput
    contexts := fun _ => rfl
    events := events
    indices := indices
    run := run
    projected := projected
    indexProjected := indexProjected
    wordSource := ws
    indexSource := ix
    words := words
    indexes := indexes
    performed := performed },rfl⟩

end PtxTorchLean.Poisson.PTX.CellGrid
