import PoissonPTX.HostCellGather
import PoissonPTX.CellGridLiftSources
import PoissonPTX.CellGridPublication

namespace PtxTorchLean.Poisson.PTX.Host
open Concurrent

/-- Complete cell-grid execution over one common global allocation and
block-private shared storage. Both word and connectivity sources refer to
actual occurrences; completion includes all real tail returns. -/
def CellLaunch (a : Layout n e w) (kind : CellEntryKind) (memory output : Memory) : Prop :=
  ∃ (regs : Fin e → Fin 32 → Registers), ∃ final events indices source indexSource,
    CellGrid.Runs (a.cellLaunch kind)
      (fun block => CellWhole.begin (a.cellStart memory (regs block))) events indices final ∧
    (∀ block t, (final block).halted t=true) ∧
    (∀ block t, ((final block).core.lanes t).pc=21+(CellConsumer.WithOutput.front w).length+6) ∧
    CellGrid.Compatible memory (fun _ _ => 0) events source ∧
    CellGrid.IndexCompatible memory events indices indexSource ∧
    CellGrid.Performed events source ∧
    output=CellGrid.publish memory events

theorem Layout.cell_indices (a : Layout n e w) (block : Fin e) (thread : Fin 32) :
    (BitVec.ofNat 32 block.val).toNat*(w*w)+thread.val<2^32 := by
  rw [a.cell_index block]
  have prod := Nat.mul_le_mul_right (w*w) (Nat.le_of_lt block.isLt)
  have small := a.localSmall
  rw [Nat.mul_assoc e w w] at small
  have := thread.isLt
  omega

/-- A local cell witness is constructed without a supplied tensor result or
coefficient values. Its loads use the actual input and coefficient bytes. -/
theorem cell_local_exists (a : Layout n e w) (kind : CellEntryKind) (memory : Memory)
    (tables : a.Coefficients) (connected : a.Connectivity memory) (block : Fin e) :
    ∃ final events indices,
      CellWhole.Runs (CellGrid.config block) a.cellBases (BitVec.ofNat 32 block.val) w
        (a.offset .cells) (a.offset kind.source) (a.offset .element) (a.cellContext block)
        (CellWhole.begin (a.cellStart memory (fun _ _ => 0))) events indices final ∧
      ByteHistory.Recorded (fun space => match space with | .global => memory | .shared => fun _ => 0) events ∧
      CellEntry.Indices memory indices ∧
      (∀ t, final.halted t=true) ∧
      (∀ t, (final.core.lanes t).pc=21+(CellConsumer.WithOutput.front w).length+6) := by
  obtain ⟨final,events,indices,run,recorded,indexWords,done,pcs,_,_⟩ :=
    CellWhole.exists_recorded (CellGrid.config block) (a.cellContext block) (a.cellStart memory (fun _ _ => 0))
      (fun space => match space with | .global => memory | .shared => fun _ => 0) a.lo a.hi
      (fun _ => rfl) rfl rfl (fun _ => rfl) (a.cell_physical tables memory (fun _ _ => 0))
      (by
        intro t active
        apply CellGather.valid_of_layout (a.gatherLayout kind memory connected (fun _ _ => 0) block t _)
        simpa only [CellEntry.context_lane] using active)
      (a.aligned .element) (a.cell_indices block)
      (fun t active => (a.cell_output block t active).2)
  exact ⟨final,events,indices,run,recorded,indexWords,done,pcs⟩

/-- All cells have one finite source-admitted grid execution. The serial block
schedule witnesses existence only; the launch relation permits arbitrary
interleavings and source assignments meeting its explicit constraints. -/
theorem cell_exists (a : Layout n e w) (kind : CellEntryKind) (memory : Memory)
    (tables : a.Coefficients) (connected : a.Connectivity memory) :
    ∃ output, CellLaunch a kind memory output := by
  classical
  choose final events indices runs recorded indexWords done pcs using cell_local_exists a kind memory tables connected
  have localRuns : ∀ block, CellWhole.Runs (CellGrid.config block) ((a.cellLaunch kind).bases block)
      (BitVec.ofNat 32 block.val) (a.cellLaunch kind).width (a.cellLaunch kind).cells (a.cellLaunch kind).source
      (a.cellLaunch kind).output ((a.cellLaunch kind).context block)
      (CellWhole.begin (a.cellStart memory (fun _ _ => 0))) (events block) (indices block) (final block) := runs
  obtain ⟨words,indexes,actual,projected,indexProjected⟩ := CellGrid.serial_exists
    (fun _ => CellWhole.begin (a.cellStart memory (fun _ _ => 0))) final events indices localRuns
  have sources := fun block => CellWhole.recorded_sources (recorded block) (indexWords block)
  let ws := fun block r k => CellGrid.liftSource block (ByteHistory.sources (events block) r k)
  let ix : CellGrid.IndexChoices e := fun _ _ _ => .initial
  have compatible : CellGrid.Compatible memory (fun _ _ => 0) words ws :=
    CellGrid.compatible_lift (fun block => ByteHistory.sources (events block)) projected (fun _ => rfl)
      (fun block => (sources block).1)
  have indexCompatible : CellGrid.IndexCompatible memory words indexes ix := by
    apply CellGrid.index_compatible_lift (fun _ _ _ => .initial) projected indexProjected
    intro block
    exact (sources block).2.2
  have performed : CellGrid.Performed words ws :=
    CellGrid.performed_lift (fun block => ByteHistory.sources (events block)) projected (fun block => (sources block).2.1)
  exact ⟨_,(fun _ _ _ => 0),final,words,indexes,ws,ix,actual,done,pcs,compatible,indexCompatible,performed,rfl⟩

end PtxTorchLean.Poisson.PTX.Host
