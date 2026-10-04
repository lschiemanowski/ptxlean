import PoissonPTX.ByteHistoryReads
import PoissonPTX.Relocate

namespace PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory

/-- Moving instruction numbers changes neither the recorded data bytes nor
the byte publication used to construct a finite execution witness. -/
theorem apply_relocate (memory : Space → Memory) (e : Event n) :
    applyEvent memory (Relocate.event offset e)=applyEvent memory e := by
  cases e <;> rfl

theorem publish_relocate (memory : Space → Memory) (events : List (Event n)) :
    publish memory (events.map (Relocate.event offset))=publish memory events := by
  induction events generalizing memory with
  | nil => rfl
  | cons e rest ih => simpa only [List.map_cons,publish,apply_relocate] using ih (applyEvent memory e)

theorem recorded_relocate (recorded : Recorded memory events) :
    Recorded memory (events.map (Relocate.event offset)) := by
  induction recorded with
  | nil => exact .nil
  | @cons memory e rest first later ih =>
    refine .cons ?_ ?_
    · cases e <;> exact first
    · simpa only [apply_relocate] using ih

end PtxTorchLean.Poisson.PTX.Concurrent.ByteHistory
