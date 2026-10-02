import PoissonPTX.CellWholeCut
import PoissonPTX.RelabelShift

namespace PtxTorchLean.Poisson.PTX.CellWhole
variable {before after : List (Concurrent.Event 32)}

/-- The history change used by the arithmetic proof is derived from actual
barrier generations, rather than assuming that renamed sites match. -/
theorem histories
    (first : CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      (entry start) before indices (entry ready))
    (aligned : Concurrent.Aligned start.core) (pcs : ∀ u, (start.core.lanes u).pc=0)
    (done : ∀ u, (ready.core.lanes u).pc=21)
    (body : Concurrent.WithTail.Runs cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (CellEntry.continuation (entry ready)) after localFinal) :
    ∃ renameKey, Concurrent.Relabel.Related renameKey (before++after) (before++after.map (Relocate.event 21)) := by
  obtain ⟨allPC,site,generation,key,reset,rest⟩ := CellEntry.completed_barrier first aligned
    (fun u => by change (start.core.lanes u).pc≤20; rw [pcs]; omega) (0 : Fin 32)
    (by change 20<(ready.core.lanes (0 : Fin 32)).pc; rw [done]; decide)
  have prefixClock := CellEntry.clock_run first
  rw [reset] at prefixClock
  have bodyClock := Concurrent.WithTail.clock_run body
  have bodyReset : (CellEntry.continuation (entry ready)).core.barrier=Ptx.Barrier.reset (generation+1) := reset
  rw [bodyReset] at bodyClock
  exact ⟨_,Concurrent.Relabel.joined prefixClock bodyClock⟩

/-- One physical-history source assignment is sufficient for the local proof. -/
theorem sources
    (first : CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
      (entry start) before indices (entry ready))
    (aligned : Concurrent.Aligned start.core) (pcs : ∀ u, (start.core.lanes u).pc=0)
    (done : ∀ u, (ready.core.lanes u).pc=21)
    (body : Concurrent.WithTail.Runs cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
      (CellFinal.tail width output) (CellEntry.continuation (entry ready)) after localFinal)
    (words : Concurrent.Visibility.Compatible memory (before++after.map (Relocate.event 21)) wordChoices)
    (performed : Concurrent.Visibility.Performed (before++after.map (Relocate.event 21)) wordChoices)
    (indexes : IndexSources.Compatible (memory .global) (before++after.map (Relocate.event 21)) indices indexChoices) :
    Concurrent.Visibility.Compatible memory (before++after) wordChoices ∧
    Concurrent.Visibility.Performed (before++after) wordChoices ∧
    IndexSources.Compatible (memory .global) (before++after) indices indexChoices := by
  obtain ⟨renameKey,related⟩ := histories first aligned pcs done body
  exact ⟨Concurrent.Relabel.compatible related words,Concurrent.Relabel.performed related performed,
    Concurrent.Relabel.indices related indexes⟩

end PtxTorchLean.Poisson.PTX.CellWhole

namespace PtxTorchLean.Poisson.PTX.Concurrent.Relabel
variable {n : Nat} {old new : List (Event n)}

theorem published (related : Related renameKey old new) :
    GlobalPublication.publish memory old=GlobalPublication.publish memory new := by
  induction related generalizing memory with
  | nil => rfl
  | cons one rest ih =>
    cases one <;> simp only [GlobalPublication.publish,GlobalPublication.applyEvent] <;> apply ih

end PtxTorchLean.Poisson.PTX.Concurrent.Relabel

namespace PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication
variable {n : Nat} {events : List (Event n)} {memory : Memory}

theorem append (first second : List (Event n)) (memory : Memory) :
    publish memory (first++second)=publish (publish memory first) second := by
  induction first generalizing memory with
  | nil => rfl
  | cons e rest ih => exact ih (applyEvent memory e)

theorem no_stores (none : ∀ owner access, Event.data owner access∈events →
    access.data.store=true → access.space≠.global) : publish memory events=memory := by
  induction events generalizing memory with
  | nil => rfl
  | cons e rest ih =>
    rw [publish,ih (fun owner access member => none owner access (List.mem_cons_of_mem _ member))]
    cases e with
    | barrier => rfl
    | data owner access =>
      simp only [applyEvent]
      split
      · rename_i writes; exact False.elim (none owner access (by simp) writes.2 writes.1)
      · rfl

end PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication
