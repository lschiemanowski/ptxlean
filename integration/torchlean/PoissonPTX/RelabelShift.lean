import PoissonPTX.RelabelHistory
import PoissonPTX.Relocate
import PoissonPTX.ExecutionClock

namespace PtxTorchLean.Poisson.PTX.Concurrent.Relabel

/-- The prefix keeps its sites; subsequent barrier generations use relocated
sites. The cut is determined by the actual first-barrier reset. -/
def renameAfter (cut offset : Nat) (key : Ptx.Barrier.Key) : Ptx.Barrier.Key :=
  if cut≤key.generation then Relocate.key offset key else key

variable {n : Nat} {e : Event n} {events before after : List (Event n)}

theorem before_event (bound : ∀ b, e=.barrier b → Clock.generation b<cut) :
    EventRelated (renameAfter cut offset) e e := by
  cases e with
  | data thread access => cases access with | mk space data => cases data; exact .data
  | barrier b =>
    have early := bound b rfl
    cases b with
    | arrival key thread =>
      change key.generation<cut at early
      simpa [renameAfter,Nat.not_le.mpr early] using
        (EventRelated.arrival (renameKey:=renameAfter cut offset) (key:=key) (thread:=thread))
    | completion key =>
      change key.generation<cut at early
      simpa [renameAfter,Nat.not_le.mpr early] using
        (EventRelated.completion (renameKey:=renameAfter cut offset) (key:=key))

theorem after_event (bound : ∀ b, e=.barrier b → cut≤Clock.generation b) :
    EventRelated (renameAfter cut offset) e (Relocate.event offset e) := by
  cases e with
  | data thread access => cases access with | mk space data => cases data; exact .data
  | barrier b =>
    have late := bound b rfl
    cases b with
    | arrival key thread =>
      change cut≤key.generation at late
      simpa [renameAfter,late,Relocate.event,Relocate.barrierEvent] using
        (EventRelated.arrival (renameKey:=renameAfter cut offset) (key:=key) (thread:=thread))
    | completion key =>
      change cut≤key.generation at late
      simpa [renameAfter,late,Relocate.event,Relocate.barrierEvent] using
        (EventRelated.completion (renameKey:=renameAfter cut offset) (key:=key))

theorem before_history (bound : ∀ b, Event.barrier b∈events → Clock.generation b<cut) :
    Related (renameAfter cut offset) events events := by
  induction events with
  | nil => exact .nil
  | cons e rest ih =>
    exact .cons (before_event (fun b same => bound b (by simp [same])))
      (ih (fun b member => bound b (by simp [member])))

theorem after_history (bound : ∀ b, Event.barrier b∈events → cut≤Clock.generation b) :
    Related (renameAfter cut offset) events (events.map (Relocate.event offset)) := by
  induction events with
  | nil => exact .nil
  | cons e rest ih =>
    exact .cons (after_event (fun b same => bound b (by simp [same])))
      (ih (fun b member => bound b (by simp [member])))

/-- A real completed generation separates old prefix sites from body sites.
Only labels change; byte sources retain exactly the same event positions. -/
theorem joined (first : Clock.Progress initial (Ptx.Barrier.reset cut) before)
    (second : Clock.Progress (Ptx.Barrier.reset cut) final after) :
    Related (renameAfter cut offset) (before++after) (before++after.map (Relocate.event offset)) := by
  apply List.rel_append
  · exact before_history (fun b member => Clock.before_reset (first.emitted b member).2)
  · exact after_history (fun b member => (second.emitted b member).1)

end PtxTorchLean.Poisson.PTX.Concurrent.Relabel
