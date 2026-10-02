import PoissonPTX.CellWhole

namespace PtxTorchLean.Poisson.PTX.CellWhole

/-- Recover the local counter view at the actual first release. -/
theorem ready_view (pcs : ∀ u, (ready.core.lanes u).pc=21) (site : ready.core.site=none)
    (running : ∀ u, ready.halted u=false) :
    ready=Relocate.tailState 21 (CellEntry.continuation (entry ready)) := by
  have lanes : (fun u => Relocate.scalar 21 {ready.core.lanes u with pc:=(ready.core.lanes u).pc-21})=
      ready.core.lanes := by
    funext u
    change {ready.core.lanes u with pc:=((ready.core.lanes u).pc-21)+21}=ready.core.lanes u
    rw [Nat.sub_add_cancel (by rw [pcs])]
  have halt : ready.halted=fun _ => false := funext running
  cases ready with
  | mk core predicate halted =>
    cases core
    simp_all [Relocate.tailState,CellEntry.continuation,CellEntry.resume,entry,Relocate.core]

/-- Once all lanes are in the relocated body, no prefix instruction can be
fetched. Invert every actual body step and retain its exact event stream. -/
theorem body_run (run : Runs cfg bases cell width cells source output ctx start events indices final)
    (view : start=Relocate.tailState 21 localStart) :
    ∃ localEvents localFinal, events=localEvents.map (Relocate.event 21) ∧ indices=[] ∧
      final=Relocate.tailState 21 localFinal ∧
      Concurrent.WithTail.Runs cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
        (CellFinal.tail width output) localStart localEvents localFinal := by
  induction run generalizing localStart with
  | nil => exact ⟨[],localStart,rfl,rfl,view,.nil⟩
  | @cons selected s out rest indexRest final one tail ih =>
    cases one with
    | entry _ one =>
      obtain ⟨fresh,i,fetch,dispatch⟩ := one
      have bound := (List.getElem?_eq_some_iff.mp fetch).1
      rw [CellEntry.program_length] at bound
      change (s.core.lanes selected).pc<21 at bound
      rw [view] at bound
      change (localStart.core.lanes selected).pc+21<21 at bound
      omega
    | body one =>
      obtain ⟨localOut,outEq,localStep⟩ := Concurrent.AtOffset.step_back (view ▸ one)
      obtain ⟨localEvents,localFinal,eventsEq,indicesEq,finalEq,localRun⟩ :=
        ih (localStart:=localOut.state) (by rw [outEq]; rfl)
      exact ⟨localOut.events++localEvents,localFinal,
        by simp [outEq,eventsEq,Relocate.tailOutcome,List.map_append],
        by simpa using indicesEq,finalEq,.cons localStep localRun⟩

/-- Both modular executions, their common boundary and their event relation
are extracted from one whole-entry execution. -/
theorem executions (run : Runs cfg bases cell width cells source output ctx start events indices final)
    (aligned : Concurrent.Aligned start.core) (pcs : ∀ u, (start.core.lanes u).pc=0)
    (running : ∀ u, start.halted u=false) (thread : Fin 32)
    (finished : 20<(final.core.lanes thread).pc) :
    ∃ before after ready localFinal,
      events=before++after.map (Relocate.event 21) ∧
      CellEntry.Runs cfg (CellPrologue.threadContext bases cell) (CellEntry.program width cells source)
        (entry start) before indices (entry ready) ∧
      (∀ u, (ready.core.lanes u).pc=21) ∧ ready.core.site=none ∧
      final=Relocate.tailState 21 localFinal ∧
      Concurrent.WithTail.Runs cfg ctx (Concurrent.CellConsumer.WithOutput.front width)
        (CellFinal.tail width output) (CellEntry.continuation (entry ready)) after localFinal := by
  obtain ⟨before,later,firstIndices,laterIndices,ready,eventEq,indexEq,first,readyPC,site,readyRunning,last⟩ :=
    split run aligned (fun u => by rw [pcs]; omega) running thread finished
  obtain ⟨after,localFinal,afterEq,noIndices,finalEq,body⟩ :=
    body_run last (ready_view readyPC site readyRunning)
  have indexSame : indices=firstIndices := by simp [noIndices] at indexEq; exact indexEq
  subst firstIndices
  exact ⟨before,after,ready,localFinal,by rw [eventEq,afterEq],first,readyPC,site,finalEq,body⟩

end PtxTorchLean.Poisson.PTX.CellWhole
