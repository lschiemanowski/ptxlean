import PoissonPTX.CellEntryStores

namespace PtxTorchLean.Poisson.PTX.CellEntry
open Ptx
variable {n : Nat} {s t : State n} {out : Outcome n} {cfg : Concurrent.Config n}
  {ctx : Fin n → CellPrologue.Context}

/-- Reuse the barrier-history proof of the arithmetic machine. Index loads
emit no barrier records and do not change the waiting set. -/
theorem step_history (step : Step cfg ctx code thread s out)
    (aligned : Concurrent.Aligned s.core)
    (origin : Concurrent.History.WaitingOrigin cfg s.core before) :
    Concurrent.History.WaitingOrigin cfg out.state.core (before++out.events) ∧
    Concurrent.History.FreshCompletions before out.events := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => exact Concurrent.History.ordinary_history ⟨_,[]⟩ origin rfl rfl (by intro key; simp)
  | gather =>
    apply Concurrent.History.ordinary_history ⟨_,_⟩ origin rfl rfl
    intro key
    cases ‹Option Concurrent.Access› <;> simp
  | skip => exact Concurrent.History.ordinary_history ⟨_,[]⟩ origin rfl rfl (by intro key; simp)
  | sync => exact Concurrent.History.synchronize_history _ _ _ _ _ aligned origin

theorem runs_history (run : Runs cfg ctx code s events indices t)
    (aligned : Concurrent.Aligned s.core)
    (origin : Concurrent.History.WaitingOrigin cfg s.core before)
    (complete : Concurrent.History.CompleteOrigins before) :
    Concurrent.History.WaitingOrigin cfg t.core (before++events) ∧
    Concurrent.History.CompleteOrigins (before++events) := by
  induction run generalizing before with
  | nil => simpa using And.intro origin complete
  | cons step _ ih =>
    obtain ⟨next,new⟩ := step_history step aligned origin
    simpa only [List.append_assoc] using
      ih (step_aligned step aligned) next (Concurrent.History.append_complete complete new)

/-- From reset, every participant has an actual earlier arrival at completion. -/
theorem completed_arrivals (run : Runs cfg ctx code s events indices t)
    (reset : s.core.barrier=Barrier.reset generation) : Concurrent.History.CompleteOrigins events := by
  have aligned : Concurrent.Aligned s.core := by intro u h; simp [reset,Barrier.reset] at h
  have origin : Concurrent.History.WaitingOrigin cfg s.core [] := by intro u h; simp [reset,Barrier.reset] at h
  have complete : Concurrent.History.CompleteOrigins ([] : List (Concurrent.Event n)) := by
    intro c key h; simp at h
  simpa using (runs_history run aligned origin complete).2

/-- Split at an indexed event occurrence, preserving both record streams. -/
theorem run_event_prefix (run : Runs cfg ctx code s events indices t)
    (observed : events[index]?=some event) :
    ∃ before earlier earlierIndices selected out suffix suffixIndices localIndex,
      Runs cfg ctx code s earlier earlierIndices before ∧ Step cfg ctx code selected before out ∧
      out.events[localIndex]?=some event ∧ Runs cfg ctx code out.state suffix suffixIndices t ∧
      events=earlier++out.events++suffix ∧ indices=earlierIndices++out.indices++suffixIndices ∧
      index=earlier.length+localIndex := by
  induction run generalizing index with
  | nil => simp at observed
  | @cons thread s out rest indices final step tail ih =>
    by_cases now : index<out.events.length
    · have atNow : out.events[index]?=some event := by
        simpa [List.getElem?_append,now] using observed
      exact ⟨s,[],[],thread,out,rest,indices,index,.nil,step,atNow,tail,rfl,rfl,by simp⟩
    · have atLater : rest[index-out.events.length]?=some event := by
        simpa [List.getElem?_append,now] using observed
      obtain ⟨before,earlier,earlierIndices,selected,next,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi,hj⟩ := ih atLater
      refine ⟨before,out.events++earlier,out.indices++earlierIndices,selected,next,suffix,suffixIndices,j,
        .cons step hp,hs,hm,ht,?_,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp [hi,List.append_assoc]
      · simp only [List.length_append]; omega

/-- An arrival occurs at the actual fetched barrier and emits no data record. -/
theorem arrival_origin (step : Step cfg ctx (program width cells source) selected s out)
    (member : Concurrent.Event.barrier (.arrival key owner)∈out.events) :
    owner=selected ∧ (s.core.lanes owner).pc=20 ∧ key.site=20 ∧
    (∀ writer access, Concurrent.Event.data writer access∉out.events) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  cases dispatch with
  | setup => simp at member
  | skip => simp at member
  | gather => cases ‹Option Concurrent.Access› <;> simp at member
  | sync =>
    have syncStep : Concurrent.Step cfg (List.replicate ((s.core.lanes selected).pc+1) (.sync 0)) selected s.core
        (Concurrent.synchronize cfg s.core selected 0) :=
      ⟨fresh,.sync 0,by simp,Concurrent.Dispatch.sync⟩
    obtain ⟨same,site⟩ := Concurrent.step_arrival_origin syncStep member
    subst owner
    have bound := (List.getElem?_eq_some_iff.mp fetch).1
    rw [program_length] at bound
    have pc : (s.core.lanes selected).pc=20 := by
      have h := fetch
      generalize (s.core.lanes selected).pc=j at h bound
      interval_cases j <;> simp_all [program,CellPrologue.program,CellGather.code]
    refine ⟨rfl,pc,site.trans pc,?_⟩
    intro writer access
    simp only [synchronize,Concurrent.synchronize]
    split <;> simp

/-- A lane at its barrier cannot emit any more stores in this prefix. -/
theorem no_store_after (run : Runs cfg ctx (program width cells source) s events indices t)
    (past : 20≤(s.core.lanes owner).pc)
    (member : Concurrent.Event.data owner access∈events) (store : access.data.store=true) : False := by
  induction run with
  | nil => simp at member
  | cons step tail ih =>
    rcases List.mem_append.mp member with first | later
    · have pc := (store_origin step first store).2.1
      omega
    · exact ih (step_after_store step owner past).1 later

/-- Actual store/arrival ordering follows from control, independent of values. -/
theorem store_before_arrival {w a : Nat} {owner : Fin n} {access : Concurrent.Access} (run : Runs cfg ctx (program width cells source) s events indices t)
    (write : events[w]?=some (.data owner access)) (store : access.data.store=true)
    (arrival : events[a]?=some (.barrier (.arrival key owner))) : w<a := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi,hj⟩ :=
    run_event_prefix run arrival
  obtain ⟨same,pc,site,noData⟩ := arrival_origin hs (List.mem_of_getElem? hm)
  have nextPC := (step_after_store hs owner (by omega)).1
  by_contra notEarlier
  have noEarly : ¬w<earlier.length := by omega
  rw [he] at write
  simp only [List.getElem?_append,List.length_append] at write
  by_cases during : w<earlier.length+out.events.length
  · have atStep : out.events[w-earlier.length]?=some (.data owner access) := by
      simpa [List.length_append,during,noEarly] using write
    exact noData owner access (List.mem_of_getElem? atStep)
  · have atTail : suffix[w-(earlier++out.events).length]?=some (.data owner access) := by
      simpa [List.length_append,during,noEarly] using write
    exact no_store_after ht nextPC (List.mem_of_getElem? atTail) store

/-- Every actual gather store lies before the writer's actual arrival and the
observed completion. The phase key and arrival are recovered from the run. -/
theorem store_before_completion {w c : Nat} {owner : Fin n} {access : Concurrent.Access}
    (run : Runs cfg ctx (program width cells source) s events indices t)
    (reset : s.core.barrier=Barrier.reset generation)
    (write : events[w]?=some (.data owner access)) (store : access.data.store=true)
    (completion : events[c]?=some (.barrier (.completion key))) :
    ∃ a, events[a]?=some (.barrier (.arrival key owner)) ∧ w<a ∧ a<c := by
  obtain ⟨a,before,observed⟩ := completed_arrivals run reset c key completion owner
  exact ⟨a,observed,store_before_arrival run write store observed,before⟩

end PtxTorchLean.Poisson.PTX.CellEntry
