import PoissonPTX.NativeFlowAccessOrder

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
open Ptx

/-- Split at the particular event occurrence, preserving its index even when
another occurrence has the same record. -/
theorem event_prefix (run : Runs cfg ctx program start events indices final)
    (observed : events[index]?=some event) :
    ∃ before earlier earlierIndices selected out suffix suffixIndices localIndex,
      Runs cfg ctx program start earlier earlierIndices before ∧ Step cfg ctx program selected before out ∧
      out.events[localIndex]?=some event ∧ Runs cfg ctx program out.state suffix suffixIndices final ∧
      events=earlier++out.events++suffix ∧ index=earlier.length+localIndex := by
  induction run generalizing index with
  | nil => simp at observed
  | @cons thread s out rest indices final step tail ih =>
    by_cases now : index<out.events.length
    · have atNow : out.events[index]?=some event := by
        simpa [List.getElem?_append,now] using observed
      exact ⟨s,[],[],thread,out,rest,indices,index,Runs.nil,step,atNow,tail,rfl,by simp⟩
    · have atLater : rest[index-out.events.length]?=some event := by
        simpa [List.getElem?_append,now] using observed
      obtain ⟨before,earlier,earlierIndices,selected,next,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi⟩ := ih atLater
      refine ⟨before,out.events++earlier,out.indices++earlierIndices,selected,next,suffix,suffixIndices,j,Runs.cons step hp,hs,hm,ht,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp only [List.length_append]; omega

/-- Arrival records use the selected thread's actual instruction position. -/
theorem step_arrival_origin (h : Step cfg ctx program selected s out)
    (member : Event.barrier (.arrival key thread) ∈ out.events) :
    thread=selected ∧ key.site=(s.core.lanes thread).pc := by
  cases h with
  | flow running fresh fetch effect => cases ‹Option Access› <;> simp at member
  | @sync _ resource running fresh fetch =>
    unfold synchronize at member
    generalize hc : barrierConfig cfg s.core selected=c at member
    generalize hr : barrierRequest cfg s.core selected resource=r at member
    by_cases same : r.key=Barrier.key c s.core.barrier
    · have notOld : ¬s.core.barrier.arrived r.thread=true := by simp [← hr,barrierRequest,fresh]
      by_cases complete : Barrier.Complete (Barrier.mark s.core.barrier r.thread)
      all_goals simp [Barrier.step,same,notOld,complete] at member
      all_goals obtain ⟨rfl,rfl⟩ := member
      all_goals simp [← same,← hr,barrierRequest]
    · simp [Barrier.step,same] at member


end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
