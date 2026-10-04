import PoissonPTX.NativeFlow

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

theorem step_access_origin (actual : Step cfg ctx program selected s out)
    (member : Event.data owner access∈out.events) :
    owner=selected ∧ ∃ i next index,
      program[(s.core.lanes selected).pc]?=some (.flow i) ∧
      Flow.Observed.Eval (ctx selected) i (lane s selected) next (some access) index := by
  cases actual with
  | @flow instruction _ next word index running fresh fetch execution =>
    obtain ⟨a,recorded,equal⟩ := List.mem_map.mp member
    cases equal
    have same : word=some access := by simpa using recorded
    exact ⟨rfl,instruction,next,index,fetch,same ▸ execution⟩
  | sync =>
    simp only [synchronize] at member
    split at member <;> simp_all

/-- Recover the executed prefix before any access in the whole history. -/
theorem access_prefix (run : Runs cfg ctx program start events indices final)
    (member : Event.data owner access∈events) :
    ∃ before earlier earlierIndices selected out,
      Runs cfg ctx program start earlier earlierIndices before ∧
      Step cfg ctx program selected before out ∧ Event.data owner access∈out.events := by
  induction run with
  | nil => simp at member
  | @cons selected s out rest indices final step tail ih =>
    rcases List.mem_append.mp member with now | later
    · exact ⟨s,[],[],selected,out,.nil,step,now⟩
    · obtain ⟨before,earlier,earlierIndices,thread,next,earlierRun,one,found⟩ := ih later
      exact ⟨before,out.events++earlier,out.indices++earlierIndices,thread,next,.cons step earlierRun,one,found⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
