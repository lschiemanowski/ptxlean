import PoissonPTX.NativeFlowOrigins

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- An observed access has a genuine preceding run, whose entire memory
history embeds in the same complete history used for source admission. -/
theorem access_decompose (run : Runs cfg ctx program start events indices final)
    (member : Event.data owner access∈events) :
    ∃ before earlier earlierIndices selected out suffix,
      Runs cfg ctx program start earlier earlierIndices before ∧
      Step cfg ctx program selected before out ∧ Event.data owner access∈out.events ∧
      events=earlier++out.events++suffix := by
  induction run with
  | nil => simp at member
  | @cons selected s out rest indices final step tail ih =>
    rcases List.mem_append.mp member with now | later
    · exact ⟨s,[],[],selected,out,rest,.nil,step,now,rfl⟩
    · obtain ⟨before,earlier,earlierIndices,thread,next,suffix,earlierRun,one,found,same⟩ := ih later
      exact ⟨before,out.events++earlier,out.indices++earlierIndices,thread,next,suffix,
        .cons step earlierRun,one,found,by simp [same,List.append_assoc]⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
