import PoissonPTX.NativeFlowPrefix

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- Track an additional relation to the exact recovered prefix state. This
permits proving that selected registers survive until their later consumers,
without accepting a separate execution or an unrelated numerical snapshot. -/
theorem prefix_track {P : State n → Flow.State → Prop}
    (region : Region program pre)
    (actual : Runs cfg ctx program s events indices t) (aligned : Aligned s.core)
    (related : Related pre.length (lane s owner) shadow) (initial : P s shadow)
    (preserves : ∀ selected s out shadow, Step cfg ctx program selected s out →
      Aligned s.core → Related pre.length (lane s owner) shadow → P s shadow →
      P out.state (if owner=selected ∧ (s.core.lanes owner).pc<pre.length
        then lane out.state owner else shadow)) :
    ∃ next words localIndices,
      Flow.Observed.Runs (ctx owner) pre shadow words localIndices next ∧
      Related pre.length (lane t owner) next ∧ P t next ∧
      (∀ a∈words, Event.data owner a∈events) ∧ (∀ a∈localIndices, (owner,a)∈indices) := by
  induction actual generalizing shadow with
  | nil => exact ⟨shadow,[],[],.nil,related,initial,by simp,by simp⟩
  | @cons selected before out restWords restIndices final one rest ih =>
    obtain ⟨middle,first,firstIndices,run,link,words,reads,equal⟩ :=
      prefix_step_exact region one aligned related
    have nextP : P out.state middle := by rw [equal]; exact preserves _ _ _ _ one aligned related initial
    obtain ⟨final,later,laterIndices,tail,finalLink,finalP,laterWords,laterReads⟩ :=
      ih (step_aligned one aligned) link nextP
    refine ⟨final,first++later,firstIndices++laterIndices,Flow.Observed.append run tail,
      finalLink,finalP,?_,?_⟩
    · intro a member
      rcases List.mem_append.mp member with early | late
      · exact List.mem_append_left _ (words a early)
      · exact List.mem_append_right _ (laterWords a late)
    · intro a member
      rcases List.mem_append.mp member with early | late
      · exact List.mem_append_left _ (reads a early)
      · exact List.mem_append_right _ (laterReads a late)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
