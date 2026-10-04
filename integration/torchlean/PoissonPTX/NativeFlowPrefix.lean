import PoissonPTX.NativeFlowRegion

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context}
  {program : List Instr} {pre : List Flow.Instr} {s t : State n} {owner selected : Fin n}
  {shadow : Flow.State}

/-- Extract real prefix instructions for one thread while retaining their
actual observed words. Steps of other threads and later instructions stutter
in this projection; a barrier does not create an assumed input-phase boundary. -/
theorem prefix_step_exact (region : Region program pre)
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (related : Related pre.length (lane s owner) shadow) :
    ∃ next words indices, Flow.Observed.Runs (ctx owner) pre shadow words indices next ∧
      Related pre.length (lane out.state owner) next ∧
      (∀ a∈words, Event.data owner a∈out.events) ∧ (∀ a∈indices, (owner,a)∈out.indices) ∧
      next=(if owner=selected ∧ (s.core.lanes owner).pc<pre.length then lane out.state owner else shadow) := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch execution =>
    by_cases sameOwner : owner=selected
    · subst owner
      by_cases before : (s.core.lanes selected).pc<pre.length
      · have same : lane s selected=shadow := by simpa only [Related,lane,before,↓reduceIte] using related
        have localFetch : pre[(s.core.lanes selected).pc]?=some instruction := by
          rw [region.fetch _ before] at fetch
          obtain ⟨i,found,equal⟩ := Option.map_eq_some_iff.mp fetch
          cases equal
          exact found
        have one : Flow.Observed.Step (ctx selected) pre shadow next access index := by
          rw [← same]
          exact ⟨running,instruction,localFetch,execution⟩
        have upper := eval_upper execution before (region.inside _ _ before localFetch)
        refine ⟨next,access.toList,index.toList,?_,?_,?_,?_,?_⟩
        · simpa using Flow.Observed.Runs.cons one Flow.Observed.Runs.nil
        · rw [lane_update_self]; exact related_initial next upper
        · intro a member; exact List.mem_map.mpr ⟨a,member,rfl⟩
        · intro a member; exact List.mem_map.mpr ⟨a,member,rfl⟩
        · simp [before,lane_update_self]
      · have past : pre.length≤(s.core.lanes selected).pc := by omega
        have lower := eval_lower execution past (region.outside _ _ past fetch)
        refine ⟨shadow,[],[],.nil,?_,by simp,by simp,by simp [before]⟩
        rw [lane_update_self]
        simpa only [Related,lane,before,show ¬next.core.pc<pre.length by omega,↓reduceIte] using related
    · exact ⟨shadow,[],[],.nil,by simpa only [lane_update_other s selected owner sameOwner next] using related,
        by simp,by simp,by simp [sameOwner]⟩
  | @sync _ resource running fresh fetch =>
    have outside : ¬(s.core.lanes selected).pc<pre.length := by
      intro inside; exact no_prefix_sync region inside fetch
    refine ⟨shadow,[],[],.nil,?_,by simp,by simp,?_⟩
    swap
    · by_cases same : owner=selected <;> simp [same,outside]
    by_cases before : (s.core.lanes owner).pc<pre.length
    · rw [sync_prefix_unchanged region aligned before fetch]
      exact related
    · have increase := sync_monotone s cfg selected owner resource
      have after : ¬((synchronize cfg s.core selected resource).state.lanes owner).pc<pre.length := by omega
      simpa only [Related,lane,before,after,↓reduceIte] using related

theorem prefix_step (region : Region program pre)
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (related : Related pre.length (lane s owner) shadow) :
    ∃ next words indices, Flow.Observed.Runs (ctx owner) pre shadow words indices next ∧
      Related pre.length (lane out.state owner) next ∧
      (∀ a∈words, Event.data owner a∈out.events) ∧ (∀ a∈indices, (owner,a)∈out.indices) := by
  obtain ⟨next,words,indices,run,link,wordMem,indexMem,_⟩ := prefix_step_exact region actual aligned related
  exact ⟨next,words,indices,run,link,wordMem,indexMem⟩

/-- The local trace and its byte observations are recovered from the actual
interleaving. Membership links every retained observation back to that one
whole-kernel history, where source admission will be checked. -/
theorem prefix_run (region : Region program pre)
    (actual : Runs cfg ctx program s events indices t) (aligned : Aligned s.core)
    (related : Related pre.length (lane s owner) shadow) :
    ∃ next words localIndices, Flow.Observed.Runs (ctx owner) pre shadow words localIndices next ∧
      Related pre.length (lane t owner) next ∧
      (∀ a∈words, Event.data owner a∈events) ∧ (∀ a∈localIndices, (owner,a)∈indices) := by
  induction actual generalizing shadow with
  | nil => exact ⟨shadow,[],[],.nil,related,by simp,by simp⟩
  | cons one rest ih =>
    obtain ⟨middle,first,firstIndices,run,link,words,reads⟩ := prefix_step region one aligned related
    obtain ⟨final,later,laterIndices,tail,finalLink,laterWords,laterReads⟩ :=
      ih (step_aligned one aligned) link
    refine ⟨final,first++later,firstIndices++laterIndices,Flow.Observed.append run tail,finalLink,?_,?_⟩
    · intro a member
      rcases List.mem_append.mp member with early | late
      · exact List.mem_append_left _ (words a early)
      · exact List.mem_append_right _ (laterWords a late)
    · intro a member
      rcases List.mem_append.mp member with early | late
      · exact List.mem_append_left _ (reads a early)
      · exact List.mem_append_right _ (laterReads a late)

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
