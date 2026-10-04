import PoissonPTX.DotPublicationSyntax
import PoissonPTX.NativeFlowPrefixTrack

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def PublicationLink (owner : Fin n) (s : NativeFlow.State n) (shadow : Flow.State) : Prop :=
  20≤(NativeFlow.lane s owner).core.pc → (NativeFlow.lane s owner).core.pc≤22 →
    ∀ r, r≠1 → r≠2 → (NativeFlow.lane s owner).core.regs r=shadow.core.regs r

theorem publication_track_step
    (actual : NativeFlow.Step cfg ctx (program count left right output scratch) selected s out)
    (aligned : Aligned s.core) (link : PublicationLink owner s shadow) :
    PublicationLink owner out.state
      (if owner=selected ∧ (s.core.lanes owner).pc<20 then NativeFlow.lane out.state owner else shadow) := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch effect =>
    by_cases same : owner=selected
    · subst owner
      by_cases before : (s.core.lanes selected).pc<20
      · simp [before,PublicationLink]
      · simp only [before,and_false,↓reduceIte]
        unfold PublicationLink
        rw [NativeFlow.lane_update_self]
        intro after upper r notOffset notAddress
        have oldLower : 20≤(s.core.lanes selected).pc := by omega
        have oldUpper : (s.core.lanes selected).pc≤22 := by
          by_contra outside
          have past := NativeFlow.eval_lower effect (cut:=23) (by change 23≤(s.core.lanes selected).pc; omega)
            (outside_publication_targets oldLower fetch)
          omega
        exact (NativeFlow.eval_keeps effect (publication_keeps oldLower oldUpper fetch notOffset notAddress)).trans
          (link oldLower oldUpper r notOffset notAddress)
    · simp only [same,false_and,↓reduceIte]
      unfold PublicationLink
      rw [NativeFlow.lane_update_other _ _ _ same]
      exact link
  | @sync _ resource running fresh fetch =>
    have selectedAfter : ¬(s.core.lanes selected).pc<20 := by
      intro before
      exact no_early_sync (by omega) fetch
    have nextShadow : (if owner=selected ∧ (s.core.lanes owner).pc<20
        then NativeFlow.lane {s with core:=(synchronize cfg s.core selected resource).state} owner else shadow)=shadow := by
      by_cases same : owner=selected <;> simp [same,selectedAfter]
    rw [nextShadow]
    by_cases early : (s.core.lanes owner).pc≤22
    · have blocked : (Ptx.Barrier.step (barrierConfig cfg s.core selected) s.core.barrier
          (barrierRequest cfg s.core selected resource)).disposition≠.released := by
        intro released
        have same := release_aligned cfg s.core selected resource aligned released owner
        apply no_early_sync early (resource:=resource)
        simpa only [same] using fetch
      simp only [synchronize]
      split <;> try exact link
      exact False.elim (blocked (by assumption))
    · have increase := NativeFlow.sync_monotone s cfg selected owner resource
      intro _ upper
      change ((synchronize cfg s.core selected resource).state.lanes owner).pc≤22 at upper
      omega

/-- At the first shared store, the saved input accumulator is the actual
store operand, not merely the result of another possible local execution. -/
theorem publication_input
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) s events indices t)
    (aligned : Aligned s.core) (entry : (s.core.lanes owner).pc=0)
    (atStore : (t.core.lanes owner).pc=22) :
    ∃ next words localIndices,
      Flow.Observed.Runs (ctx owner) (DotInput.inputProgram count left right scratch)
        (NativeFlow.lane s owner) words localIndices next ∧ next.core.pc=20 ∧
      (∀ r, r≠1 → r≠2 → (t.core.lanes owner).regs r=next.core.regs r) ∧
      (∀ a∈words, Event.data owner a∈events) := by
  obtain ⟨next,words,localIndices,observed,related,linked,wordMem,_⟩ :=
    NativeFlow.prefix_track (P:=PublicationLink owner) input_region run aligned
      (NativeFlow.related_initial (NativeFlow.lane s owner) (by simp [NativeFlow.lane,entry]))
      (by simp [PublicationLink,NativeFlow.lane,entry])
      (by
        intro selected before out shadow one consistent _ preserved
        simpa only [DotInput.input_length] using publication_track_step one consistent preserved)
  have done : next.core.pc=20 := by
    simpa [NativeFlow.Related,NativeFlow.lane,DotInput.input_length,atStore] using related
  exact ⟨next,words,localIndices,observed,done,linked (by simp [NativeFlow.lane,atStore])
    (by simp [NativeFlow.lane,atStore]),wordMem⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
