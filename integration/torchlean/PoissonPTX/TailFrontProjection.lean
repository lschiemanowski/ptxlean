import PoissonPTX.ConcurrentTail
import PoissonPTX.ConcurrentOrder

namespace PtxTorchLean.Poisson.PTX.Concurrent.WithTail
open Ptx

/-- A release can only move lanes that are all at the selected live barrier.
Thus a lane already in its tail cannot be silently advanced by a projected sync. -/
theorem synchronize_related (related : Related cut tracked actual shadow)
    (before : (actual.lanes selected).pc<cut) (aligned : Aligned actual) :
    Related cut tracked (synchronize cfg actual selected resource).state
      (synchronize cfg shadow selected resource).state ∧
    (synchronize cfg actual selected resource).events=(synchronize cfg shadow selected resource).events := by
  have live := related_live related before
  have configEq : barrierConfig cfg actual selected=barrierConfig cfg shadow selected := by
    simp [barrierConfig,related.2.1,live]
  have requestEq : barrierRequest cfg actual selected resource=barrierRequest cfg shadow selected resource := by
    simp [barrierRequest,related.1,live]
  unfold synchronize
  rw [← configEq,← requestEq,← related.1]
  dsimp only
  generalize resultEq : Barrier.step (barrierConfig cfg actual selected) actual.barrier
    (barrierRequest cfg actual selected resource)=result
  cases disposition : result.disposition with
  | rejectedWrongKey => dsimp only; exact ⟨related,rfl⟩
  | waiting => dsimp only; exact ⟨⟨rfl,rfl,related.2.2⟩,rfl⟩
  | released =>
    dsimp only
    have allPC := release_aligned cfg actual selected resource aligned (by rw [resultEq,disposition])
    refine ⟨⟨rfl,rfl,?_⟩,rfl⟩
    intro t
    have low : (actual.lanes t).pc<cut := by rw [allPC t]; exact before
    have eq := related_live related low
    dsimp only
    split
    · exact congrArg PTX.advance eq
    · constructor
      · have pc := congrArg PTX.State.pc eq
        change (shadow.lanes t).pc+1=cut
        rename_i outside
        change ¬(actual.lanes t).pc+1<cut at outside
        omega
      · change (actual.lanes t).regs tracked=(shadow.lanes t).regs tracked
        rw [eq]

/-- Every concrete front step is a fetched step of the clipped arithmetic front.
The tail is not executed by this lemma, and no numerical result is a premise. -/
theorem front_step (step : Concurrent.Step cfg front selected actual out)
    (related : Related front.length tracked actual shadow) (aligned : Aligned actual) :
    ∃ projected, Concurrent.Step cfg (front.map (clip front.length)) selected shadow projected ∧
      Related front.length tracked out.state projected.state ∧ out.events=projected.events := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := step
  have before := (List.getElem?_eq_some_iff.mp fetch).1
  have live := related_live related before
  have fresh' : shadow.barrier.arrived selected=false := by rw [← related.1]; exact fresh
  have fetch' : (front.map (clip front.length))[(shadow.lanes selected).pc]?=some (clip front.length i) := by
    rw [← live,List.getElem?_map,fetch]; rfl
  cases dispatch with
  | data hd =>
    have hd' := hd
    rw [live] at hd'
    refine ⟨_,⟨fresh',_,fetch',Dispatch.data hd'⟩,?_,rfl⟩
    apply related_update related
    · have pc := data_pc hd
      exact (Nat.min_eq_left (by omega)).symm
    · rfl
    · intro _; rfl
  | @skip active target =>
    by_cases activeLane : selected.val<active
    · have dispatch' := Dispatch.skip (cfg:=cfg) (thread:=selected) (s:=shadow)
        (active:=active) (target:=min target front.length)
      refine ⟨_,⟨fresh',_,fetch',dispatch'⟩,?_,rfl⟩
      simp only [activeLane,ite_true]
      apply related_update related
      · have pc := congrArg PTX.State.pc live
        simp only
        rw [pc,Nat.min_eq_left (by omega)]
      · rw [live]
      · intro _; rw [live]
    · have dispatch' := Dispatch.skip (cfg:=cfg) (thread:=selected) (s:=shadow)
        (active:=active) (target:=min target front.length)
      refine ⟨_,⟨fresh',_,fetch',dispatch'⟩,?_,rfl⟩
      simp only [activeLane,ite_false]
      apply related_update related
      · rfl
      · rw [live]
      · intro low
        simp only at low
        rw [live,Nat.min_eq_left (by omega)]
  | sync =>
    obtain ⟨rel,events⟩ := synchronize_related related before aligned
    exact ⟨_,⟨fresh',_,fetch',Dispatch.sync⟩,rel,events⟩

end PtxTorchLean.Poisson.PTX.Concurrent.WithTail
