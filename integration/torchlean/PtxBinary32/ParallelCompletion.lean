import PtxBinary32.ParallelControl

/-! Actual barrier completions separate earlier-site instructions from
later-site instructions in arbitrary candidate traces. -/
namespace Ptx.Scalar.Parallel.Control

private theorem synchronize_completion (cfg : Config n) (s : State n) (t : Fin n) (resource : Fin 16)
    (aligned : Aligned s)
    (seen : .barrier (.completion key) ∈ (synchronize cfg s t resource).events) :
    (synchronize cfg s t resource).events = [.barrier (.arrival key t),.barrier (.completion key)] ∧
    (∀ u, (s.lanes u).scalar.pc = key.site) ∧
    (∀ u, ((synchronize cfg s t resource).state.lanes u).scalar.pc = key.site+1) := by
  let c := barrierConfig cfg s t
  let r := barrierRequest cfg s t resource
  by_cases same : r.key = Barrier.key c s.barrier
  · by_cases old : s.barrier.arrived r.thread = true
    · simp [synchronize,← show c=barrierConfig cfg s t from rfl,
        ← show r=barrierRequest cfg s t resource from rfl,Barrier.step,same,old] at seen
    · by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      · have released : (Barrier.step (barrierConfig cfg s t) s.barrier
            (barrierRequest cfg s t resource)).disposition = .released := by
          change (Barrier.step c s.barrier r).disposition = .released
          simp [Barrier.step,same,old,complete]
        have keyEq : key=r.key := by
          simpa [synchronize,← show c=barrierConfig cfg s t from rfl,
            ← show r=barrierRequest cfg s t resource from rfl,Barrier.step,same,old,complete] using seen
        subst key
        have pcs := release_aligned cfg s t resource aligned released
        refine ⟨?_,pcs,?_⟩
        · have actual := Barrier.completing_step c s.barrier r same (Bool.eq_false_iff.mpr old) complete
          simp only [synchronize,show barrierConfig cfg s t = c from rfl,
            show barrierRequest cfg s t resource = r from rfl,actual,List.map_cons,List.map_nil]
          rfl
        · intro u
          simp only [synchronize,released]
          change (s.lanes u).scalar.pc+1=(s.lanes t).scalar.pc+1
          exact congrArg (·+1) (pcs u)
      · simp [synchronize,← show c=barrierConfig cfg s t from rfl,
          ← show r=barrierRequest cfg s t resource from rfl,Barrier.step,same,old,complete] at seen
  · simp [synchronize,← show c=barrierConfig cfg s t from rfl,
      ← show r=barrierRequest cfg s t resource from rfl,Barrier.step,same] at seen

private theorem scalar_no_completion (s : State n) (t : Fin n) (space : Option Space) (i : Scalar.Instr) :
    .barrier (.completion key) ∉ (scalarStep candidate t space i s).events := by
  cases ev : Scalar.eval candidate i {(s.lanes t).scalar with memory := arena s space} <;>
    cases space with
    | none => simp [scalarStep,ev]
    | some space => cases space <;> simp [scalarStep,ev]

theorem dispatch_completion {s : State n} (step : Dispatch cfg candidate t i s out)
    (aligned : Aligned s) (seen : .barrier (.completion key) ∈ out.events) :
    out.events = [.barrier (.arrival key t),.barrier (.completion key)] ∧
    (∀ u, (s.lanes u).scalar.pc = key.site) ∧
    (∀ u, (out.state.lanes u).scalar.pc = key.site+1) := by
  cases step with
  | localStep => exact False.elim (scalar_no_completion _ _ _ _ seen)
  | memory => exact False.elim (scalar_no_completion _ _ _ _ seen)
  | binary32 _ => simp at seen
  | exit => simp at seen
  | sync => exact synchronize_completion _ _ _ _ aligned seen

theorem step_completion {s : State n} (step : Step cfg program candidate t s out)
    (aligned : Aligned s) (seen : .barrier (.completion key) ∈ out.events) :
    out.events = [.barrier (.arrival key t),.barrier (.completion key)] ∧
    (∀ u, (s.lanes u).scalar.pc = key.site) ∧
    (∀ u, (out.state.lanes u).scalar.pc = key.site+1) := by
  have h := step.2
  split at h
  · subst out; simp at seen
  · split at h
    · subst out; simp at seen
    · split at h
      · subst out; simp at seen
      · exact dispatch_completion h aligned seen

/-- Locate the actual release step and its frontRun/suffix derivations. The
completion position comes from the trace, not a supplied phase annotation. -/
theorem completion_split {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (aligned : Aligned s)
    (c : Nat) (key : Barrier.Key) (seen : events[c]? = some (.barrier (.completion key))) :
    ∃ before after middle next t,
      events = before ++ [.barrier (.arrival key t),.barrier (.completion key)] ++ after ∧
      c = before.length+1 ∧ Runs cfg program s before middle ∧ Runs cfg program next after final ∧
      (∀ u, (middle.lanes u).scalar.pc = key.site) ∧
      (∀ u, (next.lanes u).scalar.pc = key.site+1) := by
  induction run generalizing c with
  | nil => simp at seen
  | @cons candidate t s out rest final step run ih =>
    by_cases early : c < out.events.length
    · have atC : out.events[c]? = some (.barrier (.completion key)) := by
        simpa [List.getElem?_append,early] using seen
      obtain ⟨events,pc,nextpc⟩ := step_completion step aligned (List.mem_of_getElem? atC)
      have pos : c=1 := by
        rw [events] at atC
        rcases c with _ | _ | c <;> simp_all
      exact ⟨[],rest,s,out.state,t,by simp [events],by simpa using pos,.nil,run,pc,nextpc⟩
    · have atC : rest[c-out.events.length]? = some (.barrier (.completion key)) := by
        simpa [List.getElem?_append,early] using seen
      obtain ⟨before,after,middle,next,u,trace,pos,frontRun,suffix,pc,nextpc⟩ :=
        ih (step_aligned step aligned) _ atC
      refine ⟨out.events++before,after,middle,next,u,?_,?_,Runs.cons step frontRun,suffix,pc,nextpc⟩
      · simp [trace,List.append_assoc]
      · simp only [List.length_append]; omega

/-- Earlier thread-owned events cannot already have passed this completed site;
later ones have genuinely resumed past it. -/
theorem completion_orders_sites {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : Aligned s)
    (c p : Nat) (key : Barrier.Key) (e : Event n) (t : Fin n) (pc : Nat)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hp : events[p]? = some e) (tag : stamp e = some (t,pc)) :
    (p<c → pc≤key.site) ∧ (c<p → key.site<pc) := by
  obtain ⟨before,after,middle,next,u,trace,pos,frontRun,suffix,pcs,nextpcs⟩ := completion_split run aligned c key hc
  have original := hp
  rw [trace,List.append_assoc] at hp
  have notCompletion : p≠c := by
    intro same
    subst p
    have eq := Option.some.inj (hc.symm.trans original)
    subst e; simp [stamp] at tag
  by_cases early : p<before.length
  · have he : before[p]? = some e := by simpa [List.getElem?_append,early] using hp
    have bound := ((runs_progress frontRun straight).emitted p e t pc he tag).2
    have endBound := (cursor_bounds middle t).2
    rw [pcs] at endBound
    constructor <;> intro h <;> omega
  · by_cases arrival : p=before.length
    · have eq : e = .barrier (.arrival key u) := by
        simpa [List.getElem?_append,arrival] using hp.symm
      subst e
      have equal : pc=key.site := by simpa [stamp] using congrArg (fun v => v.map Prod.snd) tag.symm
      constructor <;> intro h <;> omega
    · have later : before.length+2≤p := by omega
      have he : after[p-(before.length+2)]? = some e := by
        simpa [List.getElem?_append,early,show p-before.length=(p-(before.length+2))+1+1 by omega] using hp
      have bound := ((runs_progress suffix straight).emitted _ e t pc he tag).1
      have startBound := (cursor_bounds next t).1
      rw [nextpcs] at startBound
      constructor <;> intro h <;> omega

/-- A later instruction site lies after the observed collective completion. -/
theorem site_after_completion {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : Aligned s)
    (c p : Nat) (key : Barrier.Key) (e : Event n) (t : Fin n) (pc : Nat)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hp : events[p]? = some e) (tag : stamp e = some (t,pc)) (later : key.site<pc) : c<p := by
  rcases lt_trichotomy c p with before | same | after
  · exact before
  · subst p
    have eq := Option.some.inj (hc.symm.trans hp)
    subst e; simp [stamp] at tag
  · have := (completion_orders_sites run straight aligned c p key e t pc hc hp tag).1 after
    omega

/-- Reuse cannot complete the same straight-line barrier site a second time. -/
theorem completed_sites_ordered {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : Aligned s)
    (c d : Nat) (key other : Barrier.Key)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hd : events[d]? = some (.barrier (.completion other))) (earlier : c<d) : key.site<other.site := by
  obtain ⟨before,after,middle,next,t,trace,pos,_,_,_,_⟩ := completion_split run aligned d other hd
  have atArrival : events[before.length]? = some (.barrier (.arrival other t)) := by
    simp [trace]
  have different : c≠before.length := by
    intro eq
    subst c
    rw [atArrival] at hc
    simp at hc
  exact (completion_orders_sites run straight aligned c before.length key _ t other.site
    hc atArrival rfl).2 (by omega)

theorem completion_site_unique {s final : State n} {events : List (Event n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : Aligned s)
    (c d : Nat) (key other : Barrier.Key)
    (hc : events[c]? = some (.barrier (.completion key)))
    (hd : events[d]? = some (.barrier (.completion other))) (same : key.site=other.site) : c=d := by
  rcases lt_trichotomy c d with before | eq | after
  · have := completed_sites_ordered run straight aligned c d key other hc hd before; omega
  · exact eq
  · have := completed_sites_ordered run straight aligned d c other key hd hc after; omega

end Ptx.Scalar.Parallel.Control
