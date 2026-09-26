import PtxBinary32.GridControl
import PtxBinary32.ParallelCompletion

/-! A group's actual completion separates its earlier and later instructions.
Other groups may be at unrelated sites; no grid-wide barrier is introduced. -/
namespace Ptx.Scalar.Parallel.Grid.Control
open Parallel.Control (Straight)

theorem step_completion {s final : State groups n} {events : List (Event groups n)}
    (step : Step cfg program s events final) (aligned : ∀ g, Parallel.Aligned (view s g))
    (g : Fin groups) (key : Barrier.Key) (seen : (g,.barrier (.completion key)) ∈ events) :
    ∃ t, events=[(g,.barrier (.arrival key t)),(g,.barrier (.completion key))] ∧
      (∀ u, ((s.blocks g).lanes u).scalar.pc=key.site) ∧
      (∀ u, ((final.blocks g).lanes u).scalar.pc=key.site+1) := by
  cases step with
  | issue h t candidate out step =>
    obtain ⟨e,he,eq⟩ := List.mem_map.mp seen
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have info := Parallel.Control.step_completion step (aligned h) he
    exact ⟨t,by simp [tag,info.1],info.2.1,by simpa [install,localOf] using info.2.2⟩

theorem completion_split {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (aligned : ∀ g, Parallel.Aligned (view s g))
    (g : Fin groups) (c : Nat) (key : Barrier.Key) (seen : events[c]?=some (g,.barrier (.completion key))) :
    ∃ before after middle next t,
      events=before++[(g,.barrier (.arrival key t)),(g,.barrier (.completion key))]++after ∧
      c=before.length+1 ∧ Runs cfg program s before middle ∧ Runs cfg program next after final ∧
      (∀ u, ((middle.blocks g).lanes u).scalar.pc=key.site) ∧
      (∀ u, ((next.blocks g).lanes u).scalar.pc=key.site+1) := by
  induction run generalizing c with
  | nil => simp at seen
  | @cons s added middle rest final step run ih =>
    by_cases early : c<added.length
    · have atC : added[c]?=some (g,.barrier (.completion key)) := by simpa [List.getElem?_append,early] using seen
      obtain ⟨t,events,pc,nextpc⟩ := step_completion step aligned g key (List.mem_of_getElem? atC)
      have pos : c=1 := by
        rw [events] at atC
        rcases c with _ | _ | c <;> simp_all
      exact ⟨[],rest,s,middle,t,by simp [events],by simpa using pos,.nil,run,pc,nextpc⟩
    · have atC : rest[c-added.length]?=some (g,.barrier (.completion key)) := by simpa [List.getElem?_append,early] using seen
      obtain ⟨before,after,middle,next,u,trace,pos,frontRun,suffix,pc,nextpc⟩ := ih (Grid.step_aligned step aligned) _ atC
      refine ⟨added++before,after,middle,next,u,?_,?_,Runs.cons step frontRun,suffix,pc,nextpc⟩
      · simp [trace,List.append_assoc]
      · simp only [List.length_append]; omega

/-- Earlier thread-owned events cannot already have passed this completed site;
later ones have genuinely resumed past it. -/
theorem completion_orders_sites {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : ∀ g, Parallel.Aligned (view s g))
    (c p : Nat) (key : Barrier.Key) (e : Event groups n) (g : Fin groups) (t : Fin n) (pc : Nat)
    (hc : events[c]? = some (g,.barrier (.completion key)))
    (hp : events[p]? = some e) (tag : stamp e = some ((g,t),pc)) :
    (p<c → pc≤key.site) ∧ (c<p → key.site<pc) := by
  obtain ⟨before,after,middle,next,u,trace,pos,frontRun,suffix,pcs,nextpcs⟩ := completion_split run aligned g c key hc
  have original := hp
  rw [trace,List.append_assoc] at hp
  have notCompletion : p≠c := by
    intro same
    subst p
    have eq := Option.some.inj (hc.symm.trans original)
    subst e; simp [stamp,Parallel.Control.stamp] at tag
  by_cases early : p<before.length
  · have he : before[p]? = some e := by simpa [List.getElem?_append,early] using hp
    have bound := ((runs_progress frontRun straight).emitted p e (g,t) pc he tag).2
    have endBound := (cursor_bounds middle (g,t)).2
    rw [pcs] at endBound
    constructor <;> intro h <;> omega
  · by_cases arrival : p=before.length
    · have eq : e = (g,.barrier (.arrival key u)) := by
        simpa [List.getElem?_append,arrival] using hp.symm
      subst e
      have equal : pc=key.site := by simpa [stamp,Parallel.Control.stamp] using congrArg (fun v => v.map Prod.snd) tag.symm
      constructor <;> intro h <;> omega
    · have later : before.length+2≤p := by omega
      have he : after[p-(before.length+2)]? = some e := by
        simpa [List.getElem?_append,early,show p-before.length=(p-(before.length+2))+1+1 by omega] using hp
      have bound := ((runs_progress suffix straight).emitted _ e (g,t) pc he tag).1
      have startBound := (cursor_bounds next (g,t)).1
      rw [nextpcs] at startBound
      constructor <;> intro h <;> omega

/-- A later instruction site lies after the observed collective completion. -/
theorem site_after_completion {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : ∀ g, Parallel.Aligned (view s g))
    (c p : Nat) (key : Barrier.Key) (e : Event groups n) (g : Fin groups) (t : Fin n) (pc : Nat)
    (hc : events[c]? = some (g,.barrier (.completion key)))
    (hp : events[p]? = some e) (tag : stamp e = some ((g,t),pc)) (later : key.site<pc) : c<p := by
  rcases lt_trichotomy c p with before | same | after
  · exact before
  · subst p
    have eq := Option.some.inj (hc.symm.trans hp)
    subst e; simp [stamp,Parallel.Control.stamp] at tag
  · have := (completion_orders_sites run straight aligned c p key e g t pc hc hp tag).1 after
    omega

/-- Reuse cannot complete the same straight-line barrier site a second time. -/
theorem completed_sites_ordered {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : ∀ g, Parallel.Aligned (view s g))
    (c d : Nat) (g : Fin groups) (key other : Barrier.Key)
    (hc : events[c]? = some (g,.barrier (.completion key)))
    (hd : events[d]? = some (g,.barrier (.completion other))) (earlier : c<d) : key.site<other.site := by
  obtain ⟨before,after,middle,next,t,trace,pos,_,_,_,_⟩ := completion_split run aligned g d other hd
  have atArrival : events[before.length]? = some (g,.barrier (.arrival other t)) := by
    simp [trace]
  have different : c≠before.length := by
    intro eq
    subst c
    rw [atArrival] at hc
    simp at hc
  exact (completion_orders_sites run straight aligned c before.length key _ g t other.site
    hc atArrival rfl).2 (by omega)

theorem completion_site_unique {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program) (aligned : ∀ g, Parallel.Aligned (view s g))
    (c d : Nat) (g : Fin groups) (key other : Barrier.Key)
    (hc : events[c]? = some (g,.barrier (.completion key)))
    (hd : events[d]? = some (g,.barrier (.completion other))) (same : key.site=other.site) : c=d := by
  rcases lt_trichotomy c d with before | eq | after
  · have := completed_sites_ordered run straight aligned c d g key other hc hd before; omega
  · exact eq
  · have := completed_sites_ordered run straight aligned d c g other key hd hc after; omega

end Ptx.Scalar.Parallel.Grid.Control
