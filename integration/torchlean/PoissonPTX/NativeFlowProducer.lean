import PoissonPTX.NativeFlowReadBarrier

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

/-- A protection store cannot be crossed by an ordinary step that starts
strictly before it. Concrete code discharges this using fetched predicates. -/
def Protects (ctx : Kernel.Context) (program : List Instr) (boundary : Nat) (s : Flow.State) : Prop :=
  ∀ i t access index, program[s.core.pc]?=some (.flow i) →
    Flow.Observed.Eval ctx i s t access index → s.core.pc<boundary → t.core.pc≤boundary

theorem step_crosses_store {s : State n}
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (store : program[boundary]?=some (.flow (.data (.data (.store64 sp addr src)))))
    (protects : Protects (ctx owner) program boundary (lane s owner))
    (before : (s.core.lanes owner).pc≤boundary) (after : boundary<(out.state.core.lanes owner).pc) :
    ∃ access, Event.data owner access∈out.events ∧ access.data.pc=boundary ∧
      access.data.store=true ∧ access.space=sp := by
  cases actual with
  | @flow instruction _ next word index running fresh fetch effect =>
    by_cases same : owner=selected
    · subst owner
      simp only [update,setLane,Function.update_self] at after
      have atStore : (s.core.lanes selected).pc=boundary := by
        by_contra different
        have upper := protects _ _ _ _ fetch effect (by change (s.core.lanes selected).pc<boundary; omega)
        omega
      rw [atStore,store] at fetch
      cases fetch
      cases effect with
      | data step =>
        cases step with
        | data step =>
          cases step with
          | ordinary plain _ => simp [Concurrent.ordinary] at plain
          | store valid => exact ⟨⟨sp,⟨(s.core.lanes selected).pc,true,(addr.eval (s.core.lanes selected)).toNat,src.eval (s.core.lanes selected)⟩⟩,by simp [lane],atStore,rfl,rfl⟩
      | simple ordinary => exact False.elim (ordinary _ rfl)
    · simp [update,setLane,Function.update,same] at after
      omega
  | @sync _ resource running fresh fetch =>
    have released : (Ptx.Barrier.step (barrierConfig cfg s.core selected) s.core.barrier
        (barrierRequest cfg s.core selected resource)).disposition=.released := by
      by_contra blocked
      simp only [synchronize] at after
      split at after <;> simp only at after
      · omega
      · omega
      · exact False.elim (blocked (by assumption))
    have samePC := release_aligned cfg s.core selected resource aligned released owner
    have atStore : (s.core.lanes owner).pc=boundary := by
      simp only [synchronize,released,advance] at after
      omega
    rw [← samePC,atStore,store] at fetch
    cases fetch

/-- Protection is required only at actual reachable prefix states. It concerns
branch control, not the desired store value or a supplied memory observation. -/
theorem crossed_store {start : State n}
    (run : Runs cfg ctx program start events indices final) (aligned : Aligned start.core)
    (store : program[boundary]?=some (.flow (.data (.data (.store64 sp addr src)))))
    (protection : ∀ before earlier earlierIndices, Runs cfg ctx program start earlier earlierIndices before →
      Protects (ctx owner) program boundary (lane before owner))
    (before : (start.core.lanes owner).pc≤boundary) (after : boundary<(final.core.lanes owner).pc) :
    ∃ access, Event.data owner access∈events ∧ access.data.pc=boundary ∧
      access.data.store=true ∧ access.space=sp := by
  induction run with
  | nil => omega
  | @cons selected s out restWords restIndices final one rest ih =>
    by_cases passed : boundary<(out.state.core.lanes owner).pc
    · obtain ⟨access,found,props⟩ := step_crosses_store one aligned store (protection _ _ _ .nil) before passed
      exact ⟨access,List.mem_append_left _ found,props⟩
    · obtain ⟨access,found,props⟩ := ih (step_aligned one aligned)
        (fun t words idx earlier => protection t (out.events++words) (out.indices++idx) (.cons one earlier))
        (by omega) after
      exact ⟨access,List.mem_append_right _ found,props⟩

theorem store_before_arrival {start : State n} {key : Ptx.Barrier.Key} {events : List (Event n)} {a : Nat}
    (run : Runs cfg ctx program start events indices final) (aligned : Aligned start.core)
    (store : program[storePC]?=some (.flow (.data (.data (.store64 sp addr src)))))
    (protection : ∀ before earlier earlierIndices, Runs cfg ctx program start earlier earlierIndices before →
      Protects (ctx writer) program storePC (lane before writer))
    (initial : (start.core.lanes writer).pc≤storePC)
    (arrival : events[a]?=some (.barrier (.arrival key writer))) (later : storePC<key.site) :
    ∃ w access, w<a ∧ events[w]?=some (.data writer access) ∧
      access.data.pc=storePC ∧ access.data.store=true ∧ access.space=sp := by
  obtain ⟨before,earlier,earlierIndices,selected,out,suffix,suffixIndices,j,hp,hs,hm,ht,he,hi⟩ := event_prefix run arrival
  have origin := step_arrival_origin hs (List.mem_of_getElem? hm)
  obtain ⟨access,mem,props⟩ := crossed_store hp aligned store protection initial (by omega)
  obtain ⟨w,hw,hwe⟩ := List.mem_iff_getElem.mp mem
  refine ⟨w,access,by omega,?_,props⟩
  rw [he]
  simp [List.getElem?_append,hw,hwe]

/-- The entire store/arrival/completion/read causal path is extracted from
actual native execution and concrete store-protection obligations. -/
theorem producer_across {start : State n} {events : List (Event n)} {r : Nat}
    (run : Runs cfg ctx program start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (store : program[storePC]?=some (.flow (.data (.data (.store64 sp addr src)))))
    (protection : ∀ before earlier earlierIndices, Runs cfg ctx program start earlier earlierIndices before →
      Protects (ctx writer) program storePC (lane before writer))
    (writerInitial : (start.core.lanes writer).pc≤storePC) (beforeBarrier : storePC<boundary)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.core.lanes t).pc≤boundary)
    (observed : events[r]?=some (.data reader access)) (later : boundary<access.data.pc) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧ wa.data.pc=storePC ∧
      wa.data.store=true ∧ wa.space=sp ∧ Visibility.Across events w r := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨c,key,hcr,hc,site⟩ := access_after_barrier_index run aligned barrier stops initial observed later
  obtain ⟨a,hac,ha⟩ := completed_arrivals run reset c key hc writer
  obtain ⟨w,wa,hwa,hw,pc,write,space⟩ := store_before_arrival run aligned store protection writerInitial ha (by omega)
  exact ⟨w,wa,hw,pc,write,space,writer,reader,wa,access,key,a,c,hw,observed,ha,hc,hwa,hac,hcr⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
