import PoissonPTX.ConcurrentOrigins

namespace PtxTorchLean.Poisson.PTX.Concurrent
open Ptx

theorem release_aligned (cfg : Config n) (s : State n) (thread : Fin n) (resource : Fin 16)
    (aligned : Aligned s)
    (released : (Barrier.step (barrierConfig cfg s thread) s.barrier
      (barrierRequest cfg s thread resource)).disposition = .released) :
    ∀ t, (s.lanes t).pc = (s.lanes thread).pc := by
  obtain ⟨same,fresh,complete⟩ := (Barrier.released_iff _ _ _).mp released
  have siteEq := congrArg Barrier.Key.site same
  change (s.lanes thread).pc = s.site.getD (s.lanes thread).pc at siteEq
  intro t
  by_cases eq : t = thread
  · subst t; rfl
  have ht := complete t
  have arrived : s.barrier.arrived t = true := by simpa [Barrier.Waiting,Barrier.mark,barrierRequest,eq] using ht
  have hs := aligned t arrived
  rw [hs] at siteEq
  exact siteEq.symm


/-- Every forward skip originating before the boundary lands at or before it.
The Poisson padding branches target their own phase's barrier. -/
def StopsAt (program : List Instr) (boundary : Nat) : Prop :=
  ∀ pc active target, program[pc]?=some (.skip active target) → pc≤boundary → target≤boundary

theorem step_crosses_barrier {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (barrier : program[boundary]?=some (.sync 0))
    (stops : StopsAt program boundary) (thread : Fin n)
    (before : (s.lanes thread).pc≤boundary) (after : boundary<(out.state.lanes thread).pc) :
    ∃ key, Event.barrier (.completion key) ∈ out.events ∧ key.site=boundary := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    by_cases eq : thread=selected
    · subst thread
      have nextPC := data_pc hd
      simp only [setLane,Function.update_self] at after
      have pc : (s.lanes selected).pc=boundary := by omega
      rw [pc,barrier] at fetch; simp at fetch
    · simp [setLane,Function.update,eq] at after
      omega
  | skip =>
    by_cases eq : thread=selected
    · subst thread
      have targetBound := stops _ _ _ fetch before
      simp only [setLane,Function.update_self] at after
      split at after
      · have pc : (s.lanes selected).pc=boundary := by omega
        rw [pc,barrier] at fetch; simp at fetch
      · omega
    · simp [setLane,Function.update,eq] at after
      omega
  | @sync resource =>
    let c := barrierConfig cfg s selected
    let r := barrierRequest cfg s selected resource
    by_cases same : r.key=Barrier.key c s.barrier
    · have notOld : ¬s.barrier.arrived r.thread=true := by simp [r,barrierRequest,fresh]
      by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      · have rel : (Barrier.step c s.barrier r).disposition=.released := by
          simp [Barrier.step,same,notOld,complete]
        have pcs := release_aligned cfg s selected resource aligned rel thread
        have pc : (s.lanes thread).pc=boundary := by
          simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
            ← show r=barrierRequest cfg s selected resource from rfl,
            Barrier.step,same,notOld,complete,advance] at after
          omega
        refine ⟨r.key,?_,?_⟩
        · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
            ← show r=barrierRequest cfg s selected resource from rfl,
            Barrier.step,same,notOld,complete]
        · change (s.lanes selected).pc=boundary
          exact pcs.symm.trans pc
      · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
          ← show r=barrierRequest cfg s selected resource from rfl,
          Barrier.step,same,notOld,complete] at after
        omega
    · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
        ← show r=barrierRequest cfg s selected resource from rfl,
        Barrier.step,same] at after
      omega

/-- A thread observed beyond a protected barrier site has an actual completion
in its execution history. This is derived from fetch and transitions. -/
theorem crossed_barrier {start : State n} (run : Runs cfg program start events final)
    (aligned : Aligned start) (barrier : program[boundary]?=some (.sync 0))
    (stops : StopsAt program boundary) (initial : ∀ t, (start.lanes t).pc≤boundary)
    (thread : Fin n) (after : boundary<(final.lanes thread).pc) :
    ∃ key, Event.barrier (.completion key) ∈ events ∧ key.site=boundary := by
  have invariant : ∀ (s : State n) (trace : List (Event n)) (endState : State n),
      Runs cfg program s trace endState → Aligned s →
      ∀ prior : List (Event n),
      (∀ t, boundary<(s.lanes t).pc → ∃ key, Event.barrier (.completion key)∈prior ∧ key.site=boundary) →
      ∀ t, boundary<(endState.lanes t).pc →
        ∃ key, Event.barrier (.completion key)∈prior++trace ∧ key.site=boundary := by
    intro s trace endState hr
    induction hr with
    | nil => intro ha prior hp t ht; simpa using hp t ht
    | @cons selected current out rest final step tail ih =>
      intro ha prior hp t ht
      have next : ∀ u, boundary<(out.state.lanes u).pc →
          ∃ key, Event.barrier (.completion key)∈prior++out.events ∧ key.site=boundary := by
        intro u hu
        by_cases old : boundary<(current.lanes u).pc
        · obtain ⟨key,mem,site⟩ := hp u old
          exact ⟨key,List.mem_append_left _ mem,site⟩
        · obtain ⟨key,mem,site⟩ := step_crosses_barrier step ha barrier stops u (by omega) hu
          exact ⟨key,List.mem_append_right _ mem,site⟩
      simpa [List.append_assoc] using ih (step_aligned step ha) (prior++out.events) next t ht
  simpa using invariant start events final run aligned []
    (by intro t ht; have := initial t; omega) thread after

theorem access_pc (h : Data op s t (some access)) : access.data.pc=s.pc := by
  cases h <;> rfl

theorem access_single (h : Step cfg program thread s out)
    (member : Event.data owner access∈out.events) : out.events=[.data owner access] := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := h
  cases dispatch with
  | data h =>
    cases ha : ‹Option Access› with
    | none => simp [ha] at member
    | some actual =>
      simp only [ha,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton,Event.data.injEq] at member
      obtain ⟨rfl,rfl⟩ := member
      simp
  | skip => simp at member
  | sync => simp only [synchronize] at member; split at member <;> simp_all

/-- Every later access has a completed barrier and arrivals from all threads
in its actual earlier history. It cannot merely assume that publication happened. -/
theorem access_after_barrier {start : State n} (run : Runs cfg program start events final)
    (reset : start.barrier=Barrier.reset generation)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.lanes t).pc≤boundary)
    (member : Event.data reader access∈events) (later : boundary<access.data.pc) :
    ∃ earlier suffix key, events=earlier++(.data reader access::suffix) ∧
      Event.barrier (.completion key)∈earlier ∧ key.site=boundary ∧
      ∀ t : Fin n, Event.barrier (.arrival key t)∈earlier := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst reader
  have pc := access_pc hd
  have aligned : Aligned start := by intro t h; simp [reset,Barrier.reset] at h
  obtain ⟨key,hkey,site⟩ := crossed_barrier hp aligned barrier stops initial selected (by omega)
  refine ⟨earlier,suffix,key,?_,hkey,site,?_⟩
  · simpa only [access_single hs hm,List.append_assoc,List.singleton_append] using he
  · obtain ⟨c,hc,hce⟩ := List.mem_iff_getElem.mp hkey
    have hcopt : earlier[c]?=some (.barrier (.completion key)) := by simp [hc,hce]
    intro t
    obtain ⟨a,ha,hae⟩ := History.completed_arrivals hp reset c key hcopt t
    exact List.mem_of_getElem? hae

end PtxTorchLean.Poisson.PTX.Concurrent
