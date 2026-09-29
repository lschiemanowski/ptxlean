import PoissonPTX.ConcurrentOrder
import PoissonPTX.BarrierSources

/-! Derive producer-before-barrier order from fetched control. The branch
condition concerns only control flow, never a presumed value or read source. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent
open Ptx

/-- For this thread, a guard cannot jump past the required instruction.
Active threads fall through even when the padding target skips the store. -/
def StopsFor (program : List Instr) (thread : Fin n) (boundary : Nat) : Prop :=
  ∀ pc active target, program[pc]?=some (.skip active target) → pc≤boundary →
    thread.val<active ∨ target≤boundary

theorem step_crosses_store {s : State n} (step : Step cfg program selected s out)
    (aligned : Aligned s) (store : program[boundary]?=some (.data (.store64 sp addr src)))
    (stops : StopsFor program thread boundary)
    (before : (s.lanes thread).pc≤boundary) (after : boundary<(out.state.lanes thread).pc) :
    ∃ access, Event.data thread access ∈ out.events ∧
      access.data.pc=boundary ∧ access.data.store=true ∧ access.space=sp := by
  obtain ⟨fresh,i,fetch,h⟩ := step
  cases h with
  | data hd =>
    by_cases eq : thread=selected
    · subst thread
      have nextPC := data_pc hd
      simp only [setLane,Function.update_self] at after
      have pc : (s.lanes selected).pc=boundary := by omega
      rw [pc,store] at fetch
      cases fetch
      cases hd with
      | ordinary plain he => simp [ordinary] at plain
      | store valid => exact ⟨⟨sp,⟨(s.lanes selected).pc,true,(addr.eval (s.lanes selected)).toNat,src.eval (s.lanes selected)⟩⟩,by simp,pc,rfl,rfl⟩
    · simp [setLane,Function.update,eq] at after
      omega
  | skip =>
    by_cases eq : thread=selected
    · subst thread
      have targetBound := stops _ _ _ fetch before
      simp only [setLane,Function.update_self] at after
      split at after
      · have pc : (s.lanes selected).pc=boundary := by omega
        rw [pc,store] at fetch; simp at fetch
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
        rw [← pcs,pc,store] at fetch; simp at fetch
      · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
          ← show r=barrierRequest cfg s selected resource from rfl,
          Barrier.step,same,notOld,complete] at after
        omega
    · simp [synchronize,← show c=barrierConfig cfg s selected from rfl,
        ← show r=barrierRequest cfg s selected resource from rfl,
        Barrier.step,same] at after
      omega

/-- A producer past its mandatory store has really emitted that store. -/
theorem crossed_store {start : State n} (run : Runs cfg program start events final)
    (aligned : Aligned start) (store : program[boundary]?=some (.data (.store64 sp addr src)))
    (stops : StopsFor program thread boundary) (initial : (start.lanes thread).pc≤boundary)
    (after : boundary<(final.lanes thread).pc) :
    ∃ access, Event.data thread access ∈ events ∧
      access.data.pc=boundary ∧ access.data.store=true ∧ access.space=sp := by
  have invariant : ∀ (s : State n) (trace : List (Event n)) (endState : State n),
      Runs cfg program s trace endState → Aligned s → ∀ prior : List (Event n),
      (boundary<(s.lanes thread).pc → ∃ access, Event.data thread access∈prior ∧
        access.data.pc=boundary ∧ access.data.store=true ∧ access.space=sp) →
      boundary<(endState.lanes thread).pc → ∃ access, Event.data thread access∈prior++trace ∧
        access.data.pc=boundary ∧ access.data.store=true ∧ access.space=sp := by
    intro s trace endState hr
    induction hr with
    | nil => intro ha prior hp ht; simpa using hp ht
    | @cons selected current out rest final step tail ih =>
      intro ha prior hp ht
      have next : boundary<(out.state.lanes thread).pc →
          ∃ access, Event.data thread access∈prior++out.events ∧
            access.data.pc=boundary ∧ access.data.store=true ∧ access.space=sp := by
        intro hu
        by_cases old : boundary<(current.lanes thread).pc
        · obtain ⟨access,mem,props⟩ := hp old
          exact ⟨access,List.mem_append_left _ mem,props⟩
        · obtain ⟨access,mem,props⟩ := step_crosses_store step ha store stops (by omega) hu
          exact ⟨access,List.mem_append_right _ mem,props⟩
      simpa [List.append_assoc] using ih (step_aligned step ha) (prior++out.events) next ht
  simpa using invariant start events final run aligned [] (by intro h; omega) after

/-- Split at the particular event occurrence, preserving its index even when
another occurrence has the same record. -/
theorem run_event_prefix (run : Runs cfg program start events final)
    (observed : events[index]?=some event) :
    ∃ before earlier selected out suffix localIndex,
      Runs cfg program start earlier before ∧ Step cfg program selected before out ∧
      out.events[localIndex]?=some event ∧ Runs cfg program out.state suffix final ∧
      events=earlier++out.events++suffix ∧ index=earlier.length+localIndex := by
  induction run generalizing index with
  | nil => simp at observed
  | @cons thread s out rest final step tail ih =>
    by_cases now : index<out.events.length
    · have atNow : out.events[index]?=some event := by
        simpa [List.getElem?_append,now] using observed
      exact ⟨s,[],thread,out,rest,index,Runs.nil,step,atNow,tail,rfl,by simp⟩
    · have atLater : rest[index-out.events.length]?=some event := by
        simpa [List.getElem?_append,now] using observed
      obtain ⟨before,earlier,selected,next,suffix,j,hp,hs,hm,ht,he,hi⟩ := ih atLater
      refine ⟨before,out.events++earlier,selected,next,suffix,j,Runs.cons step hp,hs,hm,ht,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp only [List.length_append]; omega

/-- Arrival records use the selected thread's actual instruction position. -/
theorem step_arrival_origin (h : Step cfg program selected s out)
    (member : Event.barrier (.arrival key thread) ∈ out.events) :
    thread=selected ∧ key.site=(s.lanes thread).pc := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := h
  cases dispatch with
  | data h => cases ‹Option Access› <;> simp at member
  | skip => simp at member
  | @sync resource =>
    unfold synchronize at member
    generalize hc : barrierConfig cfg s selected=c at member
    generalize hr : barrierRequest cfg s selected resource=r at member
    by_cases same : r.key=Barrier.key c s.barrier
    · have notOld : ¬s.barrier.arrived r.thread=true := by simp [← hr,barrierRequest,fresh]
      by_cases complete : Barrier.Complete (Barrier.mark s.barrier r.thread)
      all_goals simp [Barrier.step,same,notOld,complete] at member
      all_goals obtain ⟨rfl,rfl⟩ := member
      all_goals simp [← same,← hr,barrierRequest]
    · simp [Barrier.step,same] at member

/-- Every actual arrival beyond a mandatory store has an earlier executed store
from that very writer. No ordering relation is supplied by the caller. -/
theorem store_before_arrival {start : State n} {key : Barrier.Key} {events : List (Event n)} {a : Nat} (run : Runs cfg program start events final)
    (aligned : Aligned start) (store : program[storePC]?=some (.data (.store64 sp addr src)))
    (stops : StopsFor program writer storePC) (initial : (start.lanes writer).pc≤storePC)
    (arrival : events[a]?=some (Event.barrier (.arrival key writer))) (later : storePC<key.site) :
    ∃ w access, w<a ∧ events[w]?=some (Event.data writer access) ∧
      access.data.pc=storePC ∧ access.data.store=true ∧ access.space=sp := by
  obtain ⟨before,earlier,selected,out,suffix,j,hp,hs,hm,ht,he,hi⟩ := run_event_prefix run arrival
  have origin := step_arrival_origin hs (List.mem_of_getElem? hm)
  obtain ⟨access,mem,props⟩ := crossed_store hp aligned store stops initial (by omega)
  obtain ⟨w,hw,hwe⟩ := List.mem_iff_getElem.mp mem
  refine ⟨w,access,by omega,?_,props⟩
  rw [he]
  simp [List.getElem?_append,hw,hwe]

/-- An indexed later access has an earlier actual completion at this barrier. -/
theorem access_after_barrier_index {start : State n} {events : List (Event n)} {r : Nat}
    (run : Runs cfg program start events final) (aligned : Aligned start)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.lanes t).pc≤boundary)
    (observed : events[r]?=some (Event.data reader access)) (later : boundary<access.data.pc) :
    ∃ c key, c<r ∧ events[c]?=some (.barrier (.completion key)) ∧ key.site=boundary := by
  obtain ⟨before,earlier,selected,out,suffix,j,hp,hs,hm,ht,he,hi⟩ := run_event_prefix run observed
  have mem := List.mem_of_getElem? hm
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs mem
  subst reader
  have pc := access_pc hd
  obtain ⟨key,hkey,site⟩ := crossed_barrier hp aligned barrier stops initial selected (by omega)
  obtain ⟨c,hc,hce⟩ := List.mem_iff_getElem.mp hkey
  refine ⟨c,key,by omega,?_,site⟩
  rw [he]
  simp [List.getElem?_append,hc,hce]

/-- Fetched control supplies the complete strict store/arrival/completion/read
path required by the byte-source theorem, for any actual candidate run. -/
theorem producer_across {start : State n} {events : List (Event n)} {r : Nat}
    (run : Runs cfg program start events final)
    (reset : start.barrier=Barrier.reset generation)
    (store : program[storePC]?=some (.data (.store64 sp addr src)))
    (writerStops : StopsFor program writer storePC)
    (writerInitial : (start.lanes writer).pc≤storePC) (beforeBarrier : storePC<boundary)
    (barrier : program[boundary]?=some (.sync 0)) (stops : StopsAt program boundary)
    (initial : ∀ t, (start.lanes t).pc≤boundary)
    (observed : events[r]?=some (Event.data reader access)) (later : boundary<access.data.pc) :
    ∃ w wa, events[w]?=some (.data writer wa) ∧ wa.data.pc=storePC ∧
      wa.data.store=true ∧ wa.space=sp ∧ Visibility.Across events w r := by
  have aligned : Aligned start := by intro t h; simp [reset,Barrier.reset] at h
  obtain ⟨c,key,hcr,hc,site⟩ := access_after_barrier_index run aligned barrier stops initial observed later
  obtain ⟨a,hac,ha⟩ := History.completed_arrivals run reset c key hc writer
  obtain ⟨w,wa,hwa,hw,pc,write,space⟩ := store_before_arrival run aligned store writerStops writerInitial ha (by omega)
  exact ⟨w,wa,hw,pc,write,space,writer,reader,wa,access,key,a,c,hw,observed,ha,hc,hwa,hac,hcr⟩

end PtxTorchLean.Poisson.PTX.Concurrent
