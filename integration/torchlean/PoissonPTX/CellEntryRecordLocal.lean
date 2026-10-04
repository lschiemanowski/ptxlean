import PoissonPTX.CellEntryBefore
import PoissonPTX.CellEntryReplay
import PoissonPTX.ObservedReadWitness

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Lift an ordinary lane step before its barrier into the actual concurrent
machine, recording precisely the bytes that step read. -/
theorem record_local_step
    (step : Local.Step (ctx thread) (Before.code width cells source) (lane s thread) next)
    (fresh : s.core.barrier.arrived thread=false) :
    ∃ events indices,
      Step cfg ctx (program width cells source) thread s ⟨setLane s thread next,events,indices⟩ ∧
      Words (s.core.lanes thread).global events ∧ Indices (s.core.lanes thread).global indices := by
  obtain ⟨i,fetch,execution⟩ := step
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  change (s.core.lanes thread).pc < (Before.code width cells source).length at bound
  have full : (program width cells source)[(s.core.lanes thread).pc]?=some i := by
    rw [Before.program_eq,List.getElem?_append_left bound]
    exact fetch
  cases i with
  | setup op => exact ⟨[],[],⟨fresh,_,full,.setup execution⟩,by simp [Words],by simp [Indices]⟩
  | gather op =>
    simp only [Local.eval,Option.map_eq_some_iff] at execution
    obtain ⟨core,executed,rfl⟩ := execution
    obtain ⟨access,index,recorded,words,indices⟩ := Flow.Observed.data_read_witness (Indexed.eval_sound executed)
    have same : setLane s thread ⟨core,(lane s thread).live⟩=⟨Concurrent.setLane s.core thread core,s.live⟩ := by
      simp [setLane,lane]
    refine ⟨access.toList.map (Concurrent.Event.data thread),index.toList.map (thread,·),?_,?_,?_⟩
    · rw [same]; exact ⟨fresh,_,full,.gather recorded⟩
    · intro owner a member read global
      have h : access=some a ∧ thread=owner := by simpa using member
      have val := words a h.1 read
      simpa [global,lane,PTX.State.memory] using val
    · intro owner a member
      have h : index=some a ∧ thread=owner := by simpa using member
      exact indices a h.1
  | skip target =>
    simp only [Local.eval,Option.some.injEq] at execution
    rw [← execution]
    have same : setLane s thread
        ⟨{(lane s thread).core with pc:=if (lane s thread).live then (lane s thread).core.pc+1 else target},(lane s thread).live⟩=
        ⟨Concurrent.setLane s.core thread {(s.core.lanes thread) with pc:=if s.live thread then (s.core.lanes thread).pc+1 else target},s.live⟩ := by
      simp [setLane,lane]
      rfl
    refine ⟨[],[],?_,by simp [Words],by simp [Indices]⟩
    rw [same]; exact ⟨fresh,_,full,.skip⟩
  | sync => exact False.elim (Before.no_sync _ (List.mem_of_getElem? fetch) rfl)

theorem set_lane_self : setLane s thread (lane s thread)=s := by
  simp [setLane,lane,Concurrent.setLane]

theorem set_lane_twice : setLane (setLane s thread first) thread last=setLane s thread last := by
  simp [setLane,Concurrent.setLane]

/-- All lane-local reads in this prefix refer to unchanged global input bytes.
This records the finite local run without choosing a tensor answer. -/
theorem record_local_run
    (run : Local.Runs (ctx thread) (Before.code width cells source) (lane s thread) next)
    (fresh : s.core.barrier.arrived thread=false) :
    ∃ events indices,
      Runs cfg ctx (program width cells source) s events indices (setLane s thread next) ∧
      Words (s.core.lanes thread).global events ∧ Indices (s.core.lanes thread).global indices := by
  generalize firstEq : lane s thread=first at run
  induction run generalizing s with
  | nil => rw [← firstEq]; exact ⟨[],[],by rw [set_lane_self]; exact .nil,by simp [Words],by simp [Indices]⟩
  | @cons first middle final step rest ih =>
    obtain ⟨events,indices,one,words,ix⟩ := record_local_step (firstEq ▸ step) fresh
    have laneEq : lane (setLane s thread middle) thread=middle := by simp [lane,setLane,Concurrent.setLane]
    obtain ⟨later,laterIndices,tail,more,moreIx⟩ := ih (s:=setLane s thread middle) fresh laneEq
    have global := step_global one thread
    refine ⟨events++later,indices++laterIndices,?_,?_,?_⟩
    · rw [set_lane_twice] at tail
      exact .cons one tail
    · intro owner a member read space
      rcases List.mem_append.mp member with before | after
      · exact words owner a before read space
      · rw [global] at more; exact more owner a after read space
    · intro owner a member
      rcases List.mem_append.mp member with before | after
      · exact ix owner a before
      · rw [global] at moreIx; exact moreIx owner a after

end PtxTorchLean.Poisson.PTX.CellEntry
