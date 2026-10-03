import PoissonPTX.ReductionWitnessLayout

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256

def ReadyAt (base pc generation : Nat) (s : State 256) : Prop :=
  (∀ t, Frame base t (s.lanes t)) ∧ (∀ t, (s.lanes t).pc=pc) ∧
    s.barrier=Ptx.Barrier.reset generation ∧ s.site=none

theorem round_expected (s : State 256) (phase : Fin 9) (generation : Nat)
    (pcs : ∀ t, (s.lanes t).pc=site phase+1) (reset : s.barrier=Ptx.Barrier.reset generation)
    (noSite : s.site=none) :
    ∃ events, Runs cfg program s events (afterRound s generation) ∧
      ∀ e, e∈events → Expected input e := by
  obtain ⟨events,run⟩ := barrier_round_exists cfg s program (site phase+1) generation pcs reset noSite (barrier_fetch phase)
  refine ⟨events,run,?_⟩
  intro e member
  obtain ⟨b,rfl⟩ := barrier_events run forward pcs (by intro t; simp [afterRound,advance,pcs]) (barrier_fetch phase) e member
  trivial

theorem initial_wave (start : State 256) (ready : ReadyAt base 0 generation start)
    (aligned : base%8=0) (inputs : ∀ t, (start.lanes t).regs 8=input t.val) :
    ∃ final events, Runs cfg program start events final ∧ ReadyAt base 4 (generation+1) final ∧
      ∀ e, e∈events → Expected input e := by
  let target := fun t => SharedStore.finish (start.lanes t) 0 8
  obtain ⟨body,bodyRun,bodyGood⟩ := Serial.run_lanes start target (Expected input) (fun thread state eq barrierEq siteEq => by
    have valid := initial_valid (ready.1 thread) aligned
    have block := initial_block (start.lanes thread) valid
    have fetch : ∀ j op, (SharedStore.code 0 8)[j]?=some op →
        program[(state.lanes thread).pc+j]?=some (.data op) := by
      intro j op found
      have bound := (List.getElem?_eq_some_iff.mp found).1
      have h := initial_fetch ⟨j,by simpa [SharedStore.code] using bound⟩
      simpa only [eq,ready.2.1,Nat.zero_add,found,Option.map_some] using h
    have run := Local.lift (cfg:=cfg) (program:=program) (thread:=thread)
      (eq ▸ block) (by rw [barrierEq,ready.2.2.1]; rfl) fetch
    refine ⟨(initialEvents (start.lanes thread)).map (Event.data thread),?_,?_⟩
    · simpa only [eq] using run
    · intro e member
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
      exact initial_expected _ thread (ready.2.1 thread) (inputs thread) a ha)
  let middle : State 256 := {start with lanes:=target}
  have pcs : ∀ t, (middle.lanes t).pc=site 0+1 := by
    intro t; change (SharedStore.finish (start.lanes t) 0 8).pc=3
    rw [initial_pc,ready.2.1]
  obtain ⟨barriers,barrierRun,barrierGood⟩ := round_expected (input:=input) middle 0 generation pcs ready.2.2.1 ready.2.2.2
  refine ⟨afterRound middle generation,body++barriers,runs_append bodyRun barrierRun,?_,?_⟩
  · refine ⟨?_,?_,rfl,rfl⟩
    · intro t; exact frame_advance (frame_initial (ready.1 t))
    · intro t; simp only [afterRound,advance,pcs]; rfl
  · intro e member; rcases List.mem_append.mp member with h|h
    · exact bodyGood e h
    · exact barrierGood e h

def stageTarget (k : Fin 8) (input : Nat → Word) (thread : Fin 256) (s : PTX.State) : PTX.State :=
  if thread.val<active (current k) then
    finish (advance s) (words input k.val thread.val) (words input k.val (thread.val+active (current k)))
  else {s with pc:=site (current k)+1}

theorem stage_wave (start : State 256) (k : Fin 8)
    (ready : ReadyAt base (4+8*k.val) generation start) (aligned : base%8=0) (input : Nat → Word) :
    ∃ final events, Runs cfg program start events final ∧ ReadyAt base (4+8*(k.val+1)) (generation+1) final ∧
      ∀ e, e∈events → Expected input e := by
  let target := fun t => stageTarget k input t (start.lanes t)
  obtain ⟨body,bodyRun,bodyGood⟩ := Serial.run_lanes start target (Expected input) (fun thread state eq barrierEq siteEq => by
    have fresh : state.barrier.arrived thread=false := by rw [barrierEq,ready.2.2.1]; rfl
    have guard : program[(state.lanes thread).pc]?=some (.skip (active (current k)) (site (current k)+1)) := by
      rw [eq,ready.2.1]; exact guard_fetch k
    by_cases live : thread.val<active (current k)
    · let middle := setLane state thread (advance (state.lanes thread))
      have first := active_guard cfg program state thread fresh guard live
      have laneEq : middle.lanes thread=advance (start.lanes thread) := by simp [middle,setLane,eq]
      have valid := update_valid (frame_advance (ready.1 thread)) aligned k live
      have block := update_block (advance (start.lanes thread)) (readOffset k true)
        (words input k.val thread.val) (words input k.val (thread.val+active (current k))) valid
      have fetch : ∀ j op, (PTX.Reduction.Update.code (readOffset k true))[j]?=some op →
          program[(middle.lanes thread).pc+j]?=some (.data op) := by
        intro j op found
        have bound := (List.getElem?_eq_some_iff.mp found).1
        have h := update_fetch k ⟨j,by simpa [PTX.Reduction.Update.code] using bound⟩
        have pcEq : (middle.lanes thread).pc=5+8*k.val := by
          rw [laneEq]; simp only [advance,ready.2.1]; omega
        rw [pcEq]
        simpa only [found,Option.map_some] using h
      have rest := Local.lift (cfg:=cfg) (program:=program) (thread:=thread) (start:=middle)
        (laneEq ▸ block) (by simpa [middle,setLane] using fresh) fetch
      have whole := runs_append (by simpa using Runs.cons first Runs.nil) rest
      refine ⟨(updateEvents (advance (start.lanes thread)) (readOffset k true)
        (words input k.val thread.val) (words input k.val (thread.val+active (current k)))).map (Event.data thread),?_,?_⟩
      · simpa [middle,setLane,target,stageTarget,live,eq] using whole
      · intro e member
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp member
        apply update_expected input _ k thread _ live a ha
        simp [advance,ready.2.1]; omega
    · have step := padding_guard cfg program state thread fresh guard (by omega)
      refine ⟨[],?_,by simp⟩
      simpa [target,stageTarget,live,eq] using (Runs.cons step Runs.nil))
  let middle : State 256 := {start with lanes:=target}
  have pcs : ∀ t, (middle.lanes t).pc=site (current k)+1 := by
    intro t
    dsimp [middle,target,stageTarget]
    split
    · rw [update_pc]; simp [advance,ready.2.1,site,current]; omega
    · rfl
  obtain ⟨barriers,barrierRun,barrierGood⟩ := round_expected (input:=input) middle (current k) generation pcs ready.2.2.1 ready.2.2.2
  refine ⟨afterRound middle generation,body++barriers,runs_append bodyRun barrierRun,?_,?_⟩
  · refine ⟨?_,?_,rfl,rfl⟩
    · intro t
      apply frame_advance
      dsimp [middle,target,stageTarget]
      split
      · exact frame_update (frame_advance (ready.1 t))
      · exact ready.1 t
    · intro t; simp [afterRound,advance,pcs,site,current]; omega
  · intro e member; rcases List.mem_append.mp member with h|h
    · exact bodyGood e h
    · exact barrierGood e h

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
