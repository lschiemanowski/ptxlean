import PoissonPTX.ReductionWaves
import PoissonPTX.ReductionWitnessAdmission

/-! Arbitrary-input execution existence and numerical correctness for the
256-lane shared tree. The full emitted dot-product entry is still separate. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
open Visibility.Repeated
variable {input : Nat → Word}

/-- Nine full-block barrier rounds, including the initial publication. The
witness runs each phase's lane bodies serially, then completes its barrier. -/
theorem candidate_exists (start : State 256) (ready : ReadyAt base 0 generation start)
    (aligned : base%8=0) (inputs : ∀ t, (start.lanes t).regs 8=input t.val) :
    ∃ final events, Runs cfg program start events final ∧ ReadyAt base 68 (generation+9) final ∧
      ∀ e, e∈events → Expected input e := by
  obtain ⟨middle,initialEvents,first,middleReady,initialGood⟩ := initial_wave start ready aligned inputs
  have stages : ∀ count, count≤8 → ∃ final events, Runs cfg program middle events final ∧
      ReadyAt base (4+8*count) (generation+1+count) final ∧ ∀ e, e∈events → Expected input e := by
    intro count bound
    induction count with
    | zero => exact ⟨middle,[],Runs.nil,by simpa using middleReady,by simp⟩
    | succ count ih =>
      obtain ⟨before,earlier,run,beforeReady,good⟩ := ih (by omega)
      obtain ⟨after,later,tail,afterReady,more⟩ := stage_wave before ⟨count,by omega⟩ beforeReady aligned input
      refine ⟨after,earlier++later,runs_append run tail,?_,?_⟩
      · simpa only [Nat.add_assoc] using afterReady
      · intro e member; rcases List.mem_append.mp member with h|h
        · exact good e h
        · exact more e h
  obtain ⟨final,later,tail,finalReady,finalGood⟩ := stages 8 (by omega)
  refine ⟨final,initialEvents++later,runs_append first tail,?_,?_⟩
  · simpa only [Nat.add_assoc] using finalReady
  · intro e member; rcases List.mem_append.mp member with h|h
    · exact initialGood e h
    · exact finalGood e h

/-- A valid input has a completed actual execution, admitted byte sources and
an actual final store computing the specified rounded numerical reduction. -/
theorem exists_correct (start : State 256) (ready : ReadyAt base 0 generation start)
    (aligned : base%8=0) (inputs : ∀ t, (start.lanes t).regs 8=input t.val)
    (initialMemory : Space → Memory) :
    ∃ final events source,
      Runs cfg program start events final ∧ (∀ t, (final.lanes t).pc=program.length) ∧
      Visibility.Compatible initialMemory events source ∧ OrderedSources events source ∧
      ∃ (w : Nat) (a : Access), events[w]?=some (.data 0 a) ∧
        a.data.pc=66 ∧ a.data.store=true ∧ a.space=.shared ∧ a.data.address=base ∧
        decode a.data.value=Binary64.reduce256 (fun i => decode (input i)) := by
  obtain ⟨final,events,run,finalReady,expected⟩ := candidate_exists start ready aligned inputs
  have baseReg := fun t => (ready.1 t).1
  have laneReg := fun t => (ready.1 t).2.1
  have noWrap : base+2048≤2^64 := by
    obtain ⟨_,_,_,room,upper⟩ := ready.1 (0 : Fin 256)
    omega
  obtain ⟨source,compatible,ordered⟩ := admitted (initialMemory:=initialMemory) run ready.2.2.1 ready.2.1
    baseReg laneReg noWrap expected
  have done : ∀ t, (final.lanes t).pc=program.length := by intro t; rw [finalReady.2.1,length]
  refine ⟨final,events,source,run,done,compatible,ordered,?_⟩
  exact Numeric.completed_result run ready.2.2.1 ready.2.1 baseReg laneReg
    (by intro t; rw [inputs]) noWrap compatible ordered done

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
