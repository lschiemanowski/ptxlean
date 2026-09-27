import PtxBinary32.MaximumOwnership
import PtxBinary32.ParallelCoverage

/-! Required producers and barriers are recovered from arbitrary completed
forward executions, not from the selected runner or an assumed phase history. -/
namespace Ptx.Scalar.Parallel.Maximum

theorem fetched_exit_site (d : Nat) (pc : Nat) (fetch : (program d)[pc]?=some .exit) :
    pc=6+24*d+11 := by
  have bound : pc<18+24*d := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<6
  · have atP : (publish)[pc]?=some .exit := by
      simpa [program,List.getElem?_append,product,show pc<6+24*d by omega,
        List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
    have member := List.mem_of_getElem? atP
    simp [publish,publishCode,pointer,Dense.pointer,Dense.scalar] at member
  · by_cases rounds : pc<6+24*d
    · let k := (pc-6)/24
      let j := (pc-6)%24
      have kj : 6+24*k+j=pc := by dsimp [k,j]; omega
      have hk : k<d := by dsimp [k]; omega
      have hj : j<(round d k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round d k)[j]?=some .exit := by rw [← round_fetch d k hk j hj,kj]; exact fetch
      have member := List.mem_of_getElem? atJ
      simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded] at member
    · have jb : pc-(6+24*d)<12 := by omega
      have atJ : (output d)[pc-(6+24*d)]?=some .exit := by
        rw [← output_fetch d _ (by simpa using jb),show 6+24*d+(pc-(6+24*d))=pc by omega]
        exact fetch
      have index : pc-(6+24*d)=11 := by
        generalize pc-(6+24*d)=j at atJ jb ⊢
        interval_cases j <;> simp_all [output,outputCode,pointer,Dense.pointer,scalar,Dense.scalar,guarded,Dense.guarded]
      omega

/-- Halting entails a fetched exit after the entire forward instruction list. -/
theorem completed_pc_bound (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true) :
    6+24*d+11≤(final.lanes t).scalar.pc := by
  obtain ⟨pc,fetch,member⟩ := Control.halted_exit_origin run (program_straight d) t rfl halted
  obtain ⟨p,hp,atP⟩ := List.mem_iff_getElem.mp member
  have bound := ((Control.runs_progress run (program_straight d)).emitted p (.exit t pc) t pc
    (by simpa [hp] using atP) rfl).2
  have upper := (Control.cursor_bounds final t).2
  have site := fetched_exit_site d pc fetch
  omega

/-- Every passed barrier site has an actual completion in this same trace. -/
theorem completed_barrier_exists (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true)
    (pc : Nat) (earlier : pc<6+24*d+11) (fetch : (program d)[pc]?=some (.sync 0)) :
    ∃ (c : Nat) (key : Barrier.Key), events[c]?=some (.barrier (.completion key)) ∧ key.site=pc :=
  Control.crossed_barrier_exists run (program_straight d) (reset_aligned _ _ _ _) t pc (Nat.zero_le _)
    (lt_of_lt_of_le earlier (completed_pc_bound d b global shared seeds run t halted)) fetch

/-- One exited participant entails all preceding collective completions, each
with the actual per-thread arrivals supplied by the machine's history theorem. -/
theorem completed_phases (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true) :
    (∃ phase : History.Phase events, phase.key.site=5) ∧
    (∀ k, k<d → ∃ phase : History.Phase events, phase.key.site=6+24*k+23) := by
  constructor
  · obtain ⟨c,key,hc,site⟩ := completed_barrier_exists d b global shared seeds run t halted 5 (by omega) (by
      simp [program,publish,publishCode,pointer,Dense.pointer,Dense.scalar])
    exact ⟨⟨c,key,hc⟩,site⟩
  · intro k hk
    obtain ⟨c,key,hc,site⟩ := completed_barrier_exists d b global shared seeds run t halted (6+24*k+23) (by omega) (by
      rw [round_fetch d k hk 23 (by simp)]; simp [round,roundCode,roundPrefix,roundSuffix,Scalar.MaximumSelect.code,pointer,Dense.pointer])
    exact ⟨⟨c,key,hc⟩,site⟩

private theorem completed_store_exists (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true)
    (pc : Nat) (space : Space) (guard : Scalar.Guard) (addr : Scalar.Operand64) (value : Scalar.Operand32)
    (earlier : pc<6+24*d+11)
    (fetch : (program d)[pc]?=some (.memory space ⟨guard,.store addr value⟩))
    (enabled : guard=.always ∨ guard=.pred 0 true ∧ (AddressControl.atPC (program d) (controlSeed d seeds t) pc).preds 0=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some space) occ) ∧ occ.pc=pc ∧
      occ.memory=some effect ∧ effect.kind=.store := by
  have finish := completed_pc_bound d b global shared seeds run t halted
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ :=
    Control.crossing_step run (program_straight d) t pc (Nat.zero_le _) (by omega)
  obtain ⟨owner,next,occ,ev,emitted⟩ := Control.memory_crossing step (program_straight d)
    (runs_aligned frontRun (reset_aligned _ _ _ _)) (by rw [old]; exact fetch) (by omega)
  subst u
  have projected := candidate_address_control d b global shared seeds frontRun t
  have active : guard.eval {(middle.lanes t).scalar with memory := arena middle (some space)}=true := by
    rcases enabled with rfl | ⟨rfl,active⟩
    · rfl
    · simpa [Scalar.Guard.eval,projected.pred,old] using active
  simp only [Scalar.eval,active,↓reduceIte] at ev
  split at ev
  · contradiction
  · have info : occ.pc=(middle.lanes t).scalar.pc ∧ ∃ effect : MemoryEffect,
        occ.memory=some effect ∧ effect.kind=.store := by
      obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj ev
      exact ⟨rfl,⟨.store,addr.eval (middle.lanes t).scalar,value.eval (middle.lanes t).scalar⟩,rfl,rfl⟩
    obtain ⟨site,effect,memory,kind⟩ := info
    exact ⟨before.length,occ,effect,by simp [trace,emitted],site.trans old,memory,kind⟩

/-- Every exited thread emitted its unconditional input publication. -/
theorem completed_input_store (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=4 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer t.val := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists d b global shared seeds run t halted
    4 .shared .always (.reg 0) (.reg 4) (by omega) (by simp [program,publish,publishCode,pointer,Dense.pointer,Dense.scalar,Scalar.Instr.plain]) (.inl rfl)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address d b global shared seeds run t .shared occ effect (List.mem_of_getElem? atP) memory store with h | ⟨k,hk,site,_,_⟩ | ⟨site,_,_⟩
  · exact h.2.2
  · omega
  · omega

/-- An active thread emitted its store in every preceding reduction round. -/
theorem completed_round_store (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true) (k : Nat) (hk : k<d)
    (active : t.val<2^(d-(k+1))) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=6+24*k+22 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (((k+1)*width d+t.val)) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists d b global shared seeds run t halted
    (6+24*k+22) .shared (.pred 0 true) (.reg 3) (.reg 6) (by omega)
    (by rw [round_fetch d k hk 22 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [round_control_active b seeds t k hk]; simp [active]⟩)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address d b global shared seeds run t .shared occ effect (List.mem_of_getElem? atP) memory store with ⟨site,_,_⟩ | ⟨j,hj,site,_,addr⟩ | ⟨site,_,_⟩
  · omega
  · have eq : j=k := by omega
    simpa [eq] using addr
  · omega

/-- Exited thread zero emitted the global output store. -/
theorem completed_output_store (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (t : Fin (width d)) (halted : (final.lanes t).halted=true) (leader : t.val=0) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .global) occ) ∧ occ.pc=6+24*d+10 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (width d) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists d b global shared seeds run t halted
    (6+24*d+10) .global (.pred 0 true) (.reg 1) (.reg 6) (by omega)
    (by rw [output_fetch d 10 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [(output_control_address b seeds t).2]; simp [leader]⟩)
  exact ⟨p,occ,effect,atP,pc,memory,store,
    (candidate_global_owner d b global shared seeds run t occ effect (List.mem_of_getElem? atP) memory store).2.1⟩

/-- Input publications occur before their producers' actual arrivals at the
same recovered barrier phase. Initialization is not used as a substitute. -/
theorem completed_input_publication (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) :
    ∃ phase : History.Phase events, phase.key.site=5 ∧ ∀ t,
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=4 ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer t.val ∧
        p<History.arrivalPosition (History.completed_arrivals run rfl) phase t := by
  let first : Fin (width d) := ⟨0,(config d).nonempty⟩
  obtain ⟨phase,site⟩ := (completed_phases d b global shared seeds run first (halted first)).1
  refine ⟨phase,site,?_⟩
  intro t
  obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_input_store d b global shared seeds run t (halted t)
  have arrival := History.arrival_position_spec (History.completed_arrivals run rfl) phase t
  exact ⟨p,occ,effect,atP,pc,memory,kind,addr,
    scalar_before_arrival d run p _ t (some .shared) occ phase.key atP arrival.2 (by omega)⟩

/-- Every active reduction producer publishes before its actual arrival at the
recovered round barrier, under arbitrary candidate scheduling and data values. -/
theorem completed_round_publication (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (k : Nat) (hk : k<d) :
    ∃ phase : History.Phase events, phase.key.site=6+24*k+23 ∧ ∀ t,
      t.val<2^(d-(k+1)) →
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=6+24*k+22 ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (((k+1)*width d+t.val)) ∧
        p<History.arrivalPosition (History.completed_arrivals run rfl) phase t := by
  let first : Fin (width d) := ⟨0,(config d).nonempty⟩
  obtain ⟨phase,site⟩ := (completed_phases d b global shared seeds run first (halted first)).2 k hk
  refine ⟨phase,site,?_⟩
  intro t active
  obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_round_store d b global shared seeds run t (halted t) k hk active
  have arrival := History.arrival_position_spec (History.completed_arrivals run rfl) phase t
  exact ⟨p,occ,effect,atP,pc,memory,kind,addr,
    scalar_before_arrival d run p _ t (some .shared) occ phase.key atP arrival.2 (by omega)⟩

end Ptx.Scalar.Parallel.Maximum
