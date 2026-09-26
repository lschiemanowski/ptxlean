import PtxBinary32.DenseOwnership
import PtxBinary32.ParallelCoverage

/-! Required producers and barriers are recovered from arbitrary completed
forward executions, not from the selected runner or an assumed phase history. -/
namespace Ptx.Scalar.Parallel.Dense

theorem fetched_exit_site (s : Shape) (pc : Nat) (fetch : (program s)[pc]?=some .exit) :
    pc=22+16*s.depth+19 := by
  have bound : pc<42+16*s.depth := by simpa [program_length] using (List.getElem?_eq_some_iff.mp fetch).choose
  by_cases product : pc<22
  · have atP : (products s)[pc]?=some .exit := by
      simpa [program,List.getElem?_append,product,show pc<22+16*s.depth by omega,
        List.length_flatMap,List.sum_replicate,Nat.mul_comm] using fetch
    have member := List.mem_of_getElem? atP
    simp [products,pointer,scalar,guarded] at member
  · by_cases rounds : pc<22+16*s.depth
    · let k := (pc-22)/16
      let j := (pc-22)%16
      have kj : 22+16*k+j=pc := by dsimp [k,j]; omega
      have hk : k<s.depth := by dsimp [k]; omega
      have hj : j<(round s k).length := by rw [round_length]; dsimp [j]; omega
      have atJ : (round s k)[j]?=some .exit := by rw [← round_fetch s k hk j hj,kj]; exact fetch
      have member := List.mem_of_getElem? atJ
      simp [round,pointer,scalar,guarded] at member
    · have jb : pc-(22+16*s.depth)<20 := by omega
      have atJ : (output s)[pc-(22+16*s.depth)]?=some .exit := by
        rw [← output_fetch s _ (by simpa using jb),show 22+16*s.depth+(pc-(22+16*s.depth))=pc by omega]
        exact fetch
      have index : pc-(22+16*s.depth)=19 := by
        generalize pc-(22+16*s.depth)=j at atJ jb ⊢
        interval_cases j <;> simp_all [output,pointer,scalar,guarded]
      omega

/-- Halting entails a fetched exit after the entire forward instruction list. -/
theorem completed_pc_bound (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true) :
    22+16*s.depth+19≤(final.lanes t).scalar.pc := by
  obtain ⟨pc,fetch,member⟩ := Control.halted_exit_origin run (program_straight s) t rfl halted
  obtain ⟨p,hp,atP⟩ := List.mem_iff_getElem.mp member
  have bound := ((Control.runs_progress run (program_straight s)).emitted p (.exit t pc) t pc
    (by simpa [hp] using atP) rfl).2
  have upper := (Control.cursor_bounds final t).2
  have site := fetched_exit_site s pc fetch
  omega

/-- Every passed barrier site has an actual completion in this same trace. -/
theorem completed_barrier_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true)
    (pc : Nat) (earlier : pc<22+16*s.depth+19) (fetch : (program s)[pc]?=some (.sync 0)) :
    ∃ (c : Nat) (key : Barrier.Key), events[c]?=some (.barrier (.completion key)) ∧ key.site=pc :=
  Control.crossed_barrier_exists run (program_straight s) (reset_aligned _ _ _ _) t pc (Nat.zero_le _)
    (lt_of_lt_of_le earlier (completed_pc_bound s b global shared seeds run t halted)) fetch

/-- One exited participant entails all preceding collective completions, each
with the actual per-thread arrivals supplied by the machine's history theorem. -/
theorem completed_phases (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true) :
    (∃ phase : History.Phase events, phase.key.site=21) ∧
    (∀ k, k<s.depth → ∃ phase : History.Phase events, phase.key.site=22+16*k+15) := by
  constructor
  · obtain ⟨c,key,hc,site⟩ := completed_barrier_exists s b global shared seeds run t halted 21 (by omega) (by
      simp [program,products,pointer,scalar,guarded])
    exact ⟨⟨c,key,hc⟩,site⟩
  · intro k hk
    obtain ⟨c,key,hc,site⟩ := completed_barrier_exists s b global shared seeds run t halted (22+16*k+15) (by omega) (by
      rw [round_fetch s k hk 15 (by simp)]; exact round_barrier s k)
    exact ⟨⟨c,key,hc⟩,site⟩

private theorem completed_store_exists (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true)
    (pc : Nat) (space : Space) (guard : Scalar.Guard) (addr : Scalar.Operand64) (value : Scalar.Operand32)
    (earlier : pc<22+16*s.depth+19)
    (fetch : (program s)[pc]?=some (.memory space ⟨guard,.store addr value⟩))
    (enabled : guard=.always ∨ guard=.pred 0 true ∧ (AddressControl.atPC (program s) (controlSeed s seeds t) pc).preds 0=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some space) occ) ∧ occ.pc=pc ∧
      occ.memory=some effect ∧ effect.kind=.store := by
  have finish := completed_pc_bound s b global shared seeds run t halted
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ :=
    Control.crossing_step run (program_straight s) t pc (Nat.zero_le _) (by omega)
  obtain ⟨owner,next,occ,ev,emitted⟩ := Control.memory_crossing step (program_straight s)
    (runs_aligned frontRun (reset_aligned _ _ _ _)) (by rw [old]; exact fetch) (by omega)
  subst u
  have projected := candidate_address_control s b global shared seeds frontRun t
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

/-- Every exited thread emitted its unconditional product publication. -/
theorem completed_product_store (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=20 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer t.val := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global shared seeds run t halted
    20 .shared .always (.reg 2) (.reg 6) (by omega) (by simp [program,products,pointer,scalar,guarded,Scalar.Instr.plain]) (.inl rfl)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address s b global shared seeds run t .shared occ effect (List.mem_of_getElem? atP) memory store with h | ⟨k,hk,site,_,_⟩ | ⟨site,_,_⟩
  · exact h.2.2
  · omega
  · omega

/-- An active column emitted its store in every preceding reduction round. -/
theorem completed_round_store (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true) (k : Nat) (hk : k<s.depth)
    (active : t.val%s.width<2^(s.depth-(k+1))) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=22+16*k+14 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (nextIndex s k t) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global shared seeds run t halted
    (22+16*k+14) .shared (.pred 0 true) (.reg 2) (.reg 6) (by omega)
    (by rw [round_fetch s k hk 14 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [round_control_active s b seeds t k hk]; simp [active]⟩)
  refine ⟨p,occ,effect,atP,pc,memory,store,?_⟩
  rcases candidate_store_address s b global shared seeds run t .shared occ effect (List.mem_of_getElem? atP) memory store with ⟨site,_,_⟩ | ⟨j,hj,site,_,addr⟩ | ⟨site,_,_⟩
  · omega
  · have eq : j=k := by omega
    simpa [eq] using addr
  · omega

/-- Each exited row leader emitted the row's global output store. -/
theorem completed_output_store (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (t : Fin s.threads) (halted : (final.lanes t).halted=true) (leader : t.val%s.width=0) :
    ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect), events[p]?=some (.scalar t (some .global) occ) ∧ occ.pc=22+16*s.depth+18 ∧
      occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (outputIndex s t) := by
  obtain ⟨p,occ,effect,atP,pc,memory,store⟩ := completed_store_exists s b global shared seeds run t halted
    (22+16*s.depth+18) .global (.pred 0 true) (.reg 6) (.reg 6) (by omega)
    (by rw [output_fetch s 18 (by simp)]; rfl)
    (.inr ⟨rfl,by rw [(output_control_address s b seeds t).2]; simp [leader]⟩)
  exact ⟨p,occ,effect,atP,pc,memory,store,
    (candidate_global_owner s b global shared seeds run t occ effect (List.mem_of_getElem? atP) memory store).2.1⟩

/-- Product publications occur before their producers' actual arrivals at the
same recovered barrier phase. Initialization is not used as a substitute. -/
theorem completed_product_publication (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) :
    ∃ phase : History.Phase events, phase.key.site=21 ∧ ∀ t,
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=20 ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer t.val ∧
        p<History.arrivalPosition (History.completed_arrivals run rfl) phase t := by
  let first : Fin s.threads := ⟨0,(config s b).nonempty⟩
  obtain ⟨phase,site⟩ := (completed_phases s b global shared seeds run first (halted first)).1
  refine ⟨phase,site,?_⟩
  intro t
  obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_product_store s b global shared seeds run t (halted t)
  have arrival := History.arrival_position_spec (History.completed_arrivals run rfl) phase t
  exact ⟨p,occ,effect,atP,pc,memory,kind,addr,
    scalar_before_arrival s run p _ t (some .shared) occ phase.key atP arrival.2 (by omega)⟩

/-- Every active reduction producer publishes before its actual arrival at the
recovered round barrier, under arbitrary candidate scheduling and data values. -/
theorem completed_round_publication (s : Shape) (b : Bounds s) (global shared : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Event s.threads)} {final : Parallel.State s.threads}
    (run : Runs (config s b) (program s) (initial s global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (k : Nat) (hk : k<s.depth) :
    ∃ phase : History.Phase events, phase.key.site=22+16*k+15 ∧ ∀ t,
      t.val%s.width<2^(s.depth-(k+1)) →
      ∃ (p : Nat) (occ : Scalar.Occurrence) (effect : MemoryEffect),
        events[p]?=some (.scalar t (some .shared) occ) ∧ occ.pc=22+16*k+14 ∧
        occ.memory=some effect ∧ effect.kind=.store ∧ effect.address=bytePointer (nextIndex s k t) ∧
        p<History.arrivalPosition (History.completed_arrivals run rfl) phase t := by
  let first : Fin s.threads := ⟨0,(config s b).nonempty⟩
  obtain ⟨phase,site⟩ := (completed_phases s b global shared seeds run first (halted first)).2 k hk
  refine ⟨phase,site,?_⟩
  intro t active
  obtain ⟨p,occ,effect,atP,pc,memory,kind,addr⟩ := completed_round_store s b global shared seeds run t (halted t) k hk active
  have arrival := History.arrival_position_spec (History.completed_arrivals run rfl) phase t
  exact ⟨p,occ,effect,atP,pc,memory,kind,addr,
    scalar_before_arrival s run p _ t (some .shared) occ phase.key atP arrival.2 (by omega)⟩

end Ptx.Scalar.Parallel.Dense
