import PtxBinary32.ParallelCompletion

/-! Recover actual execution steps at sites crossed by a thread. Completion of
an execution is evidence, never a scheduler fairness assumption. -/
namespace Ptx.Scalar.Parallel.Control

private theorem scalar_next_pc (i : Scalar.Instr) (s next : Scalar.State) (event : Scalar.Occurrence)
    (straight : StraightOp i.op) (evaluated : Scalar.eval candidate i s = .next next event) : next.pc=s.pc+1 := by
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [StraightOp] at straight
  all_goals first | contradiction | skip
  all_goals cases enabled : guard.eval s <;> simp only [Scalar.eval,enabled,↓reduceIte] at evaluated
  all_goals first
    | (obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated; rfl)
    | contradiction
    | (split at evaluated; contradiction; obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated; rfl)

private theorem scalar_no_halt (i : Scalar.Instr) (s next : Scalar.State) (event : Scalar.Occurrence)
    (straight : StraightOp i.op) : Scalar.eval candidate i s ≠ .halted next event := by
  rcases i with ⟨guard,op⟩
  cases op <;> simp only [StraightOp] at straight
  all_goals cases enabled : guard.eval s <;> simp only [Scalar.eval,enabled,↓reduceIte]
  all_goals first | (solve | simp) | (split <;> simp)

private theorem scalar_other (s : State n) (selected t : Fin n) (different : t≠selected)
    (space : Option Space) (i : Scalar.Instr) :
    ((scalarStep candidate selected space i s).state.lanes t).scalar.pc=(s.lanes t).scalar.pc := by
  cases ev : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} <;>
    cases space with
    | none => simp [scalarStep,ev,setLane,Function.update,different]
    | some space => cases space <;> simp [scalarStep,ev,setLane,Function.update,different]

private theorem scalar_bound (s : State n) (selected t : Fin n) (space : Option Space) (i : Scalar.Instr)
    (straight : StraightOp i.op) :
    ((scalarStep candidate selected space i s).state.lanes t).scalar.pc≤(s.lanes t).scalar.pc+1 := by
  by_cases same : t=selected
  · subst t
    cases ev : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} with
    | next next event =>
      have pc := scalar_next_pc i _ next event straight ev
      cases space with
      | none => simp [scalarStep,ev,setLane,pc]
      | some space => cases space <;> simp [scalarStep,ev,setLane,pc]
    | halted next event => exact False.elim (scalar_no_halt i _ _ _ straight ev)
    | fault reason => simp [scalarStep,ev]
    | unsupported spelling => simp [scalarStep,ev]
  · rw [scalar_other s selected t same space i]; omega

/-- A step can advance a PC by at most one, including a collective release. -/
theorem dispatch_pc_bound {s : State n} (step : Dispatch cfg candidate selected i s out) (straight : StraightInstr i)
    (t : Fin n) : (out.state.lanes t).scalar.pc≤(s.lanes t).scalar.pc+1 := by
  cases step with
  | localStep => exact scalar_bound s selected t _ _ straight
  | memory => exact scalar_bound s selected t _ _ straight
  | binary32 ev =>
    have pc := (Scalar.Binary32.eval_frame _ _ _ _ ev).1
    by_cases same : t=selected
    · subst t; simp [setLane,pc]
    · simp [setLane,Function.update,same]
  | sync =>
    rename_i resource
    cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition <;>
      simp [synchronize,hd]
  | exit =>
    by_cases same : t=selected
    · subst t; simp [setLane]
    · simp [setLane,Function.update,same]

theorem step_pc_bound {s : State n} (step : Step cfg program candidate selected s out) (straight : Straight program)
    (t : Fin n) : (out.state.lanes t).scalar.pc≤(s.lanes t).scalar.pc+1 := by
  have h := step.2
  split at h
  · subst out; simp
  · split at h
    · subst out; simp
    · split at h
      · subst out; simp
      · exact dispatch_pc_bound h (straight _ (List.mem_of_getElem? (by assumption))) t

/-- Locate the step that passes a site, retaining its actual prefix and suffix. -/
theorem crossing_step {s : State n} (run : Runs cfg program s events final) (straight : Straight program)
    (t : Fin n) (pc : Nat) (start : (s.lanes t).scalar.pc≤pc) (finish : pc<(final.lanes t).scalar.pc) :
    ∃ before after middle out selected candidate,
      events=before++out.events++after ∧ Runs cfg program s before middle ∧
      Step cfg program candidate selected middle out ∧ Runs cfg program out.state after final ∧
      (middle.lanes t).scalar.pc=pc ∧ (out.state.lanes t).scalar.pc=pc+1 := by
  induction run with
  | nil => omega
  | @cons candidate selected s out rest final step run ih =>
    by_cases passed : pc<(out.state.lanes t).scalar.pc
    · have bound := step_pc_bound step straight t
      exact ⟨[],rest,s,out,selected,candidate,by simp,.nil,step,run,by omega,by omega⟩
    · obtain ⟨before,after,middle,next,u,c,trace,frontRun,cross,suffix,old,new⟩ := ih (by omega) finish
      exact ⟨out.events++before,after,middle,next,u,c,by simp [trace,List.append_assoc],
        Runs.cons step frontRun,cross,suffix,old,new⟩

/-- At a scalar-memory site, only that thread's successful scalar evaluation
can advance it. A barrier release cannot impersonate this instruction. -/
theorem memory_crossing (step : Step cfg program candidate selected s out) (straight : Straight program) (aligned : Aligned s)
    (fetch : program[(s.lanes t).scalar.pc]?=some (.memory space i))
    (advance : (out.state.lanes t).scalar.pc=(s.lanes t).scalar.pc+1) :
    selected=t ∧ ∃ next occ,
      Scalar.eval candidate i {(s.lanes t).scalar with memory := arena s (some space)}=.next next occ ∧
      out.events=[.scalar t (some space) occ] := by
  have h := step.2
  split at h
  · subst out; simp at advance
  · split at h
    · subst out; simp at advance
    · split at h
      · subst out; simp at advance
      · rename_i inst atSelected
        have owner : selected=t := by
          by_contra different
          cases h with
          | localStep => rw [scalar_other s selected t (Ne.symm different)] at advance; omega
          | memory => rw [scalar_other s selected t (Ne.symm different)] at advance; omega
          | binary32 _ | exit => simp [setLane,Function.update,Ne.symm different] at advance
          | sync =>
            rename_i resource
            cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition with
            | waiting => simp [synchronize,hd] at advance
            | rejectedWrongKey => simp [synchronize,hd] at advance
            | released =>
              have pcs := release_aligned cfg s selected resource aligned hd
              rw [pcs t,atSelected] at fetch; cases fetch
        subst selected
        rw [fetch] at atSelected
        cases Option.some.inj atSelected
        cases h
        cases ev : Scalar.eval candidate i {(s.lanes t).scalar with memory := arena s (some space)} with
        | next next occ => exact ⟨rfl,next,occ,rfl,by simp [scalarStep,ev]⟩
        | halted next occ => exact False.elim (scalar_no_halt i _ _ _ (straight _ (List.mem_of_getElem? fetch)) ev)
        | fault reason => simp [scalarStep,ev] at advance
        | unsupported spelling => simp [scalarStep,ev] at advance

private theorem sync_passed (cfg : Config n) (s : State n) (selected t : Fin n) (resource : Fin 16)
    (aligned : Aligned s)
    (advance : ((synchronize cfg s selected resource).state.lanes t).scalar.pc=(s.lanes t).scalar.pc+1) :
    ∃ key, key.site=(s.lanes t).scalar.pc ∧ .barrier (.completion key) ∈ (synchronize cfg s selected resource).events := by
  cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition with
  | waiting => simp [synchronize,hd] at advance
  | rejectedWrongKey => simp [synchronize,hd] at advance
  | released =>
    obtain ⟨same,fresh,complete⟩ := (Barrier.released_iff _ _ _).mp hd
    have actual := Barrier.completing_step _ _ _ same fresh complete
    refine ⟨(barrierRequest cfg s selected resource).key,(release_aligned cfg s selected resource aligned hd t).symm,?_⟩
    simp only [synchronize,actual,List.map_cons,List.map_nil,List.mem_cons]
    exact .inr (.inl trivial)

/-- Passing a synchronization site requires a recorded collective completion. -/
theorem barrier_crossing {s : State n} (step : Step cfg program candidate selected s out) (aligned : Aligned s)
    (fetch : program[(s.lanes t).scalar.pc]?=some (.sync resource))
    (advance : (out.state.lanes t).scalar.pc=(s.lanes t).scalar.pc+1) :
    ∃ key, key.site=(s.lanes t).scalar.pc ∧ .barrier (.completion key) ∈ out.events := by
  have h := step.2
  split at h
  · subst out; simp at advance
  · split at h
    · subst out; simp at advance
    · split at h
      · subst out; simp at advance
      · rename_i inst atSelected
        by_cases owner : t=selected
        · subst t
          rw [fetch] at atSelected
          cases Option.some.inj atSelected
          cases h
          exact sync_passed _ _ _ _ _ aligned advance
        · cases h with
          | localStep => rw [scalar_other s selected t owner] at advance; omega
          | memory => rw [scalar_other s selected t owner] at advance; omega
          | binary32 _ | exit => simp [setLane,Function.update,owner] at advance
          | sync => exact sync_passed _ _ _ _ _ aligned advance

/-- The trace really contains a completion at every synchronization site crossed
by any participant. No desired barrier history is supplied by the caller. -/
theorem crossed_barrier_exists {s : State n} (run : Runs cfg program s events final)
    (straight : Straight program) (aligned : Aligned s) (t : Fin n) (pc : Nat)
    (start : (s.lanes t).scalar.pc≤pc) (finish : pc<(final.lanes t).scalar.pc)
    (fetch : program[pc]?=some (.sync resource)) :
    ∃ (c : Nat) (key : Barrier.Key), events[c]?=some (.barrier (.completion key)) ∧ key.site=pc := by
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ := crossing_step run straight t pc start finish
  obtain ⟨key,site,member⟩ := barrier_crossing step (runs_aligned frontRun aligned) (by rw [old]; exact fetch) (by omega)
  have present : .barrier (.completion key) ∈ events := by rw [trace]; simp only [List.mem_append]; exact .inl (.inr member)
  obtain ⟨c,bound,atC⟩ := List.mem_iff_getElem.mp present
  exact ⟨c,key,by simpa [bound] using atC,site.trans old⟩

private theorem scalar_halt_frame (s : State n) (selected t : Fin n) (space : Option Space) (i : Scalar.Instr)
    (straight : StraightOp i.op) :
    ((scalarStep candidate selected space i s).state.lanes t).halted=(s.lanes t).halted := by
  cases ev : Scalar.eval candidate i {(s.lanes selected).scalar with memory := arena s space} with
  | next next event =>
    cases space with
    | none => simp [scalarStep,ev,setLane,Function.update]; split <;> simp_all
    | some space => cases space <;> simp [scalarStep,ev,setLane,Function.update] <;> split <;> simp_all
  | halted next event => exact False.elim (scalar_no_halt i _ _ _ straight ev)
  | fault reason => simp [scalarStep,ev]
  | unsupported spelling => simp [scalarStep,ev]

private theorem step_halt_origin {s : State n} (step : Step cfg program candidate selected s out) (straight : Straight program)
    (live : (s.lanes t).halted=false) (halted : (out.state.lanes t).halted=true) :
    ∃ pc, program[pc]?=some .exit ∧ .exit t pc ∈ out.events := by
  have h := step.2
  split at h
  · subst out; simp [live] at halted
  · split at h
    · subst out; simp [live] at halted
    · split at h
      · subst out; simp [live] at halted
      · rename_i inst atSelected
        have form := straight inst (List.mem_of_getElem? atSelected)
        cases h with
        | localStep => rw [scalar_halt_frame s selected t _ _ form,live] at halted; contradiction
        | memory => rw [scalar_halt_frame s selected t _ _ form,live] at halted; contradiction
        | binary32 _ => simp [setLane,Function.update] at halted; split at halted <;> simp_all
        | sync =>
          rename_i resource
          cases hd : (Barrier.step (barrierConfig cfg s selected) s.barrier (barrierRequest cfg s selected resource)).disposition <;>
            simp [synchronize,hd,live] at halted
        | exit =>
          have owner : t=selected := by by_contra h; simp [setLane,Function.update,h,live] at halted
          subst t
          exact ⟨_,atSelected,by simp⟩

/-- A halted lane started live and therefore executed an actual fetched exit. -/
theorem halted_exit_origin {s : State n} (run : Runs cfg program s events final) (straight : Straight program)
    (t : Fin n) (live : (s.lanes t).halted=false) (halted : (final.lanes t).halted=true) :
    ∃ pc, program[pc]?=some .exit ∧ .exit t pc ∈ events := by
  induction run with
  | nil => simp [live] at halted
  | @cons candidate selected s out rest final step run ih =>
    by_cases done : (out.state.lanes t).halted = true
    · obtain ⟨pc,fetch,member⟩ := step_halt_origin step straight live done
      exact ⟨pc,fetch,List.mem_append_left _ member⟩
    · obtain ⟨pc,fetch,member⟩ := ih (Bool.eq_false_iff.mpr done) halted
      exact ⟨pc,fetch,List.mem_append_right _ member⟩

end Ptx.Scalar.Parallel.Control
