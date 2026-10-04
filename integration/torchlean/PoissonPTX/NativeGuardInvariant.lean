import PoissonPTX.NativeGuard

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard

variable {n : Nat} {s t : State n} {cfg : Config n} {program : List Instr}

/-- Another lane halfway through its guard cannot be advanced by a barrier:
that lane has not arrived. This is a protocol fact, not scheduler atomicity. -/
theorem pending_sync (s : Concurrent.State n) (selected owner : Fin n)
    (different : owner≠selected) (fresh : s.barrier.arrived selected=false)
    (missing : s.barrier.arrived owner=false) :
    (synchronize cfg s selected resource).state.lanes=s.lanes ∧
    (synchronize cfg s selected resource).state.barrier.arrived owner=false := by
  have incomplete : ¬Ptx.Barrier.Complete (Ptx.Barrier.mark s.barrier selected) := by
    intro h
    have seen := h owner
    simp [Ptx.Barrier.Waiting,Ptx.Barrier.mark,different,missing] at seen
  have requestThread : (barrierRequest cfg s selected resource).thread=selected := rfl
  by_cases key : (barrierRequest cfg s selected resource).key =
      Ptx.Barrier.key (barrierConfig cfg s selected) s.barrier
  all_goals simp only [synchronize,Ptx.Barrier.step,key,requestThread,fresh,
    Bool.false_eq_true,incomplete,↓reduceIte]
  · exact ⟨True.intro,by simpa only [Ptx.Barrier.mark,ite_eq_right (fun h => different h)] using missing⟩
  · exact ⟨True.intro,missing⟩

theorem preserved (actual : Step cfg program thread s events t) (ready : Ready program s)
    (keeps : Address.Keeps program 14) (counts : CountsFit program) (small : n≤2^32) :
    Ready program t := by
  have registers : ∀ u, ((t.core.lanes u).regs 14).toNat=u.val := by
    intro u
    rw [Address.runs_keeps (project_step actual ready) keeps u]
    exact ready.2 u
  refine ⟨?_,registers⟩
  intro owner pending
  cases actual with
  | compare fresh phase fetch =>
    by_cases same : owner=thread
    · subst owner
      refine ⟨fresh,_,_,fetch,?_⟩
      simpa only [compared,Function.update_self] using
        compare_value (ready.2 thread) small (counts _ _ _ fetch)
    · simpa [compared,Function.update,same] using
        ready.1 owner (by simpa [compared,Function.update,same] using pending)
  | branch fresh phase fetch =>
    have different : owner≠thread := by
      intro same; subst owner; simp [branched] at pending
    simpa [branched,setLane,Function.update,different] using
      ready.1 owner (by simpa [branched,Function.update,different] using pending)
  | data fresh phase fetch hd =>
    have different : owner≠thread := by
      intro same; subst owner; simp [phase] at pending
    simpa [setLane,Function.update,different] using ready.1 owner pending
  | @sync _ resource fresh phase fetch =>
    have different : owner≠thread := by
      intro same; subst owner; simp [phase] at pending
    obtain ⟨missing,count,target,found,flag⟩ := ready.1 owner pending
    have frame := pending_sync s.core thread owner different fresh missing (cfg:=cfg) (resource:=resource)
    exact ⟨frame.2,count,target,by simpa only [frame.1] using found,flag⟩

/-- Arbitrary schedules, including comparison/branch interleavings, project
to actual old-model runs. The initial predicate bits can be arbitrary. -/
theorem project (run : Runs cfg program s events t) (ready : Ready program s)
    (keeps : Address.Keeps program 14) (counts : CountsFit program) (small : n≤2^32) :
    Concurrent.Runs cfg program s.core events t.core ∧ Ready program t := by
  induction run with
  | nil => exact ⟨.nil,ready⟩
  | cons one rest ih =>
    have next := preserved one ready keeps counts small
    obtain ⟨later,finalReady⟩ := ih next
    exact ⟨runs_append (project_step one ready) later,finalReady⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard
