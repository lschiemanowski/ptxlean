import PoissonPTX.NativeGuardInvariant

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard

variable {n : Nat} {cfg : Config n} {program : List Instr}

theorem append (first : Runs cfg program s left middle) (second : Runs cfg program middle right final) :
    Runs cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons one rest ih => simpa only [List.append_assoc] using Runs.cons one (ih second)

/-- Each old guard expands into two actual steps. This constructor chooses
adjacent scheduling only as a witness; projection permits arbitrary schedules. -/
theorem lift_step {s : Concurrent.State n}
    (actual : Concurrent.Step cfg program thread s out)
    (lanes : ∀ u, ((s.lanes u).regs 14).toNat=u.val)
    (counts : CountsFit program) (small : n≤2^32) (flags : Fin n → Bool) :
    ∃ nextFlags, Runs cfg program (start s flags) out.events (start out.state nextFlags) := by
  obtain ⟨fresh,i,fetch,dispatch⟩ := actual
  cases dispatch with
  | data hd =>
    exact ⟨flags,by simpa [start] using Runs.cons (Step.data fresh rfl fetch hd) Runs.nil⟩
  | sync =>
    exact ⟨flags,by simpa [start] using Runs.cons (Step.sync fresh rfl fetch) Runs.nil⟩
  | @skip active target =>
    let nextFlags := Function.update flags thread (decide (active≤thread.val))
    have value := compare_value (lanes thread) small (counts _ _ _ fetch)
    have finish : branched (compared (start s flags) thread active) thread target =
        start (setLane s thread {s.lanes thread with
          pc:=if thread.val<active then (s.lanes thread).pc+1 else target}) nextFlags := by
      have phase : Function.update (Function.update (fun _ : Fin n => false) thread true) thread false =
          (fun _ => false) := by funext u; by_cases h : u=thread <;> simp [Function.update,h]
      simp only [branched,compared,start,Function.update_self,value,phase]
      by_cases h : active≤thread.val
      · simp [h,show ¬thread.val<active by omega,nextFlags]
      · simp [h,show thread.val<active by omega,nextFlags]
    refine ⟨nextFlags,?_⟩
    rw [← finish]
    exact .cons (.compare fresh rfl fetch) (.cons (.branch fresh (by simp [compared]) fetch) .nil)

theorem lift {s t : Concurrent.State n}
    (run : Concurrent.Runs cfg program s events t)
    (lanes : ∀ u, ((s.lanes u).regs 14).toNat=u.val)
    (keeps : Address.Keeps program 14) (counts : CountsFit program) (small : n≤2^32)
    (flags : Fin n → Bool) :
    ∃ nextFlags, Runs cfg program (start s flags) events (start t nextFlags) := by
  induction run generalizing flags with
  | nil => exact ⟨flags,.nil⟩
  | cons one rest ih =>
    obtain ⟨middleFlags,first⟩ := lift_step one lanes counts small flags
    have next (u : Fin n) := (congrArg BitVec.toNat (Address.step_keeps one keeps u)).trans (lanes u)
    obtain ⟨lastFlags,later⟩ := ih next middleFlags
    exact ⟨lastFlags,append first later⟩

end PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard
