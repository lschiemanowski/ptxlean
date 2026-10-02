import PoissonPTX.Relocate

namespace PtxTorchLean.Poisson.PTX.Relocate

/-- Recover the local instruction effect from an execution at a relocated PC. -/
theorem eval_back (step : PTX.Eval op (scalar offset s) t) :
    ∃ localState, t=scalar offset localState ∧ PTX.Eval op s localState := by
  cases step with
  | mov => refine ⟨_,?_,.mov⟩; simp
  | mul32 => refine ⟨_,?_,.mul32⟩; simp
  | add32 => refine ⟨_,?_,.add32⟩; simp
  | add64 => refine ⟨_,?_,.add64⟩; simp
  | wide8 => refine ⟨_,?_,.wide8⟩; simp
  | load64 valid => refine ⟨_,?_,.load64 (by simpa using valid)⟩; simp
  | store64 valid => refine ⟨_,?_,.store64 (by simpa using valid)⟩; simp
  | fp allowed => refine ⟨_,?_,.fp (by simpa using allowed)⟩; simp

/-- The chosen load bits are retained in both directions. -/
theorem data_back (step : Concurrent.Data op (scalar offset s) t observed) :
    ∃ localState localAccess,
      t=scalar offset localState ∧ observed=localAccess.map (access offset) ∧
      Concurrent.Data op s localState localAccess := by
  cases step with
  | ordinary plain he =>
    obtain ⟨localState,same,he⟩ := eval_back he
    exact ⟨localState,none,same,rfl,.ordinary plain he⟩
  | load valid =>
    rename_i sp dst addr word
    refine ⟨_,_,?_,?_,Concurrent.Data.load (word:=word) (by simpa using valid)⟩
    · simp
    · simp [access]
  | store valid =>
    refine ⟨_,_,?_,?_,.store (by simpa using valid)⟩
    · simp
    · simp [access]

theorem scalar_injective : Function.Injective (scalar offset) := by
  intro s t h
  cases s; cases t
  simpa [scalar,PTX.State.mk.injEq] using h

theorem core_injective : Function.Injective (core (n:=n) offset) := by
  intro s t h
  have lanes := congrArg Concurrent.State.lanes h
  have barrier := congrArg Concurrent.State.barrier h
  have site := congrArg Concurrent.State.site h
  have sameLanes : s.lanes=t.lanes := by
    funext u
    exact scalar_injective (congrFun lanes u)
  have sameSite : s.site=t.site := by
    cases hs : s.site <;> cases ht : t.site <;> simp_all [core]
  cases s; cases t
  simp_all [core]

/-- Every relocated dispatch is an image of a local dispatch; relocation does
not merely construct a convenient subset of executions. -/
theorem dispatch_back (step : Concurrent.Dispatch cfg thread (instruction offset i) (core offset s) out) :
    ∃ localOut, out=outcome offset localOut ∧ Concurrent.Dispatch cfg thread i s localOut := by
  cases i with
  | data op =>
    cases step with
    | data hd =>
      obtain ⟨next,record,same,observed,localStep⟩ := data_back hd
      refine ⟨_,?_,Concurrent.Dispatch.data localStep⟩
      simp [outcome,same,observed,event,List.map_map,Function.comp_def,Option.toList_map]
  | skip active target =>
    cases step
    refine ⟨_,?_,Concurrent.Dispatch.skip⟩
    by_cases live : thread.val<active <;> simp [outcome,core_setLane,core_lane,scalar,live,Nat.add_right_comm]
  | sync resource =>
    cases step
    exact ⟨_,synchronize cfg s thread resource,Concurrent.Dispatch.sync⟩

end PtxTorchLean.Poisson.PTX.Relocate
