import PtxBinary32.GridFlatten

/-! Reflection of global-only instruction executions into actual grid steps.
Together with flatten_run, this prevents flattening from inventing executions. -/
namespace Ptx.Scalar.Parallel.Grid

theorem dispatch_reflect {s : State groups n} {g : Fin groups} {t : Fin n}
    {localCfg : Parallel.Config n} {flatCfg : Parallel.Config (groups*n)}
    (step : Dispatch flatCfg candidate (flatThread g t) i (flatten s) flatOut) (only : GlobalOnly i) :
    ∃ out, Dispatch localCfg candidate t i (view s g) out ∧ flatOutcome s g out=flatOut := by
  cases step with
  | localStep => exact ⟨_,.localStep,scalar_flatten _ _ _ _ _ _ (by simp)⟩
  | @memory space i =>
    cases space with
    | shared => contradiction
    | global => exact ⟨_,.memory,scalar_flatten _ _ _ _ _ _ (by simp)⟩
  | binary32 ev =>
    rename_i i next event
    have mapped : Scalar.Binary32.Eval i ((view s g).lanes t).scalar next event := by simpa using ev
    refine ⟨_,.binary32 mapped,?_⟩
    simp [flatOutcome,flatEvent,flatten_install_lane]
  | exit => exact ⟨_,.exit,by simp [flatOutcome,flatEvent,flatten_install_lane]⟩
  | sync => contradiction

theorem local_step_reflect {s : State groups n} {g : Fin groups} {t : Fin n}
    {localCfg : Parallel.Config n} {flatCfg : Parallel.Config (groups*n)}
    (target : flatCfg.target=localCfg.target)
    (step : Parallel.Step flatCfg program candidate (flatThread g t) (flatten s) flatOut)
    (only : ∀ i ∈ program, GlobalOnly i) (idle : IdleBarriers s) :
    ∃ out, Parallel.Step localCfg program candidate t (view s g) out ∧ flatOutcome s g out=flatOut := by
  have eligible : Mixed.Eligible localCfg.target := target ▸ step.1
  have h := step.2
  have reset : (view s g).barrier.arrived t=false := by simp [view,idle g,Barrier.reset]
  simp only [flatten_lane] at h
  by_cases halted : ((s.blocks g).lanes t).halted=true
  · simp only [halted,ite_true] at h
    subst flatOut
    exact ⟨⟨view s g,.halted,[]⟩,⟨eligible,by simp [view,halted]⟩,by simp [flatOutcome]⟩
  · simp only [halted,ite_false,flatten,Barrier.reset,Bool.false_eq_true] at h
    change (match program[((s.blocks g).lanes t).scalar.pc]? with | none => _ | some i => _) at h
    cases fetch : program[((s.blocks g).lanes t).scalar.pc]? with
    | none =>
      simp only [fetch] at h
      subst flatOut
      refine ⟨⟨view s g,.invalidPC,[]⟩,⟨eligible,?_⟩,by simp [flatOutcome,flatten,Barrier.reset]⟩
      simp [view_lanes,halted,reset,fetch]
    | some i =>
      simp only [fetch] at h
      obtain ⟨out,dispatch,eq⟩ := dispatch_reflect (localCfg := localCfg) h (only i (List.mem_of_getElem? fetch))
      refine ⟨out,⟨eligible,?_⟩,eq⟩
      simpa [view_lanes,halted,reset,fetch] using dispatch

theorem reflect_run {s : State groups n} {flatCfg : Parallel.Config (groups*n)} (cfg : Config n)
    (target : flatCfg.target=cfg.target)
    (run : Parallel.Runs flatCfg program (flatten s) events final)
    (only : ∀ i ∈ program, GlobalOnly i) (idle : IdleBarriers s) :
    ∃ gridEvents gridFinal, Runs cfg program s gridEvents gridFinal ∧
      flatEvents gridEvents=events ∧ flatten gridFinal=final := by
  generalize startEq : flatten s=start at run
  induction run generalizing s with
  | nil => exact ⟨[],s,.nil,rfl,startEq⟩
  | @cons candidate thread start out rest final step tail ih =>
    obtain ⟨⟨g,t⟩,eq⟩ := finProdFinEquiv.surjective thread
    subst thread
    rw [← startEq] at step
    obtain ⟨localOut,localStep,mapped⟩ := local_step_reflect (localCfg := cfg.group g) target step only idle
    have gridStep := Step.issue g t candidate localOut localStep
    have stateEq : flatten (install s g localOut.state)=out.state := congrArg Outcome.state mapped
    obtain ⟨more,last,gridTail,traceEq,finalEq⟩ := ih (s := install s g localOut.state) (step_idle gridStep only idle) stateEq
    refine ⟨tag g localOut.events++more,last,.cons gridStep gridTail,?_,finalEq⟩
    have eventsEq : localOut.events.map (flatEvent g)=out.events := congrArg Outcome.events mapped
    simp only [flatEvents,List.map_append] at traceEq ⊢
    rw [traceEq]
    simp only [tag,List.map_map,Function.comp_def]
    rw [eventsEq]

end Ptx.Scalar.Parallel.Grid
