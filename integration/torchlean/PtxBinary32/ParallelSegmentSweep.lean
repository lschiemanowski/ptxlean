import PtxBinary32.ParallelSegment

/-! Finite sweeps execute one ordinary instruction segment per lane. Barrier
rounds remain separate actual executions, never implicit phase transitions. -/
namespace Ptx.Scalar.Parallel

def NoSync (code : List Instr) : Prop := ∀ resource, Instr.sync resource ∉ code

private theorem scalar_frame (s : State n) (t : Fin n) (space : Option Space) (i : Scalar.Instr) :
    (scalarStep none t space i s).state.site=s.site ∧
      ∀ u, u≠t → (scalarStep none t space i s).state.lanes u=s.lanes u := by
  cases ev : Scalar.eval none i {(s.lanes t).scalar with memory := arena s space} <;>
    cases space with
    | none => simp [scalarStep,ev,setLane,Function.update] <;> grind
    | some space => cases space <;> simp [scalarStep,ev,setLane,Function.update] <;> grind

private theorem dispatch_frame (step : Dispatch cfg none t i s out) (ordinary : ∀ r, i≠.sync r) :
    out.state.site=s.site ∧ ∀ u, u≠t → out.state.lanes u=s.lanes u := by
  cases step with
  | localStep => exact scalar_frame _ _ _ _
  | memory => exact scalar_frame _ _ _ _
  | binary32 _ => exact ⟨rfl,fun u hu => by simp [setLane,Function.update,hu]⟩
  | exit => exact ⟨rfl,fun u hu => by simp [setLane,Function.update,hu]⟩
  | sync => exact False.elim (ordinary _ rfl)

theorem ConcreteSegment.frame_extra (segment : ConcreteSegment cfg t code s events final) (ordinary : NoSync code) :
    final.site=s.site ∧ ∀ u, u≠t → final.lanes u=s.lanes u := by
  induction segment with
  | nil => exact ⟨rfl,fun _ _ => rfl⟩
  | @cons i current out restCode restEvents last step pc live barrier rest ih =>
    have head := dispatch_frame step (by intro r eq; apply ordinary r; simp [eq])
    have tail := ih (by intro r mem; apply ordinary r; simp [mem])
    exact ⟨tail.1.trans head.1,fun u hu => (tail.2 u hu).trans (head.2 u hu)⟩

/-- Any lane can execute its segment at a common entry site; the witness runs
all lanes once, retaining a concrete fetched prefix for each construction. -/
theorem segment_sweep {cfg : Config n} {program code : List Instr} {start : State n}
    (ordinary : NoSync code) (pc : Nat) (generation : Nat)
    (pcs : ∀ t, (start.lanes t).scalar.pc=pc) (live : ∀ t, (start.lanes t).halted=false)
    (barrier : start.barrier=Barrier.reset generation) (site : start.site=none)
    (fetch : Fetches program pc code) (eligible : Mixed.Eligible cfg.target)
    (construct : ∀ {events state}, ConcreteRuns cfg program start events state →
      ∀ t, (state.lanes t).scalar.pc=pc →
        ∃ next final, ConcreteSegment cfg t code state next final) :
    ∃ events final, ConcreteRuns cfg program start events final ∧
      (∀ t, (final.lanes t).scalar.pc=pc+code.length ∧ (final.lanes t).halted=false) ∧
      final.barrier=Barrier.reset generation ∧ final.site=none := by
  have sweep : ∀ count, count≤n → ∃ events state,
      ConcreteRuns cfg program start events state ∧
      (∀ t : Fin n, (state.lanes t).scalar.pc=pc+(if t.val<count then code.length else 0)) ∧
      (∀ t, (state.lanes t).halted=false) ∧ state.barrier=Barrier.reset generation ∧ state.site=none := by
    intro count bound
    induction count with
    | zero => exact ⟨[],start,.nil,by simpa using pcs,live,barrier,site⟩
    | succ count ih =>
      obtain ⟨events,state,run,positions,lives,reset,site⟩ := ih (by omega)
      let t : Fin n := ⟨count,by omega⟩
      have atPC : (state.lanes t).scalar.pc=pc := by simp [positions,t]
      obtain ⟨next,final,segment⟩ := construct run t atPC
      have frame := segment.frame
      have extra := segment.frame_extra ordinary
      have tail := segment.compile (by rw [atPC]; exact fetch) (lives t)
        (by simp [reset,Barrier.reset]) eligible
      refine ⟨events++next,final,concrete_runs_append run tail,?_,?_,frame.2.2.trans reset,extra.1.trans site⟩
      · intro u
        by_cases same : u=t
        · subst u; simpa [t,atPC] using frame.1
        · rw [extra.2 u same,positions]
          have ne : u.val≠count := fun h => same (Fin.ext h)
          have eq : u.val<count+1 ↔ u.val<count := by omega
          simp [eq]
      · intro u
        by_cases same : u=t
        · subst u; exact frame.2.1.trans (lives t)
        · rw [extra.2 u same]; exact lives u
  obtain ⟨events,final,run,pcs,live,rest⟩ := sweep n (by rfl)
  exact ⟨events,final,run,fun t => ⟨by simpa [t.isLt] using pcs t,live t⟩,rest⟩

/-- A finite exit sweep retains the fetched exits, rather than marking lanes
halted outside the instruction semantics. -/
theorem exit_sweep {cfg : Config n} {program : List Instr} {start : State n}
    (pc generation : Nat) (pcs : ∀ t, (start.lanes t).scalar.pc=pc)
    (live : ∀ t, (start.lanes t).halted=false) (barrier : start.barrier=Barrier.reset generation)
    (fetch : program[pc]?=some .exit) (eligible : Mixed.Eligible cfg.target) :
    ∃ events final, ConcreteRuns cfg program start events final ∧ ∀ t, (final.lanes t).halted=true := by
  have sweep : ∀ count, count≤n → ∃ events state, ConcreteRuns cfg program start events state ∧
      (∀ t, (state.lanes t).scalar.pc=pc) ∧
      (∀ t : Fin n, (state.lanes t).halted=decide (t.val<count)) ∧ state.barrier=Barrier.reset generation := by
    intro count bound
    induction count with
    | zero => exact ⟨[],start,.nil,pcs,by simpa using live,barrier⟩
    | succ count ih =>
      obtain ⟨events,state,run,positions,halted,reset⟩ := ih (by omega)
      let t : Fin n := ⟨count,by omega⟩
      let out := Reference.dispatch cfg t .exit state
      have step : Step cfg program none t state out := by
        refine ⟨eligible,?_⟩
        have live : (state.lanes t).halted=false := by simp [halted,t]
        simp only [live,reset,Barrier.reset,Bool.false_eq_true,ite_false,positions,fetch]
        exact Dispatch.exit
      have one := ConcreteRuns.cons step ConcreteRuns.nil
      refine ⟨events++out.events, out.state,concrete_runs_append run (by simpa using one),?_,?_,reset⟩
      · intro u
        by_cases same : u=t
        · subst u; simpa [out,Reference.dispatch,setLane] using positions t
        · simpa [out,Reference.dispatch,setLane,Function.update,same] using positions u
      · intro u
        by_cases same : u=t
        · subst u; simp [out,Reference.dispatch,setLane,t]
        · have ne : u.val≠count := fun h => same (Fin.ext h)
          have eq : u.val<count+1 ↔ u.val<count := by omega
          simp [out,Reference.dispatch,setLane,Function.update,same,halted,eq]
  obtain ⟨events,final,run,_,halted,_⟩ := sweep n (by rfl)
  exact ⟨events,final,run,fun t => by simp [halted,t.isLt]⟩

end Ptx.Scalar.Parallel
