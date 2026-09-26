import PtxBinary32.GridExecution
import Mathlib.Logic.Equiv.Fin.Basic

/-! Flattening independent, global-only threads is a proof device. It does not
assert that a grid is one hardware CTA, or flatten barriers/shared storage. -/
namespace Ptx.Scalar.Parallel.Grid

def flatThread (g : Fin groups) (t : Fin n) : Fin (groups*n) := finProdFinEquiv (g,t)

@[simp] theorem product_div (g : Fin groups) (t : Fin n) : (finProdFinEquiv (g,t)).divNat=g :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g,t))
@[simp] theorem product_mod (g : Fin groups) (t : Fin n) : (finProdFinEquiv (g,t)).modNat=t :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (g,t))

def flatten (s : State groups n) : Parallel.State (groups*n) :=
  ⟨fun t => (s.blocks (finProdFinEquiv.symm t).1).lanes (finProdFinEquiv.symm t).2,
    s.global,[],Barrier.reset 0,none⟩

def flatEvent (g : Fin groups) : Parallel.Event n → Parallel.Event (groups*n)
  | .scalar t space occ => .scalar (flatThread g t) space occ
  | .binary32 t occ => .binary32 (flatThread g t) occ
  | .exit t pc => .exit (flatThread g t) pc
  | .barrier (.arrival key t) => .barrier (.arrival key (flatThread g t))
  | .barrier (.completion key) => .barrier (.completion key)

def flatEvents (events : List (Event groups n)) : List (Parallel.Event (groups*n)) :=
  events.map (fun e => flatEvent e.1 e.2)

@[simp] theorem flatten_global (s : State groups n) : (flatten s).global=s.global := rfl
@[simp] theorem view_global (s : State groups n) (g : Fin groups) : (view s g).global=s.global := rfl
@[simp] theorem view_lanes (s : State groups n) (g : Fin groups) : (view s g).lanes=(s.blocks g).lanes := rfl

@[simp] theorem flatten_lane (s : State groups n) (g : Fin groups) (t : Fin n) :
    (flatten s).lanes (flatThread g t)=(s.blocks g).lanes t := by
  change (s.blocks (finProdFinEquiv.symm (finProdFinEquiv (g,t))).1).lanes (finProdFinEquiv.symm (finProdFinEquiv (g,t))).2=_
  rw [Equiv.symm_apply_apply]

@[simp] theorem install_view (s : State groups n) (g : Fin groups) : install s g (view s g)=s := by
  cases s; simp [install,view,localOf]

theorem flatten_install_lane (s : State groups n) (g : Fin groups) (t : Fin n) (lane : Lane) :
    flatten (install s g (setLane (view s g) t lane))=setLane (flatten s) (flatThread g t) lane := by
  unfold flatten install setLane view localOf
  congr 1
  funext p
  obtain ⟨⟨h,u⟩,rfl⟩ := finProdFinEquiv.surjective p
  by_cases gh : h=g <;> by_cases tu : u=t
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals simp [flatThread,Function.update_apply,gh,tu,Prod.ext_iff]

/-- Only global loads/stores and non-memory scalar/FP operations are flattened. -/
def GlobalOnly : Instr → Prop
  | .memory .shared _ | .sync _ => False
  | _ => True

def IdleBarriers (s : State groups n) : Prop := ∀ g, (s.blocks g).barrier=Barrier.reset 0

@[simp] theorem flatten_install_global (s : State groups n) (g : Fin groups) (next : Parallel.State n) (memory : List Word) :
    flatten (install s g {next with global := memory})={flatten (install s g next) with global := memory} := rfl

def flatOutcome (s : State groups n) (g : Fin groups) (out : Outcome n) : Outcome (groups*n) :=
  ⟨flatten (install s g out.state),out.status,out.events.map (flatEvent g)⟩

theorem scalar_flatten (s : State groups n) (g : Fin groups) (t : Fin n) (candidate : Option Word)
    (space : Option Space) (i : Scalar.Instr) (globalOnly : space≠some .shared) :
    flatOutcome s g (scalarStep candidate t space i (view s g))=
      scalarStep candidate (flatThread g t) space i (flatten s) := by
  cases space with
  | none =>
    cases ev : Scalar.eval candidate i {(s.blocks g).lanes t |>.scalar with memory := []} <;>
      simp [scalarStep,flatOutcome,flatten_lane,Parallel.arena,ev,flatten_install_lane,flatEvent]
  | some space =>
    cases space with
    | shared => contradiction
    | global =>
      cases ev : Scalar.eval candidate i {(s.blocks g).lanes t |>.scalar with memory := s.global} <;>
        simp [scalarStep,flatOutcome,flatten_lane,Parallel.arena,ev,flatten_install_lane,flatEvent]

theorem dispatch_flatten {s : State groups n} {g : Fin groups} {t : Fin n}
    {localCfg : Parallel.Config n} {flatCfg : Parallel.Config (groups*n)}
    (step : Dispatch localCfg candidate t i (view s g) out) (only : GlobalOnly i) :
    Dispatch flatCfg candidate (flatThread g t) i (flatten s) (flatOutcome s g out) := by
  cases step with
  | localStep => rw [scalar_flatten _ _ _ _ _ _ (by simp)]; exact .localStep
  | @memory space i =>
    cases space with
    | shared => contradiction
    | global => rw [scalar_flatten _ _ _ _ _ _ (by simp)]; exact .memory
  | binary32 ev =>
    rename_i i next event
    have mapped : Scalar.Binary32.Eval i ((flatten s).lanes (flatThread g t)).scalar next event := by
      simpa using ev
    simpa [flatOutcome,flatEvent,flatten_install_lane] using (Dispatch.binary32 (cfg := flatCfg) (candidate := candidate) (thread := flatThread g t) mapped)
  | exit => simpa [flatOutcome,flatEvent,flatten_install_lane] using (Dispatch.exit (cfg := flatCfg) (candidate := candidate) (thread := flatThread g t) (s := flatten s))
  | sync => contradiction

private theorem scalar_barrier (s : Parallel.State n) (t : Fin n) (space : Option Space) (i : Scalar.Instr) (candidate : Option Word) :
    (scalarStep candidate t space i s).state.barrier=s.barrier := by
  cases ev : Scalar.eval candidate i {(s.lanes t).scalar with memory := arena s space} <;>
    cases space <;> simp [scalarStep,ev,setLane]
  all_goals split <;> rfl

theorem dispatch_barrier (step : Dispatch cfg candidate t i s out) (only : GlobalOnly i) :
    out.state.barrier=s.barrier := by
  cases step with
  | localStep => exact scalar_barrier _ _ _ _ _
  | memory => exact scalar_barrier _ _ _ _ _
  | binary32 _ | exit => rfl
  | sync => contradiction

theorem step_barrier (step : Parallel.Step cfg program candidate t s out)
    (only : ∀ i ∈ program, GlobalOnly i) : out.state.barrier=s.barrier := by
  have h := step.2
  split at h
  · subst out; rfl
  · split at h
    · subst out; rfl
    · split at h
      · subst out; rfl
      · exact dispatch_barrier h (only _ (List.mem_of_getElem? (by assumption)))

theorem step_idle (step : Step cfg program s events final)
    (only : ∀ i ∈ program, GlobalOnly i) (idle : IdleBarriers s) : IdleBarriers final := by
  cases step with
  | issue g t candidate out step =>
    intro h
    by_cases eq : h=g
    · subst h
      simpa [install,localOf,view] using (step_barrier step only).trans (idle g)
    · simpa [install,eq] using idle h

theorem local_step_flatten {s : State groups n} {g : Fin groups} {t : Fin n}
    {localCfg : Parallel.Config n} {flatCfg : Parallel.Config (groups*n)}
    (target : flatCfg.target=localCfg.target)
    (step : Parallel.Step localCfg program candidate t (view s g) out)
    (only : ∀ i ∈ program, GlobalOnly i) (idle : IdleBarriers s) :
    Parallel.Step flatCfg program candidate (flatThread g t) (flatten s) (flatOutcome s g out) := by
  refine ⟨target ▸ step.1,?_⟩
  have h := step.2
  have reset : (view s g).barrier.arrived t=false := by simp [view,idle g,Barrier.reset]
  simp only [view_lanes,reset,Bool.false_eq_true,ite_false] at h
  change (if ((flatten s).lanes (flatThread g t)).halted then _ else _)
  rw [flatten_lane]
  by_cases halted : ((s.blocks g).lanes t).halted=true
  · simp only [halted,ite_true] at h ⊢
    subst out
    simp [flatOutcome]
  · simp only [halted,ite_false] at h ⊢
    simp only [flatten,Barrier.reset,Bool.false_eq_true,ite_false]
    change (match program[((s.blocks g).lanes t).scalar.pc]? with | none => _ | some i => _)
    cases fetch : program[((s.blocks g).lanes t).scalar.pc]? with
    | none =>
      simp only [fetch] at h ⊢
      subst out; simp [flatOutcome,flatten,Barrier.reset]
    | some i =>
      simp only [fetch] at h ⊢
      exact dispatch_flatten h (only i (List.mem_of_getElem? fetch))

theorem flatten_run {s final : State groups n} {events : List (Event groups n)}
    {flatCfg : Parallel.Config (groups*n)} (target : flatCfg.target=cfg.target)
    (run : Runs cfg program s events final) (only : ∀ i ∈ program, GlobalOnly i) (idle : IdleBarriers s) :
    Parallel.Runs flatCfg program (flatten s) (flatEvents events) (flatten final) := by
  induction run with
  | nil => exact .nil
  | cons step tail ih =>
    have nextIdle := step_idle step only idle
    have next := ih nextIdle
    cases step with
    | issue g t candidate out step =>
      have mapped := local_step_flatten target step only idle
      simpa [flatEvents,tag,flatOutcome,List.map_append,List.map_map,Function.comp_def] using Parallel.Runs.cons mapped next

end Ptx.Scalar.Parallel.Grid
