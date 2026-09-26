import PtxBinary32.GridUnflatten
import PtxBinary32.PointwiseLaunch

/-! Pointwise grid correspondence reuses the actual all-thread memory graph only
after proving instruction-level flattening. No per-CTA execution is assumed. -/
namespace Ptx.Scalar.Parallel.GridPointwise

abbrev Layout (groups n : Nat) := Pointwise.Layout (groups*n)

def initial (l : Layout groups n) (global : List Word) (seeds : Fin (groups*n) → Scalar.State) : Grid.State groups n :=
  ⟨global,fun g => ⟨fun t => ⟨Pointwise.seed l seeds (Grid.flatThread g t),false⟩,[],Barrier.reset 0,none⟩⟩

theorem initial_flatten (l : Layout groups n) (global : List Word) (seeds : Fin (groups*n) → Scalar.State) :
    Grid.flatten (initial l global seeds)=Pointwise.initial l global [] seeds := by
  unfold Grid.flatten initial Pointwise.initial
  congr 1
  funext t
  simp only [Grid.flatThread,Prod.mk.eta,Equiv.apply_symm_apply]

theorem initial_idle (l : Layout groups n) (global : List Word) (seeds : Fin (groups*n) → Scalar.State) :
    Grid.IdleBarriers (initial l global seeds) := fun _ => rfl

theorem program_global (op : Pointwise.Op) : ∀ i ∈ Pointwise.program op, Grid.GlobalOnly i := by
  intro i member
  cases op <;> simp [Pointwise.program,Pointwise.body] at member
  all_goals repeat' (first | (rcases member with rfl | member) | (subst i; trivial))
  all_goals trivial

theorem candidate_run (op : Pointwise.Op) (l : Layout groups n) (global : List Word)
    (seeds : Fin (groups*n) → Scalar.State) (cfg : Grid.Config n)
    (target : cfg.target=⟨94,70⟩) (positive : 0<groups*n)
    {events : List (Grid.Event groups n)} {final : Grid.State groups n}
    (run : Grid.Runs cfg (Pointwise.program op) (initial l global seeds) events final) :
    Runs (Pointwise.config positive) (Pointwise.program op) (Pointwise.initial l global [] seeds)
      (Grid.flatEvents events) (Grid.flatten final) := by
  have flat := Grid.flatten_run (show (Pointwise.config positive).target=cfg.target from target.symm)
    run (program_global op) (initial_idle l global seeds)
  rw [initial_flatten] at flat
  exact flat

/-- The one combined graph has unique global thread identities and actual global
locations. There are no scratch accesses or barriers in these instruction lists. -/
def Admitted (op : Pointwise.Op) (l : Layout groups n) (global : List Word)
    (seeds : Fin (groups*n) → Scalar.State) (cfg : Grid.Config n) (target : cfg.target=⟨94,70⟩)
    (positive : 0<groups*n) {events : List (Grid.Event groups n)} {final : Grid.State groups n}
    (run : Grid.Runs cfg (Pointwise.program op) (initial l global seeds) events final) : Prop :=
  ∃ source co, Pointwise.Admitted op l global [] seeds (candidate_run op l global seeds cfg target positive run) source co

theorem completed (op : Pointwise.Op) (l : Layout groups n) (global : List Word)
    (seeds : Fin (groups*n) → Scalar.State) (cfg : Grid.Config n) (target : cfg.target=⟨94,70⟩)
    (positive : 0<groups*n) {events : List (Grid.Event groups n)} {final : Grid.State groups n}
    (run : Grid.Runs cfg (Pointwise.program op) (initial l global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true)
    (admitted : Admitted op l global seeds cfg target positive run) :
    (∀ t, ∃ value, final.global[l.output t]?=some value ∧ Pointwise.Result op global[l.left t]! global[l.right t]! value) ∧
    (∀ i, i<l.prefixWords → final.global[i]?=global[i]?) ∧ final.global.length=global.length ∧
    (∀ event ∈ events, Grid.AccessSafe (initial l global seeds) event) := by
  obtain ⟨source,co,valid⟩ := admitted
  have flat := candidate_run op l global seeds cfg target positive run
  have done : ∀ t, ((Grid.flatten final).lanes t).halted=true := by
    intro t; exact halted _ _
  have result := Pointwise.completed op l global [] seeds flat done source co valid
  exact ⟨result.1,result.2.1,result.2.2.1,Grid.runs_access_safe run⟩

/-- Nonvacuity under storage bounds, with no assumptions on numerical values. -/
theorem admitted_exists (op : Pointwise.Op) (l : Layout groups n) (global : List Word)
    (seeds : Fin (groups*n) → Scalar.State) (cfg : Grid.Config n) (target : cfg.target=⟨94,70⟩)
    (positive : 0<groups*n) (size : l.prefixWords+groups*n≤global.length) :
    ∃ events final, ∃ run : Grid.Runs cfg (Pointwise.program op) (initial l global seeds) events final,
      (∀ g t, ((final.blocks g).lanes t).halted=true) ∧ Admitted op l global seeds cfg target positive run := by
  obtain ⟨events,final,run,halted,source,co,valid⟩ := Pointwise.admitted_exists op l global [] seeds positive size
  have original := run
  rw [← initial_flatten l global seeds] at run
  obtain ⟨gridEvents,gridFinal,gridRun,traceEq,stateEq⟩ := Grid.reflect_run cfg
    (show (Pointwise.config positive).target=cfg.target from target.symm) run (program_global op) (initial_idle l global seeds)
  refine ⟨gridEvents,gridFinal,gridRun,?_,?_⟩
  · intro g t
    have h := halted (Grid.flatThread g t)
    rw [← stateEq,Grid.flatten_lane] at h
    exact h
  · unfold Admitted Pointwise.Admitted
    cases traceEq
    cases stateEq
    exact ⟨source,co,valid⟩

end Ptx.Scalar.Parallel.GridPointwise
