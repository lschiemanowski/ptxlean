import PtxBinary32.ParallelConcrete
import PtxBinary32.ParallelWriteValues

/-! Uniform groups fetch one common program against one actual global array.
Scratch, lanes and barriers are private. Memory admission is separate. -/
namespace Ptx.Scalar.Parallel.Grid
structure Local (n : Nat) where
  lanes : Fin n → Lane
  shared : List Word
  barrier : Barrier.State n
  site : Option Nat
structure State (groups n : Nat) where
  global : List Word
  blocks : Fin groups → Local n
structure Config (n : Nat) where
  target : Target
  positive : 0<n
  threads : n≤1024

def Config.group (cfg : Config n) (g : Fin groups) : Parallel.Config n := ⟨cfg.target,g.val,cfg.positive⟩
def view (s : State groups n) (g : Fin groups) : Parallel.State n :=
  ⟨(s.blocks g).lanes,s.global,(s.blocks g).shared,(s.blocks g).barrier,(s.blocks g).site⟩
def localOf (s : Parallel.State n) : Local n := ⟨s.lanes,s.shared,s.barrier,s.site⟩
def install (s : State groups n) (g : Fin groups) (next : Parallel.State n) : State groups n :=
  ⟨next.global,Function.update s.blocks g (localOf next)⟩
abbrev Event (groups n : Nat) := Fin groups × Parallel.Event n
def tag (g : Fin groups) (events : List (Parallel.Event n)) : List (Event groups n) := events.map (fun e => (g,e))
inductive Step (cfg : Config n) (program : List Instr) : State groups n → List (Event groups n) → State groups n → Prop
  | issue (g : Fin groups) (thread : Fin n) (candidate : Option Word) (out : Outcome n)
      (step : Parallel.Step (cfg.group g) program candidate thread (view s g) out) :
      Step cfg program s (tag g out.events) (install s g out.state)
inductive Runs (cfg : Config n) (program : List Instr) : State groups n → List (Event groups n) → State groups n → Prop
  | nil : Runs cfg program s [] s
  | cons : Step cfg program s events middle → Runs cfg program middle rest final → Runs cfg program s (events++rest) final

@[simp] theorem view_install_same (s : State groups n) (g : Fin groups) (next : Parallel.State n) :
    view (install s g next) g=next := by simp [view,install,localOf]
@[simp] theorem install_local_other (s : State groups n) (g h : Fin groups) (next : Parallel.State n)
    (different : h≠g) : (install s g next).blocks h=s.blocks h := by simp [install,different]
/-- Other groups retain private state and observe the actual updated global array. -/
theorem view_install_other (s : State groups n) (g h : Fin groups) (next : Parallel.State n)
    (different : h≠g) : view (install s g next) h={view s h with global := next.global} := by simp [view,install,different]
theorem step_exists (cfg : Config n) (program : List Instr) (s : State groups n)
    (g : Fin groups) (thread : Fin n) (candidate : Option Word) (eligible : Mixed.Eligible cfg.target) :
    ∃ events final, Step cfg program s events final := by
  obtain ⟨out,step⟩ := Parallel.step_exists (cfg.group g) program candidate thread (view s g) eligible
  exact ⟨_,_,.issue g thread candidate out step⟩
theorem step_lengths (step : Step cfg program s events final) :
    final.global.length=s.global.length ∧ ∀ g, (final.blocks g).shared.length=(s.blocks g).shared.length := by
  cases step with
  | issue g t candidate out step =>
    have safe := Parallel.step_safe step
    refine ⟨safe.1,?_⟩
    intro h
    by_cases eq : h=g
    · subst h; simpa [install,localOf,view] using safe.2.1
    · simp [install,eq]
theorem runs_lengths (run : Runs cfg program s events final) :
    final.global.length=s.global.length ∧ ∀ g, (final.blocks g).shared.length=(s.blocks g).shared.length := by
  induction run with
  | nil => exact ⟨rfl,fun _ => rfl⟩
  | cons step _ ih =>
    have lengths := step_lengths step
    exact ⟨ih.1.trans lengths.1,fun g => (ih.2 g).trans (lengths.2 g)⟩
def AccessSafe (s : State groups n) (event : Event groups n) : Prop := Parallel.AccessSafe (view s event.1) event.2

theorem step_access_safe (step : Step cfg program s events final) : ∀ event ∈ events, AccessSafe s event := by
  cases step with
  | issue g t candidate out step =>
    intro event member
    change event ∈ out.events.map (fun e => (g,e)) at member
    obtain ⟨e,he,eq⟩ := List.mem_map.mp member
    subst event
    exact (Parallel.step_safe step).2.2 e he
theorem access_safe_of_lengths {s next : State groups n}
    (global : next.global.length=s.global.length)
    (shared : ∀ g, (next.blocks g).shared.length=(s.blocks g).shared.length)
    (event : Event groups n) (safe : AccessSafe next event) : AccessSafe s event := by
  rcases event with ⟨g,e⟩
  cases e <;> simp only [AccessSafe,Parallel.AccessSafe] at *
  case scalar t space occ =>
    intro effect memory
    have valid := safe effect memory
    cases space with
    | none => exact valid
    | some space => cases space <;> simpa [Parallel.arena,view,Scalar.ValidAddress,global,shared] using valid
  all_goals trivial

theorem runs_access_safe (run : Runs cfg program s events final) : ∀ event ∈ events, AccessSafe s event := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    intro event member
    rcases List.mem_append.mp member with first | rest
    · exact step_access_safe step event first
    · have lengths := step_lengths step
      exact access_safe_of_lengths lengths.1 lengths.2 event (ih event rest)
theorem step_aligned (step : Step cfg program s events final)
    (aligned : ∀ g, Parallel.Aligned (view s g)) : ∀ g, Parallel.Aligned (view final g) := by
  cases step with
  | issue g t candidate out step =>
    intro h
    by_cases eq : h=g
    · subst h; rw [view_install_same]; exact Parallel.step_aligned step (aligned g)
    · rw [view_install_other _ _ _ _ eq]; exact aligned h
theorem runs_aligned (run : Runs cfg program s events final)
    (aligned : ∀ g, Parallel.Aligned (view s g)) : ∀ g, Parallel.Aligned (view final g) := by
  induction run with
  | nil => exact aligned
  | cons step _ ih => exact ih (step_aligned step aligned)
theorem runs_append (first : Runs cfg program s left middle) (second : Runs cfg program middle right final) :
    Runs cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => simpa [List.append_assoc] using Runs.cons step (ih second)
/-- Embeds an actual group execution with the other groups idle; not an admission theorem. -/
theorem embed_run (g : Fin groups) (run : Parallel.Runs (cfg.group g) program (view s g) events final) :
    Runs cfg program s (tag g events) (install s g final) := by
  generalize startEq : view s g=start at run
  induction run generalizing s with
  | nil =>
    rw [← startEq]
    have same : install s g (view s g)=s := by
      cases s with
      | mk global blocks => simp [install,view,localOf]
    rw [same]; exact .nil
  | @cons candidate thread start out rest final step run ih =>
    rw [← startEq] at step
    have tail := ih (s := install s g out.state) (by simp)
    have same : install (install s g out.state) g final=install s g final := by simp [install,Function.update_idem]
    rw [same] at tail
    simpa [tag,List.map_append] using Runs.cons (.issue g thread candidate out step) tail
end Ptx.Scalar.Parallel.Grid
