import PtxBinary32.GridCompletion
import PtxBinary32.ParallelCoverage

/-! Actual instruction crossings and exits for any selected group. These facts
are recovered from grid execution, never supplied as a desired phase schedule. -/
namespace Ptx.Scalar.Parallel.Grid.Control
open Parallel.Control (Straight)

theorem step_pc_bound {s final : State groups n} {events : List (Event groups n)}
    (step : Step cfg program s events final) (straight : Straight program) (g : Fin groups) (t : Fin n) :
    ((final.blocks g).lanes t).scalar.pc≤((s.blocks g).lanes t).scalar.pc+1 := by
  cases step with
  | issue h u candidate out step =>
    by_cases same : g=h
    · subst h; simpa [install,localOf,view] using Parallel.Control.step_pc_bound step straight t
    · simp [install,same]

theorem crossing_step {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program)
    (g : Fin groups) (t : Fin n) (pc : Nat) (start : ((s.blocks g).lanes t).scalar.pc≤pc)
    (finish : pc<((final.blocks g).lanes t).scalar.pc) :
    ∃ before after middle out selected candidate,
      events=before++tag g out.events++after ∧ Runs cfg program s before middle ∧
      Parallel.Step (cfg.group g) program candidate selected (view middle g) out ∧
      Runs cfg program (install middle g out.state) after final ∧
      ((middle.blocks g).lanes t).scalar.pc=pc ∧ (out.state.lanes t).scalar.pc=pc+1 := by
  induction run with
  | nil => omega
  | @cons s added middle rest final step run ih =>
    by_cases passed : pc<((middle.blocks g).lanes t).scalar.pc
    · have bound := step_pc_bound step straight g t
      cases step with
      | issue h u candidate out step =>
        have same : g=h := by
          by_contra diff
          simp [install,diff] at passed
          omega
        subst h
        refine ⟨[],rest,s,out,u,candidate,by simp,.nil,step,run,by omega,?_⟩
        simpa [install,localOf] using (show (((install s g out.state).blocks g).lanes t).scalar.pc=pc+1 by omega)
    · obtain ⟨before,after,middle,next,u,c,trace,frontRun,cross,suffix,old,new⟩ := ih (by omega) finish
      exact ⟨added++before,after,middle,next,u,c,by simp [trace,List.append_assoc],Runs.cons step frontRun,cross,suffix,old,new⟩

theorem crossed_barrier_exists {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program)
    (aligned : ∀ g, Parallel.Aligned (view s g)) (g : Fin groups) (t : Fin n) (pc : Nat)
    (start : ((s.blocks g).lanes t).scalar.pc≤pc) (finish : pc<((final.blocks g).lanes t).scalar.pc)
    (fetch : program[pc]?=some (.sync resource)) :
    ∃ (c : Nat) (key : Barrier.Key), events[c]?=some (g,.barrier (.completion key)) ∧ key.site=pc := by
  obtain ⟨before,after,middle,out,u,candidate,trace,frontRun,step,_,old,new⟩ := crossing_step run straight g t pc start finish
  obtain ⟨key,site,member⟩ := Parallel.Control.barrier_crossing step ((Grid.runs_aligned frontRun aligned) g)
    (by change program[((middle.blocks g).lanes t).scalar.pc]?=_; rw [old]; exact fetch) (by change _=((middle.blocks g).lanes t).scalar.pc+1; omega)
  have present : (g,.barrier (.completion key)) ∈ events := by
    rw [trace]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,member,rfl⟩
  obtain ⟨c,bound,atC⟩ := List.mem_iff_getElem.mp present
  exact ⟨c,key,by simpa [bound] using atC,site.trans old⟩

theorem halted_exit_origin {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final) (straight : Straight program) (g : Fin groups) (t : Fin n)
    (live : ((s.blocks g).lanes t).halted=false) (halted : ((final.blocks g).lanes t).halted=true) :
    ∃ pc, program[pc]?=some .exit ∧ (g,.exit t pc) ∈ events := by
  induction run with
  | nil => simp [live] at halted
  | @cons s added middle rest final step run ih =>
    by_cases done : ((middle.blocks g).lanes t).halted=true
    · cases step with
      | issue h u candidate out step =>
        have same : g=h := by
          by_contra diff
          simp [install,diff,live] at done
        subst h
        have finalHalt : (out.state.lanes t).halted=true := by simpa [install,localOf] using done
        obtain ⟨pc,fetch,member⟩ := Parallel.Control.halted_exit_origin (Parallel.Runs.cons step Parallel.Runs.nil) straight t live finalHalt
        refine ⟨pc,fetch,List.mem_append_left _ ?_⟩
        apply List.mem_map.mpr
        exact ⟨_,by simpa using member,rfl⟩
    · obtain ⟨pc,fetch,member⟩ := ih (Bool.eq_false_iff.mpr done) halted
      exact ⟨pc,fetch,List.mem_append_right _ member⟩

end Ptx.Scalar.Parallel.Grid.Control
