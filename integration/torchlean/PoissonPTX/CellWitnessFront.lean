import PoissonPTX.CellMiddleExists
import PoissonPTX.CellTailProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
open CellMiddle

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem front_prefix (lo : 2≤width) (hi : width≤5) :
    (WithOutput.front width).take (Checks.program width).length=Checks.program width := by
  interval_cases width <;> decide +kernel

theorem front_fetch_before (lo : 2≤width) (hi : width≤5) (before : pc<(Checks.program width).length) :
    (WithOutput.front width)[pc]?=(program width)[pc]? := by
  have same := congrArg (fun code : List Instr => code[pc]?) (front_prefix lo hi)
  rw [program,List.getElem?_append_left before]
  simpa only [List.getElem?_take,ite_eq_left before] using same

/-- A run ending at a forward guard has not executed that guard. Thus changing
only code at/after that point leaves its actual prior steps and records intact. -/
theorem run_before_guard {old runtime : List Instr} {active : Nat}
    (run : Runs cfg old start events final) (forward : Forward old)
    (guard : old[cut]?=some (.skip active target)) (later : cut<target)
    (done : ∀ t, (final.lanes t).pc≤cut)
    (same : ∀ pc, pc<cut → runtime[pc]?=old[pc]?) : Runs cfg runtime start events final := by
  induction run with
  | nil => exact .nil
  | @cons selected state out rest final step tail ih =>
    have upper := (runs_pc_mono tail forward selected).trans (done selected)
    have lower := step_pc_mono step forward selected
    have before : (state.lanes selected).pc<cut := by
      by_contra wrong
      have atCut : (state.lanes selected).pc=cut := by omega
      obtain ⟨fresh,i,fetch,dispatch⟩ := step
      rw [atCut,guard] at fetch
      cases Option.some.inj fetch
      cases dispatch
      simp only [setLane,Function.update_self] at upper
      split at upper <;> omega
    obtain ⟨fresh,i,fetch,dispatch⟩ := step
    exact .cons ⟨fresh,i,by rw [same _ before]; exact fetch,dispatch⟩ (ih done)

theorem middle_front (lo : 2≤width) (hi : width≤5)
    (run : Runs cfg (program width) start events final)
    (done : ∀ t, (final.lanes t).pc=startPC width 3) :
    Runs cfg (WithOutput.front width) start events final := by
  apply run_before_guard run (checked_forward (checked width lo hi)) (stage_guard (width:=width) 3)
    (by omega) (fun t => (done t).le)
  intro pc before
  exact front_fetch_before lo hi before

/-- Lift the same actual front steps; thread predicates and halt flags are
retained, and no auxiliary arithmetic state is added to the machine. -/
theorem lift_front {start : WithTail.State n} (run : Runs cfg front start.core events final)
    (running : ∀ t, start.halted t=false) :
    WithTail.Runs cfg ctx front tail start events {start with core:=final} := by
  generalize coreEq : start.core=core at run
  induction run generalizing start with
  | nil => cases start; cases coreEq; exact .nil
  | @cons selected state out rest final step later ih =>
    have actual : Concurrent.Step cfg front selected start.core out := coreEq ▸ step
    exact .cons (.front (running selected) actual) (ih running rfl)

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Witness
