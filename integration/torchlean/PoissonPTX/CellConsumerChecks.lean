import PoissonPTX.CellConsumerOutput
import PoissonPTX.CellMiddleNumericChecks

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks
open Ptx CellMiddle Symbolic
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
attribute [local irreducible] Witness.result

def schedule : List (Fin 32) := (List.finRange 32).flatMap fun t =>
  List.replicate (if t.val<4 then (body 2).length+1 else 1) t

def candidate : Option (Outcome 32) :=
  execute Witness.cfg (program 2) (fun _ _ => 0) schedule Witness.result.state

theorem successful : candidate.isSome=true := by decide +kernel

def result : Outcome 32 := candidate.getD ⟨Witness.result.state,[]⟩
theorem executed : candidate=some result := by
  have h := successful
  cases he : candidate with
  | none => simp [he] at h
  | some out => simp [result,he]

attribute [local irreducible] result

theorem tail_run : Runs Witness.cfg (program 2) Witness.result.state result.events result.state :=
  execute_sound executed

theorem finished : ∀ t, (result.state.lanes t).pc=(program 2).length := by decide +kernel

theorem whole_run : Runs Witness.cfg (program 2) Witness.start (Witness.result.events++result.events) result.state :=
  combined Witness.candidate_run tail_run

theorem zero_words : ZeroSources.Zero (Witness.result.events++result.events) := by
  intro thread access member
  rcases List.mem_append.mp member with early|late
  · exact Numeric.Checks.zero_words thread access early
  · exact ZeroSources.execute_zero_reads executed thread access late
      (tail_readonly (by decide) (by decide) tail_run Witness.finished.2 thread access late)

theorem compatible : Visibility.Compatible (fun _ _ => 0) (Witness.result.events++result.events)
    (ZeroSources.source (Witness.result.events++result.events)) := ZeroSources.compatible zero_words

theorem performed : Visibility.Performed (Witness.result.events++result.events)
    (ZeroSources.source (Witness.result.events++result.events)) := ZeroSources.performed whole_run

/-- The numerical theorem has a completed source-constrained execution with all
32 participants, including 28 padding lanes. It is not arbitrary-input existence. -/
theorem correspondence (i j : Fin 2) :
    decode ((result.state.lanes ⟨i.val*2+j.val,by have := i.isLt; have := j.isLt; omega⟩).regs 11)=
      Spec.get2 (localAction
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 0)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 64)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .global 128)
        (Numeric.initialTensor 2 (fun _ => 0) (fun _ _ => 0) .shared 0)) i j :=
  completed_arithmetic Numeric.Checks.launch (by decide) (by decide) Witness.candidate_run Witness.finished.2
    tail_run compatible performed _ i j rfl (finished _)

/-- A changed arithmetic join fails the exact symbolic numerical certificate. -/
theorem wrong_join_rejected : number (atPC .values
    ((program 2).set ((program 2).length-1) (.data (.fp .sub 11 (.reg 8) (.reg 9))))
    (Numeric.seed 2 0) (program 2).length 11)≠some (expected 2 0) := by decide +kernel

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks
