import PoissonPTX.ScalarExecution

namespace PtxTorchLean.Poisson.PTX.Scalar

/-- Exact state uniqueness is used only where no rounded-result encoding is
chosen. Floating operations retain their relational result freedom. -/
def noFP : Instr → Bool
  | .base i => Flow.noFP i
  | .sqrt .. | .max .. | .predFP .. => false
  | _ => true

def sequence (ctx : Kernel.Context) : List Instr → Flow.State → Option Flow.State
  | [],s => some s
  | i::code,s => if s.halted then none else eval ctx i s >>= sequence ctx code

theorem sequence_sound (h : sequence ctx code s=some t) : Sequence ctx code s t := by
  induction code generalizing s with
  | nil => cases h; exact .nil
  | cons i code ih =>
    simp only [sequence] at h
    split at h
    · simp at h
    · rename_i running
      change ((eval ctx i s).bind (sequence ctx code))=some t at h
      obtain ⟨middle,first,rest⟩ := Option.bind_eq_some_iff.mp h
      exact .cons (by cases he : s.halted <;> simp_all) (eval_sound first) (ih rest)

theorem eval_complete (step : Eval ctx i s t) (plain : noFP i=true) : eval ctx i s=some t := by
  cases step with
  | base actual => exact Flow.eval_complete actual plain
  | simple ordinary => cases i <;> simp_all [noFP,eval,Scalar.ordinary]
  | store32 valid => simp [eval,valid]
  | _ => simp [noFP] at plain

theorem eval_unique (one : Eval ctx i s t) (two : Eval ctx i s u) (plain : noFP i=true) : t=u :=
  Option.some.inj ((eval_complete one plain).symm.trans (eval_complete two plain))

theorem sequence_unique (one : Sequence ctx code s t) (two : Sequence ctx code s u)
    (plain : ∀ i∈code, noFP i=true) : t=u := by
  induction one generalizing u with
  | nil => cases two; rfl
  | cons running step rest ih =>
    cases two with
    | cons alive actual tail =>
      have same := eval_unique step actual (plain _ (by simp))
      subst_vars
      exact ih tail (fun i member => plain i (by simp[member]))

end PtxTorchLean.Poisson.PTX.Scalar
