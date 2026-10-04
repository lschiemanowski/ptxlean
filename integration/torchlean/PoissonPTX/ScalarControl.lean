import PoissonPTX.ScalarDeterministic

namespace PtxTorchLean.Poisson.PTX.Scalar.Control

/-- Pure register/predicate instructions used by the coefficient guards. -/
def supported : Instr → Bool
  | .base (.compare ..) => true
  | i => Scalar.ordinary i

def apply (ctx : Kernel.Context) (i : Instr) (s : Flow.State) : Flow.State :=
  match i with | .base op => Flow.simple ctx op s | _ => Scalar.simple i s

def fold (ctx : Kernel.Context) : List Instr → Flow.State → Flow.State
  | [],s => s
  | i::code,s => fold ctx code (apply ctx i s)

theorem step (supported : Control.supported i=true) : Eval ctx i s (apply ctx i s) := by
  cases i with
  | base op =>
    cases op <;> simp_all [Control.supported,Scalar.ordinary]
    exact .base (.simple (by intro op h; cases h))
  | _ => exact .simple supported

theorem running (supported : Control.supported i=true) : (apply ctx i s).halted=s.halted := by
  cases i with
  | base op => cases op <;> simp_all [Control.supported,Scalar.ordinary,apply,Flow.simple,Flow.next]
  | _ =>
    simp_all [Control.supported,Scalar.ordinary,apply,Scalar.simple,Flow.next]
    all_goals split <;> rfl

theorem plain (supported : Control.supported i=true) : noFP i=true := by
  cases i with
  | base op => cases op <;> simp_all [Control.supported,Scalar.ordinary,noFP,Flow.noFP]
  | _ => simp_all [Control.supported,Scalar.ordinary,noFP]

theorem trace (plain : ∀ i∈code, supported i=true) (alive : s.halted=false) :
    Sequence ctx code s (fold ctx code s) := by
  induction code generalizing s with
  | nil => exact .nil
  | cons i code ih =>
    exact .cons alive (step (plain i (by simp)))
      (ih (fun j member => plain j (by simp [member])) ((running (plain i (by simp))).trans alive))

theorem unique (actual : Sequence ctx code s t) (plain : ∀ i∈code, supported i=true)
    (alive : s.halted=false) : t=fold ctx code s :=
  sequence_unique actual (trace plain alive) (fun i member => Control.plain (plain i member))

end PtxTorchLean.Poisson.PTX.Scalar.Control
