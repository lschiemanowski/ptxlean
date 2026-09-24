import Ptx.Pure32
/-! Independent mechanism probes, not additional PTX instruction coverage. -/
namespace Ptx.Pure32Independent
open Ptx Ptx.Scalar Ptx.Scalar.Pure32
private def choices : Family Unit where
  wordArity := fun _ => 2
  predicateArity := fun _ => 1
  Results := fun _ ws ps value => value = ws 0 ∨ (ps 0 = true ∧ value = ws 1)
  inhabited := fun _ ws _ => ⟨ws 0, Or.inl rfl⟩
  Supported := fun target _ => target.isa = 94 ∧ target.sm ≥ 70
private def state : State := ⟨8, fun r => if r = 0 then 7 else 19,
  fun _ => 42, fun r => r = 2, [3,4]⟩
private def instruction : Pure32.Instr choices :=
  ⟨.pred 2 true, (), 0, fun x => if x.val = 0 then .reg 0 else .reg 1,
    fun _ => .reg 2 true⟩
example : Eval instruction state (write state 0 7) (occurrence state instruction true) :=
  .executed rfl (Or.inl rfl)
example : Eval instruction state (write state 0 19) (occurrence state instruction true) :=
  .executed rfl (Or.inr ⟨rfl,rfl⟩)
example : (occurrence state instruction true).reads = [.predicate 2,.word 0,.word 1,.predicate 2] := by decide
example : (occurrence state instruction false).reads = [.predicate 2] := rfl
example : (write state 0 19).memory = [3,4] ∧ (write state 0 19).regs 1 = 19 := by decide
example : ¬ Pure32.Step ⟨94,60⟩ [instruction] {state with pc := 0} state
    (occurrence state instruction false) := by
  apply step_unsupported (i := instruction) (by rfl)
  simp [choices]
end Ptx.Pure32Independent
