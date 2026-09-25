import Ptx.Shf32
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Shf32.Acceptance

example : ∀ (a b c : Word) ,
    compute .leftClamp a b c = (b <<< (min c.toNat 32)) ||| (a >>> (32 - (min c.toNat 32)))
  := @compute_leftClamp

example : ∀ (a b c : Word) ,
    compute .leftWrap a b c = (b <<< (c.toNat % 32)) ||| (a >>> (32 - (c.toNat % 32)))
  := @compute_leftWrap

example : ∀ (a b c : Word) ,
    compute .rightClamp a b c = (b <<< (32 - (min c.toNat 32))) ||| (a >>> (min c.toNat 32))
  := @compute_rightClamp

example : ∀ (a b c : Word) ,
    compute .rightWrap a b c = (b <<< (32 - (c.toNat % 32))) ||| (a >>> (c.toNat % 32))
  := @compute_rightWrap

example : ∀ (op : Operation) (words : Fin 3 → Word) (predicates : Fin 0 → Bool) (value : Word) ,
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2)
  := @results_iff

example : ∀ (i : Instr) , (lower i).operation = i.operation
  := @lower_operation

example : ∀ (i : Instr) ,
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 3) = i.first ∧ (lower i).words (⟨1, by decide⟩ : Fin 3) = i.second ∧ (lower i).words (⟨2, by decide⟩ : Fin 3) = i.control
  := @lower_fields

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) ,
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true
  := @eval_true_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) ,
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false
  := @eval_false_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) ,
    next.regs i.destination = result i s
  := @eval_destination

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) ,
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds
  := @eval_frame

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) ,
    next.regs other = s.regs other
  := @eval_other

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) ,
    event = occurrence s i (i.guard.eval s)
  := @eval_event

example : ∀ (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) ,
    next₁ = next₂ ∧ event₁ = event₂
  := @eval_deterministic

example : ∀ (i : Instr) (s : Scalar.State) , ∃ next event, Eval i s next event
  := @eval_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) ,
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event
  := @step_origin

example : ∀ (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) ,
    ∃ next event, Step target program s next event
  := @step_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) ,
    ¬ Step target program s next event
  := @step_no_fetch

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) ,
    ¬ Step target program s next event
  := @step_unsupported_target

example : ∀ (i : Instr) , Text.decode (Text.encode i) = .ok i
  := @Text.decode_encode

example : ∀ (statement : Scalar.Text.Statement) (i : Instr) ,
    Text.decode statement = .ok i ↔ statement = Text.encode i
  := @Text.decode_iff

end Ptx.Scalar.Shf32.Acceptance
