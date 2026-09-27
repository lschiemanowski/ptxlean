import PtxBinary32.ExponentialInstruction

/-! Independent coordinator acceptance driver, calibrated in full before dispatch
against a separate reference fixture and compiling semantic mutants. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Ptx.ExponentialInstructionAcceptance
open Scalar
abbrev I := Scalar.Exponential.Instr
abbrev E := Scalar.Exponential.Occurrence

example (g : Guard) (d : Nat) (a : Operand32) :
    Scalar.Exponential.Text.decode ⟨g, "ex2.approx.f32", [.word (.reg d), .word a]⟩ =
      .ok (⟨g, d, a⟩ : I) := rfl
example (g : Guard) (d : Nat) (a : Operand32) :
    Scalar.Exponential.Text.encode (⟨g, d, a⟩ : I) =
      ⟨g, "ex2.approx.f32", [.word (.reg d), .word a]⟩ := rfl
example : Scalar.Exponential.Text.supportedMnemonic "ex2.approx.f32" = true := rfl
example : (["ex2.f32", "ex2.rn.f32", "ex2.approx.ftz.f32", "ex2.approx.f64", "ex2.u32"].map
      fun name => Scalar.Exponential.Text.decode
        ⟨.always, name, [.word (.reg 0), .word (.reg 1)]⟩) =
    (["ex2.f32", "ex2.rn.f32", "ex2.approx.ftz.f32", "ex2.approx.f64", "ex2.u32"].map
      fun name => Except.error (Text.DecodeError.unsupportedMnemonic name)) := by decide
example : Scalar.Exponential.Text.decode
    ⟨.always, "ex2.approx.f32", [.word (.imm 0), .word (.reg 1)]⟩ =
    .error (.invalidOperands "ex2.approx.f32") := rfl
example : Scalar.Exponential.Text.decode
    ⟨.always, "ex2.approx.f32", [.word (.reg 0)]⟩ =
    .error (.invalidOperands "ex2.approx.f32") := rfl
example : Scalar.Exponential.Text.decode
    ⟨.always, "ex2.approx.f32", [.word (.reg 0), .address (.reg 1)]⟩ =
    .error (.invalidOperands "ex2.approx.f32") := rfl
example : Scalar.Exponential.Text.decode
    ⟨.always, "ex2.approx.f32", [.word (.reg 0), .word (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "ex2.approx.f32") := rfl

example (s : State) :
    Scalar.Exponential.occurrence s (⟨.pred 5 false, 3, .reg 3⟩ : I) true =
      (⟨s.pc, ⟨.pred 5 false, 3, .reg 3⟩, true,
        [.predicate 5, .word 3], [.word 3], none⟩ : E) := rfl
example (s : State) :
    Scalar.Exponential.occurrence s (⟨.pred 5 true, 3, .imm 0⟩ : I) false =
      (⟨s.pc, ⟨.pred 5 true, 3, .imm 0⟩, false,
        [.predicate 5], [], none⟩ : E) := rfl

-- All supported encoded cases, including exact special values and NaN freedom,
-- must be retained by the instruction rather than just by its numeric provider.
example (s : State) (input output : Word)
    (result : Ptx.Binary32.Exponential.Results input output) :
    Scalar.Exponential.Eval (⟨.always, 2, .imm input⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 output}
      (Scalar.Exponential.occurrence s ⟨.always, 2, .imm input⟩ true) :=
  .executed rfl result
-- The exact special cases cannot be replaced by the finite neighborhood.
example (output : Word) : Ptx.Binary32.Exponential.Results 0xff800000 output ↔ output = 0 :=
  Ptx.Binary32.Exponential.neg_inf_iff output
example (output : Word) : Ptx.Binary32.Exponential.Results 0x7f800000 output ↔ output = 0x7f800000 :=
  Ptx.Binary32.Exponential.pos_inf_iff output
example : Ptx.Binary32.Exponential.Results 0x7fc00000 0x7fc00017 :=
  (Ptx.Binary32.Exponential.nan_iff _ _ (by decide)).mpr (by decide)
example (input output : Word) (h : Ptx.Binary32.finiteReal input = some 0) :
    Ptx.Binary32.Exponential.Results input output ↔ output = 0x3f800000 :=
  Ptx.Binary32.Exponential.zero_iff input output h

-- Destination aliases the source, and operands are taken from the pre-state.
example (s : State) (value : s.regs 3 = 0xff800000) :
    Scalar.Exponential.Eval (⟨.always, 3, .reg 3⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 3 0}
      (Scalar.Exponential.occurrence s ⟨.always, 3, .reg 3⟩ true) := by
  apply Scalar.Exponential.Eval.executed rfl
  change Ptx.Binary32.Exponential.Results (s.regs 3) 0
  rw [value]
  exact (Ptx.Binary32.Exponential.neg_inf_iff _).mpr rfl
example (s next : State) (e : E) (d : Nat)
    (h : Scalar.Exponential.Eval (⟨.always, d, .reg d⟩ : I) s next e) :
    Ptx.Binary32.Exponential.Results (s.regs d) (next.regs d) :=
  Scalar.Exponential.eval_destination (⟨.always, d, .reg d⟩ : I) s next e h rfl

example (s : State) (h : s.preds 7 = true) :
    Scalar.Exponential.Eval (⟨.pred 7 false, 0, .imm 0x7fc00000⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Exponential.occurrence s ⟨.pred 7 false, 0, .imm 0x7fc00000⟩ false) := by
  apply Scalar.Exponential.Eval.skipped
  simp [Guard.eval, h]
example (s : State) (h : s.preds 7 = false) :
    Scalar.Exponential.Eval (⟨.pred 7 true, 0, .imm 0⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Exponential.occurrence s ⟨.pred 7 true, 0, .imm 0⟩ false) := by
  apply Scalar.Exponential.Eval.skipped
  simp [Guard.eval, h]

example (s : State) (pc : s.pc = 1) :
    Scalar.Exponential.Step ⟨94, 20⟩
      [⟨.always, 8, .imm 0⟩, ⟨.always, 2, .imm 0xff800000⟩] s
      {s with pc := s.pc+1, regs := update s.regs 2 0}
      (Scalar.Exponential.occurrence s ⟨.always, 2, .imm 0xff800000⟩ true) := by
  refine ⟨by unfold Scalar.Exponential.SupportedTarget; decide, ?_⟩
  refine ⟨⟨.always, 2, .imm 0xff800000⟩, ?_, ?_⟩
  · simp [pc]
  · apply Scalar.Exponential.Eval.executed rfl
    change Ptx.Binary32.Exponential.Results 0xff800000 0
    exact (Ptx.Binary32.Exponential.neg_inf_iff _).mpr rfl

example (i : I) (s next : State) (e : E) (enabled : i.guard.eval s = true) :
    Scalar.Exponential.Eval i s next e ↔ ∃ value,
      Ptx.Binary32.Exponential.Results (i.source.eval s) value ∧
      next = {s with pc := s.pc+1, regs := update s.regs i.destination value} ∧
      e = Scalar.Exponential.occurrence s i true :=
  Scalar.Exponential.eval_true_iff i s next e enabled
example (i : I) (s next : State) (e : E) (disabled : i.guard.eval s = false) :
    Scalar.Exponential.Eval i s next e ↔ next = {s with pc := s.pc+1} ∧
      e = Scalar.Exponential.occurrence s i false :=
  Scalar.Exponential.eval_false_iff i s next e disabled
example (i : I) (s next : State) (e : E) (h : Scalar.Exponential.Eval i s next e) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds :=
  Scalar.Exponential.eval_frame i s next e h
example (i : I) (s next : State) (e : E) (other : Nat)
    (h : Scalar.Exponential.Eval i s next e) (different : other ≠ i.destination) :
    next.regs other = s.regs other := Scalar.Exponential.eval_other i s next e other h different
example (i : I) (s next : State) (e : E) (h : Scalar.Exponential.Eval i s next e) :
    e = Scalar.Exponential.occurrence s i (i.guard.eval s) :=
  Scalar.Exponential.eval_event i s next e h
example (i : I) (s : State)
    (domain : i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s)) :
    ∃ next e, Scalar.Exponential.Eval i s next e := Scalar.Exponential.eval_exists i s domain
example (i : I) (s : State) : (∃ next e, Scalar.Exponential.Eval i s next e) ↔
    i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s) :=
  Scalar.Exponential.eval_exists_iff i s
example (target : Target) (program : List I) (s next : State) (e : E)
    (h : Scalar.Exponential.Step target program s next e) :
    Scalar.Exponential.SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      e.instruction = i ∧ Scalar.Exponential.Eval i s next e :=
  Scalar.Exponential.step_origin target program s next e h
example (target : Target) (program : List I) (s : State) (i : I)
    (supported : Scalar.Exponential.SupportedTarget target) (fetch : program[s.pc]? = some i)
    (domain : i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s)) :
    ∃ next e, Scalar.Exponential.Step target program s next e :=
  Scalar.Exponential.step_exists target program s i supported fetch domain
example (target : Target) (s next : State) (e : E) :
    ¬ Scalar.Exponential.Step target [] s next e :=
  Scalar.Exponential.step_no_fetch target [] s next e (by simp)
example (target : Target) (i : I) (s next : State) (e : E) (pc : s.pc = 2) :
    ¬ Scalar.Exponential.Step target [i] s next e :=
  Scalar.Exponential.step_no_fetch target [i] s next e (by simp [pc])
example (program : List I) (s next : State) (e : E) :
    ¬ Scalar.Exponential.Step ⟨94, 19⟩ program s next e :=
  Scalar.Exponential.step_unsupported_target _ program s next e (by
    unfold Scalar.Exponential.SupportedTarget; decide)
example (program : List I) (s next : State) (e : E) :
    ¬ Scalar.Exponential.Step ⟨95, 90⟩ program s next e :=
  Scalar.Exponential.step_unsupported_target _ program s next e (by
    unfold Scalar.Exponential.SupportedTarget; decide)
example (i : I) : Scalar.Exponential.Text.decode (Scalar.Exponential.Text.encode i) = .ok i :=
  Scalar.Exponential.Text.decode_encode i
example (s : Text.Statement) (i : I) :
    Scalar.Exponential.Text.decode s = .ok i ↔ s = Scalar.Exponential.Text.encode i :=
  Scalar.Exponential.Text.decode_iff s i

-- All finite accuracy is derived from actual execution, not a correct-answer premise.
example (s next : State) (e : E) (d : Nat) (x : ℝ)
    (h : Scalar.Exponential.Eval (⟨.always, d, .reg d⟩ : I) s next e)
    (input : Ptx.Binary32.finiteReal (s.regs d) = some x) :
    ∃ z : ℝ, Ptx.Binary32.finiteReal (next.regs d) = some z ∧
      |z-(2:ℝ)^x| ≤ 5/(2:ℝ)^24 :=
  Ptx.Binary32.Exponential.finite_error _ _ x input
    (Scalar.Exponential.eval_destination (⟨.always, d, .reg d⟩ : I) s next e h rfl)

-- A positive finite operand is legal PTX but outside this fragment's enabled domain.
example (s next : State) (e : E) :
    ¬ Scalar.Exponential.Eval (⟨.always,0,.imm 0x3f800000⟩ : I) s next e := by
  intro h
  have domain := (Scalar.Exponential.eval_exists_iff (⟨.always,0,.imm 0x3f800000⟩ : I) s).mp ⟨next,e,h⟩
  have unsupported := Ptx.Binary32.Exponential.positive_unsupported _ 1 Ptx.Binary32.Approximate.one_real (by norm_num)
  rcases domain with disabled | supported
  · contradiction
  · exact unsupported supported
example (s : State) (h : s.preds 7 = false) :
    Scalar.Exponential.Eval (⟨.pred 7 true,0,.imm 0x3f800000⟩ : I) s
      {s with pc := s.pc+1} (Scalar.Exponential.occurrence s ⟨.pred 7 true,0,.imm 0x3f800000⟩ false) := by
  apply Scalar.Exponential.Eval.skipped
  simp [Guard.eval,h]

-- Both enabled predicate polarities, including same-register source/destination.
example (s : State) (p d : Nat) (expected : Bool) (h : s.preds p = expected)
    (output : Word) (result : Ptx.Binary32.Exponential.Results (s.regs d) output) :
    Scalar.Exponential.Eval (⟨.pred p expected,d,.reg d⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs d output}
      (Scalar.Exponential.occurrence s ⟨.pred p expected,d,.reg d⟩ true) := by
  exact @Scalar.Exponential.Eval.executed (⟨.pred p expected,d,.reg d⟩ : I) s output
    (by simp [Guard.eval,h]) result

-- No narrowing to a chosen result: every member of either finite ULP policy executes.
example (s : State) (input output : Word) (x : ℝ)
    (value : Ptx.Binary32.finiteReal input = some x) (negative : x < 0)
    (result : Ptx.Binary32.ConservativeULP.Results ((2:ℝ)^x) output) :
    Scalar.Exponential.Eval (⟨.always,2,.imm input⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 output}
      (Scalar.Exponential.occurrence s ⟨.always,2,.imm input⟩ true) :=
  .executed rfl ((Ptx.Binary32.Exponential.negative_iff input output x value negative).mpr result)

example (s next : State) (e : E) (input : Word)
    (zero : Ptx.Binary32.finiteReal input = some 0)
    (h : Scalar.Exponential.Eval (⟨.always,0,.imm input⟩ : I) s next e) :
    next.regs 0 = 0x3f800000 :=
  (Ptx.Binary32.Exponential.zero_iff input _ zero).mp
    (Scalar.Exponential.eval_destination (⟨.always,0,.imm input⟩ : I) s next e h rfl)
end Ptx.ExponentialInstructionAcceptance
