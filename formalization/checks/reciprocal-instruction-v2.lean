import PtxBinary32.ReciprocalInstruction

/-! Coordinator-owned checks revised after replay: explicit instruction arguments
avoid elaborator timeouts; every proposition is unchanged from frozen v1. They exercise the
specified unary instruction, not hardware conformance or full kernel execution. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Ptx.ReciprocalInstructionAcceptance
open Scalar
abbrev I := Scalar.Reciprocal.Instr
abbrev E := Scalar.Reciprocal.Occurrence

example (g : Guard) (d : Nat) (a : Operand32) :
    Scalar.Reciprocal.Text.decode ⟨g, "rcp.rn.f32", [.word (.reg d), .word a]⟩ =
      .ok (⟨g, d, a⟩ : I) := rfl
example (g : Guard) (d : Nat) (a : Operand32) :
    Scalar.Reciprocal.Text.encode (⟨g, d, a⟩ : I) =
      ⟨g, "rcp.rn.f32", [.word (.reg d), .word a]⟩ := rfl
example : Scalar.Reciprocal.Text.supportedMnemonic "rcp.rn.f32" = true := rfl
example : (["rcp.f32", "rcp.approx.f32", "rcp.rz.f32", "rcp.rm.f32", "rcp.rp.f32",
    "rcp.rn.ftz.f32", "rcp.rn.f64", "rcp.rn.f32x2", "rcp.u32"].map
      fun name => Scalar.Reciprocal.Text.decode
        ⟨.always, name, [.word (.reg 0), .word (.reg 1)]⟩) =
    (["rcp.f32", "rcp.approx.f32", "rcp.rz.f32", "rcp.rm.f32", "rcp.rp.f32",
    "rcp.rn.ftz.f32", "rcp.rn.f64", "rcp.rn.f32x2", "rcp.u32"].map
      fun name => Except.error (Text.DecodeError.unsupportedMnemonic name)) := by decide
example : Scalar.Reciprocal.Text.decode
    ⟨.always, "rcp.rn.f32", [.word (.imm 0), .word (.reg 1)]⟩ =
    .error (.invalidOperands "rcp.rn.f32") := rfl
example : Scalar.Reciprocal.Text.decode
    ⟨.always, "rcp.rn.f32", [.word (.reg 0)]⟩ =
    .error (.invalidOperands "rcp.rn.f32") := rfl
example : Scalar.Reciprocal.Text.decode
    ⟨.always, "rcp.rn.f32", [.word (.reg 0), .address (.reg 1)]⟩ =
    .error (.invalidOperands "rcp.rn.f32") := rfl
example : Scalar.Reciprocal.Text.decode
    ⟨.always, "rcp.rn.f32", [.word (.reg 0), .word (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "rcp.rn.f32") := rfl

example (s : State) :
    Scalar.Reciprocal.occurrence s (⟨.pred 5 false, 3, .reg 3⟩ : I) true =
      (⟨s.pc, ⟨.pred 5 false, 3, .reg 3⟩, true,
        [.predicate 5, .word 3], [.word 3], none⟩ : E) := rfl
example (s : State) :
    Scalar.Reciprocal.occurrence s (⟨.pred 5 true, 3, .imm 0⟩ : I) false =
      (⟨s.pc, ⟨.pred 5 true, 3, .imm 0⟩, false,
        [.predicate 5], [], none⟩ : E) := rfl

-- All encoded cases, including overflow, subnormal output, and NaN freedom,
-- must be retained by the instruction rather than just by its numeric provider.
example (s : State) (input output : Word)
    (result : Ptx.Binary32.Reciprocal.Results input output) :
    Scalar.Reciprocal.Eval (⟨.always, 2, .imm input⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 output}
      (Scalar.Reciprocal.occurrence s ⟨.always, 2, .imm input⟩ true) :=
  .executed rfl result
example : Ptx.Binary32.Reciprocal.Results 0x40400000 0x3eaaaaab ∧
    Ptx.Binary32.Reciprocal.Results 0x80000000 0xff800000 ∧
    Ptx.Binary32.Reciprocal.Results 0xff800000 0x80000000 ∧
    Ptx.Binary32.Reciprocal.Results 0x7f7fffff 0x00200000 ∧
    Ptx.Binary32.Reciprocal.Results 1 0x7f800000 ∧
    Ptx.Binary32.Reciprocal.Results 0x7fc00000 0x7fc00017 ∧
    ¬ Ptx.Binary32.Reciprocal.Results 0x40000000 0x3f800000 := by decide

-- Destination aliases the source, and operands are taken from the pre-state.
example (s : State) (value : s.regs 3 = 0x40000000) :
    Scalar.Reciprocal.Eval (⟨.always, 3, .reg 3⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 3 0x3f000000}
      (Scalar.Reciprocal.occurrence s ⟨.always, 3, .reg 3⟩ true) := by
  apply Scalar.Reciprocal.Eval.executed rfl
  change Ptx.Binary32.Reciprocal.Results (s.regs 3) 0x3f000000
  rw [value]
  decide
example (s next : State) (e : E) (d : Nat)
    (h : Scalar.Reciprocal.Eval (⟨.always, d, .reg d⟩ : I) s next e) :
    Ptx.Binary32.Reciprocal.Results (s.regs d) (next.regs d) :=
  Scalar.Reciprocal.eval_destination (⟨.always, d, .reg d⟩ : I) s next e h rfl

example (s : State) (h : s.preds 7 = true) :
    Scalar.Reciprocal.Eval (⟨.pred 7 false, 0, .imm 0x7fc00000⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Reciprocal.occurrence s ⟨.pred 7 false, 0, .imm 0x7fc00000⟩ false) := by
  apply Scalar.Reciprocal.Eval.skipped
  simp [Guard.eval, h]
example (s : State) (h : s.preds 7 = false) :
    Scalar.Reciprocal.Eval (⟨.pred 7 true, 0, .imm 0⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Reciprocal.occurrence s ⟨.pred 7 true, 0, .imm 0⟩ false) := by
  apply Scalar.Reciprocal.Eval.skipped
  simp [Guard.eval, h]

example (s : State) (pc : s.pc = 1) :
    Scalar.Reciprocal.Step ⟨94, 20⟩
      [⟨.always, 8, .imm 0⟩, ⟨.always, 2, .imm 0x40000000⟩] s
      {s with pc := s.pc+1, regs := update s.regs 2 0x3f000000}
      (Scalar.Reciprocal.occurrence s ⟨.always, 2, .imm 0x40000000⟩ true) := by
  refine ⟨by unfold Scalar.Reciprocal.SupportedTarget; decide, ?_⟩
  refine ⟨⟨.always, 2, .imm 0x40000000⟩, ?_, ?_⟩
  · simp [pc]
  · apply Scalar.Reciprocal.Eval.executed rfl
    change Ptx.Binary32.Reciprocal.Results 0x40000000 0x3f000000
    decide

example (i : I) (s next : State) (e : E) (enabled : i.guard.eval s = true) :
    Scalar.Reciprocal.Eval i s next e ↔ ∃ value,
      Ptx.Binary32.Reciprocal.Results (i.source.eval s) value ∧
      next = {s with pc := s.pc+1, regs := update s.regs i.destination value} ∧
      e = Scalar.Reciprocal.occurrence s i true :=
  Scalar.Reciprocal.eval_true_iff i s next e enabled
example (i : I) (s next : State) (e : E) (disabled : i.guard.eval s = false) :
    Scalar.Reciprocal.Eval i s next e ↔ next = {s with pc := s.pc+1} ∧
      e = Scalar.Reciprocal.occurrence s i false :=
  Scalar.Reciprocal.eval_false_iff i s next e disabled
example (i : I) (s next : State) (e : E) (h : Scalar.Reciprocal.Eval i s next e) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds :=
  Scalar.Reciprocal.eval_frame i s next e h
example (i : I) (s next : State) (e : E) (other : Nat)
    (h : Scalar.Reciprocal.Eval i s next e) (different : other ≠ i.destination) :
    next.regs other = s.regs other := Scalar.Reciprocal.eval_other i s next e other h different
example (i : I) (s next : State) (e : E) (h : Scalar.Reciprocal.Eval i s next e) :
    e = Scalar.Reciprocal.occurrence s i (i.guard.eval s) :=
  Scalar.Reciprocal.eval_event i s next e h
example (i : I) (s : State) : ∃ next e, Scalar.Reciprocal.Eval i s next e :=
  Scalar.Reciprocal.eval_exists i s
example (target : Target) (program : List I) (s next : State) (e : E)
    (h : Scalar.Reciprocal.Step target program s next e) :
    Scalar.Reciprocal.SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      e.instruction = i ∧ Scalar.Reciprocal.Eval i s next e :=
  Scalar.Reciprocal.step_origin target program s next e h
example (target : Target) (program : List I) (s : State) (i : I)
    (supported : Scalar.Reciprocal.SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next e, Scalar.Reciprocal.Step target program s next e :=
  Scalar.Reciprocal.step_exists target program s i supported fetch
example (target : Target) (s next : State) (e : E) :
    ¬ Scalar.Reciprocal.Step target [] s next e :=
  Scalar.Reciprocal.step_no_fetch target [] s next e (by simp)
example (target : Target) (i : I) (s next : State) (e : E) (pc : s.pc = 2) :
    ¬ Scalar.Reciprocal.Step target [i] s next e :=
  Scalar.Reciprocal.step_no_fetch target [i] s next e (by simp [pc])
example (program : List I) (s next : State) (e : E) :
    ¬ Scalar.Reciprocal.Step ⟨94, 19⟩ program s next e :=
  Scalar.Reciprocal.step_unsupported_target _ program s next e (by
    unfold Scalar.Reciprocal.SupportedTarget; decide)
example (program : List I) (s next : State) (e : E) :
    ¬ Scalar.Reciprocal.Step ⟨95, 90⟩ program s next e :=
  Scalar.Reciprocal.step_unsupported_target _ program s next e (by
    unfold Scalar.Reciprocal.SupportedTarget; decide)
example (i : I) : Scalar.Reciprocal.Text.decode (Scalar.Reciprocal.Text.encode i) = .ok i :=
  Scalar.Reciprocal.Text.decode_encode i
example (s : Text.Statement) (i : I) :
    Scalar.Reciprocal.Text.decode s = .ok i ↔ s = Scalar.Reciprocal.Text.encode i :=
  Scalar.Reciprocal.Text.decode_iff s i

-- No expected result is assumed: numeric correctness is derived from Eval.
example (s next : State) (e : E) (d : Nat) (x : ℝ)
    (h : Scalar.Reciprocal.Eval (⟨.always, d, .reg d⟩ : I) s next e)
    (input : Ptx.Binary32.finiteReal (s.regs d) = some x)
    (nonzero : x ≠ 0) (range : |1/x| ≤ Ptx.Binary32.Bounds.maxFinite) :
    Ptx.Binary32.finiteReal (next.regs d) = some (TorchLean.Floats.round32 (1/x)) :=
  Ptx.Binary32.Reciprocal.results_real _ _ x input nonzero range
    (Scalar.Reciprocal.eval_destination (⟨.always, d, .reg d⟩ : I) s next e h rfl)
end Ptx.ReciprocalInstructionAcceptance
