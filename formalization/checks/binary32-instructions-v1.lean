import PtxBinary32.Instructions
import PtxBinary32Bounds

/- Coordinator-owned acceptance checks, independent of the worker's examples.
These concern the declared conservative result envelope, not GPU realizability. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Ptx.FPInstructionAcceptance

open Scalar
abbrev I := Scalar.Binary32.Instr
abbrev E := Scalar.Binary32.Occurrence

example (g : Guard) (d : Nat) (a b : Operand32) :
    Scalar.Binary32.Text.decode ⟨g, "add.rn.f32", [.word (.reg d), .word a, .word b]⟩ =
      .ok (⟨g, .add, d, a, b⟩ : I) := rfl
example (g : Guard) (d : Nat) (a b : Operand32) :
    Scalar.Binary32.Text.decode ⟨g, "mul.rn.f32", [.word (.reg d), .word a, .word b]⟩ =
      .ok (⟨g, .mul, d, a, b⟩ : I) := rfl

example (g : Guard) (d : Nat) (a b : Operand32) :
    Scalar.Binary32.Text.encode (⟨g, .add, d, a, b⟩ : I) =
      ⟨g, "add.rn.f32", [.word (.reg d), .word a, .word b]⟩ := rfl
example (g : Guard) (d : Nat) (a b : Operand32) :
    Scalar.Binary32.Text.encode (⟨g, .mul, d, a, b⟩ : I) =
      ⟨g, "mul.rn.f32", [.word (.reg d), .word a, .word b]⟩ := rfl

example : (["add.f32", "mul.f32", "add.rz.f32", "mul.rm.f32", "add.rp.f32",
    "add.rn.ftz.f32", "mul.rn.sat.f32", "add.rn.f64", "mul.rn.f32x2", "add.u32"].map
      fun spelling => Scalar.Binary32.Text.decode
        ⟨.pred 0 false, spelling, [.word (.reg 0), .word (.reg 1), .word (.imm 0)]⟩) =
    (["add.f32", "mul.f32", "add.rz.f32", "mul.rm.f32", "add.rp.f32",
    "add.rn.ftz.f32", "mul.rn.sat.f32", "add.rn.f64", "mul.rn.f32x2", "add.u32"].map
      fun spelling => Except.error (Text.DecodeError.unsupportedMnemonic spelling)) := by decide

example : Scalar.Binary32.Text.decode
    ⟨.always, "add.rn.f32", [.word (.imm 0), .word (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "add.rn.f32") := rfl
example : Scalar.Binary32.Text.decode
    ⟨.always, "mul.rn.f32", [.word (.reg 0), .word (.reg 1)]⟩ =
    .error (.invalidOperands "mul.rn.f32") := rfl
example : Scalar.Binary32.Text.decode
    ⟨.always, "mul.rn.f32", [.word (.reg 0), .address (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "mul.rn.f32") := rfl

example (s : State) :
    Scalar.Binary32.occurrence s (⟨.pred 5 false, .mul, 3, .reg 3, .reg 3⟩ : I) true =
      (⟨s.pc, ⟨.pred 5 false, .mul, 3, .reg 3, .reg 3⟩, true,
        [.predicate 5, .word 3, .word 3], [.word 3], none⟩ : E) := rfl
example (s : State) :
    Scalar.Binary32.occurrence s (⟨.pred 5 true, .add, 3, .reg 2, .imm 0⟩ : I) false =
      (⟨s.pc, ⟨.pred 5 true, .add, 3, .reg 2, .imm 0⟩, false,
        [.predicate 5], [], none⟩ : E) := rfl

-- Distinguish both arithmetic operations from integer arithmetic and from each other.
example (s : State) :
    Scalar.Binary32.Eval (⟨.always, .add, 2, .imm 0x3fc00000, .imm 0x40100000⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 0x40700000}
      (Scalar.Binary32.occurrence s ⟨.always, .add, 2, .imm 0x3fc00000, .imm 0x40100000⟩ true) := by
  apply Scalar.Binary32.Eval.executed rfl
  change Ptx.Binary32.Results .add 0x3fc00000 0x40100000 0x40700000
  unfold Ptx.Binary32.Results
  decide
example (s : State) :
    Scalar.Binary32.Eval (⟨.always, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 0x40580000}
      (Scalar.Binary32.occurrence s ⟨.always, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ true) := by
  apply Scalar.Binary32.Eval.executed rfl
  change Ptx.Binary32.Results .mul 0x3fc00000 0x40100000 0x40580000
  unfold Ptx.Binary32.Results
  decide

-- An alternative NaN payload must remain available in the envelope.
example (s : State) :
    Scalar.Binary32.Eval (⟨.always, .add, 0, .imm 0x7f800000, .imm 0xff800000⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 0 0x7fc00017}
      (Scalar.Binary32.occurrence s ⟨.always, .add, 0, .imm 0x7f800000, .imm 0xff800000⟩ true) := by
  apply Scalar.Binary32.Eval.executed rfl
  change Ptx.Binary32.Results .add 0x7f800000 0xff800000 0x7fc00017
  unfold Ptx.Binary32.Results
  decide

example : Scalar.Binary32.SupportedTarget ⟨94, 20⟩ := by
  unfold Scalar.Binary32.SupportedTarget
  decide
example : ¬ Scalar.Binary32.SupportedTarget ⟨94, 19⟩ := by
  unfold Scalar.Binary32.SupportedTarget
  decide
example : ¬ Scalar.Binary32.SupportedTarget ⟨95, 90⟩ := by
  unfold Scalar.Binary32.SupportedTarget
  decide

-- Guard-false evaluation is total even on exceptional operands and preserves data.
example (s : State) (h : s.preds 7 = true) :
    Scalar.Binary32.Eval (⟨.pred 7 false, .mul, 0, .imm 0x7f800000, .imm 0⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Binary32.occurrence s ⟨.pred 7 false, .mul, 0, .imm 0x7f800000, .imm 0⟩ false) := by
  apply Scalar.Binary32.Eval.skipped
  simp [Guard.eval, h]

-- Fetched occurrence must come from the actual nonzero program counter.
example (s : State) (pc : s.pc = 1) :
    Scalar.Binary32.Step ⟨94, 20⟩
      [⟨.always, .mul, 8, .imm 0, .imm 0⟩,
       ⟨.always, .add, 2, .imm 1, .imm 1⟩] s
      {s with pc := s.pc+1, regs := update s.regs 2 2}
      (Scalar.Binary32.occurrence s ⟨.always, .add, 2, .imm 1, .imm 1⟩ true) := by
  refine ⟨by unfold Scalar.Binary32.SupportedTarget; decide, ?_⟩
  refine ⟨⟨.always, .add, 2, .imm 1, .imm 1⟩, ?_, ?_⟩
  · simp [pc]
  · apply Scalar.Binary32.Eval.executed rfl
    change Ptx.Binary32.Results .add 1 1 2
    unfold Ptx.Binary32.Results
    decide

-- A signed zero result remains encoded even though its real interpretation is zero.
example (s : State) :
    Scalar.Binary32.Eval (⟨.always, .mul, 0, .imm 0x80000000, .imm 0x3f800000⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 0 0x80000000}
      (Scalar.Binary32.occurrence s ⟨.always, .mul, 0, .imm 0x80000000, .imm 0x3f800000⟩ true) := by
  apply Scalar.Binary32.Eval.executed rfl
  change Ptx.Binary32.Results .mul 0x80000000 0x3f800000 0x80000000
  unfold Ptx.Binary32.Results
  decide

-- Aliases are unrestricted: both operands use the incoming register file.
example (s next : State) (e : E) (d l r : Nat)
    (h : Scalar.Binary32.Eval (⟨.always, .mul, d, .reg l, .reg r⟩ : I) s next e) :
    Ptx.Binary32.Results .mul (s.regs l) (s.regs r) (next.regs d) :=
  Scalar.Binary32.eval_destination _ s next e h rfl
example (s next : State) (e : E) (d : Nat)
    (h : Scalar.Binary32.Eval (⟨.always, .add, d, .reg d, .reg d⟩ : I) s next e) :
    Ptx.Binary32.Results .add (s.regs d) (s.regs d) (next.regs d) :=
  Scalar.Binary32.eval_destination _ s next e h rfl

-- The actual post-state value can enter the independent finite-range theorem.
example (i : I) (s next : State) (e : E) (x y : ℝ)
    (h : Scalar.Binary32.Eval i s next e) (enabled : i.guard.eval s = true)
    (leftReal : Ptx.Binary32.finiteReal (i.left.eval s) = some x)
    (rightReal : Ptx.Binary32.finiteReal (i.right.eval s) = some y)
    (range : |Ptx.Binary32.Bounds.exactReal i.operation x y| ≤ Ptx.Binary32.Bounds.maxFinite) :
    Ptx.Binary32.isFinite (next.regs i.destination) = true ∧
      ∃ z : ℝ, Ptx.Binary32.finiteReal (next.regs i.destination) = some z ∧
        |z - Ptx.Binary32.Bounds.exactReal i.operation x y| ≤
          TorchLean.Floats.eps32 (Ptx.Binary32.Bounds.exactReal i.operation x y) :=
  Ptx.Binary32.Bounds.results_error i.operation _ _ _ x y leftReal rightReal range
    (Scalar.Binary32.eval_destination i s next e h enabled)

example (i : I) (s next : State) (e : E) (h : Scalar.Binary32.Eval i s next e) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds :=
  Scalar.Binary32.eval_frame i s next e h
example (i : I) (s next : State) (e : E) (other : Nat)
    (h : Scalar.Binary32.Eval i s next e) (different : other ≠ i.destination) :
    next.regs other = s.regs other := Scalar.Binary32.eval_other i s next e other h different
example (i : I) (s next : State) (e : E) (h : Scalar.Binary32.Eval i s next e) :
    e = Scalar.Binary32.occurrence s i (i.guard.eval s) :=
  Scalar.Binary32.eval_event i s next e h
example (i : I) (s : State) : ∃ next e, Scalar.Binary32.Eval i s next e :=
  Scalar.Binary32.eval_exists i s
example (i : I) (s next : State) (e : E) (disabled : i.guard.eval s = false) :
    Scalar.Binary32.Eval i s next e ↔ next = {s with pc := s.pc+1} ∧
      e = Scalar.Binary32.occurrence s i false :=
  Scalar.Binary32.eval_false_iff i s next e disabled

example (target : Target) (program : List I) (s next : State) (e : E)
    (h : Scalar.Binary32.Step target program s next e) :
    Scalar.Binary32.SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      e.instruction = i ∧ Scalar.Binary32.Eval i s next e :=
  Scalar.Binary32.step_origin target program s next e h
example (target : Target) (program : List I) (s : State) (i : I)
    (supported : Scalar.Binary32.SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next e, Scalar.Binary32.Step target program s next e :=
  Scalar.Binary32.step_exists target program s i supported fetch
example (target : Target) (s next : State) (e : E) :
    ¬ Scalar.Binary32.Step target [] s next e :=
  Scalar.Binary32.step_no_fetch target [] s next e (by simp)
example (program : List I) (s next : State) (e : E) :
    ¬ Scalar.Binary32.Step ⟨94, 19⟩ program s next e :=
  Scalar.Binary32.step_unsupported_target ⟨94, 19⟩ program s next e
    (by unfold Scalar.Binary32.SupportedTarget; decide)
example (statement : Text.Statement) (i : I) :
    Scalar.Binary32.Text.decode statement = .ok i ↔
      statement = Scalar.Binary32.Text.encode i := Scalar.Binary32.Text.decode_iff statement i

example : (["add.rn.f32", "mul.rn.f32", "add.f32", "mul.rn.ftz.f32"].map
    Scalar.Binary32.Text.supportedMnemonic) = [true, true, false, false] := by decide

example (i : I) (s next : State) (e : E) (enabled : i.guard.eval s = true) :
    Scalar.Binary32.Eval i s next e ↔ ∃ value,
      Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value ∧
      next = {s with pc := s.pc+1, regs := update s.regs i.destination value} ∧
      e = Scalar.Binary32.occurrence s i true :=
  Scalar.Binary32.eval_true_iff i s next e enabled

example (s : State) (e : E) :
    ¬ Scalar.Binary32.Eval (⟨.always, .add, 2, .imm 0x3fc00000, .imm 0x40100000⟩ : I) s
      {s with pc := s.pc+1, regs := update s.regs 2 0x3fc00000} e := by
  intro h
  have result := Scalar.Binary32.eval_destination _ _ _ e h rfl
  have wrong : ¬ Ptx.Binary32.Results .add 0x3fc00000 0x40100000 0x3fc00000 := by
    unfold Ptx.Binary32.Results
    decide
  exact wrong (by simpa [Operand32.eval, update] using result)

example (i : I) : Scalar.Binary32.Text.decode (Scalar.Binary32.Text.encode i) = .ok i :=
  Scalar.Binary32.Text.decode_encode i
example : Scalar.Binary32.Text.decode
    ⟨.always, "add.rn.f32", [.word (.reg 0), .word (.reg 1)]⟩ =
    .error (.invalidOperands "add.rn.f32") := rfl
example : Scalar.Binary32.Text.decode
    ⟨.always, "add.rn.f32", [.word (.reg 0), .address (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "add.rn.f32") := rfl
example : Scalar.Binary32.Text.decode
    ⟨.always, "mul.rn.f32", [.word (.imm 0), .word (.reg 1), .word (.reg 2)]⟩ =
    .error (.invalidOperands "mul.rn.f32") := rfl
example (s : State) (h : s.preds 7 = false) :
    Scalar.Binary32.Eval (⟨.pred 7 true, .add, 0, .imm 0x7fc00017, .imm 0⟩ : I) s
      {s with pc := s.pc+1}
      (Scalar.Binary32.occurrence s ⟨.pred 7 true, .add, 0, .imm 0x7fc00017, .imm 0⟩ false) := by
  apply Scalar.Binary32.Eval.skipped
  simp [Guard.eval, h]
example (target : Target) (i : I) (s next : State) (e : E) (pc : s.pc = 2) :
    ¬ Scalar.Binary32.Step target [i] s next e :=
  Scalar.Binary32.step_no_fetch target [i] s next e (by simp [pc])
example (target : Target) (i j : I) (s next : State) (e : E) (pc : s.pc = 1)
    (wrong : e.instruction = i) (different : i ≠ j) :
    ¬ Scalar.Binary32.Step target [i,j] s next e := by
  intro h
  obtain ⟨_, k, fetch, origin, _⟩ := Scalar.Binary32.step_origin target [i,j] s next e h
  have kj : k = j := by simpa [pc] using fetch.symm
  exact different (wrong.symm.trans (origin.trans kj))

end Ptx.FPInstructionAcceptance
