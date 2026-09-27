# Frozen rounded reciprocal instruction contract v1

Implement only `integration/torchlean/PtxBinary32/ReciprocalInstruction.lean`,
namespace `Ptx.Scalar.Reciprocal`. Do not change any other files. Use the existing
state and numerical provider. This task is the unary floating leaf and its typed
text/fetch semantics, not a kernel or new numerical algorithm.

Imports: `PtxBinary32.Reciprocal`, `Ptx.ScalarText`, `Ptx.Environment`.
Reference pattern: `PtxBinary32/Instructions.lean` (binary add/mul). Do not edit
that module, duplicate its arithmetic, or encode reciprocal as an integer op.

Required definitions with these names and exact meanings:

- `Instr` has `guard : Scalar.Guard := .always`, `destination : Nat`,
  `source : Scalar.Operand32`, deriving DecidableEq and Repr. No opcode field.
- `Occurrence` has `pc : Nat`, `instruction : Instr`, `executed : Bool`,
  `reads writes : List Scalar.Register`, `memory : Option Scalar.MemoryEffect`,
  deriving DecidableEq and Repr.
- `occurrence s i executed` has PC `s.pc`, exact `i`, guard reads followed by
  source reads iff executed, singleton destination write iff executed, no memory.
- `SupportedTarget target := target.isa = 94 ∧ 20 ≤ target.sm`.
- Inductive `Eval i s next event` has only constructors `skipped` and `executed`.
  `skipped` requires `i.guard.eval s = false`, increments pc, changes nothing else,
  and emits `occurrence s i false`. `executed` requires true guard and
  `Ptx.Binary32.Reciprocal.Results (i.source.eval s) value`; increments pc,
  updates just `i.destination` to value, emits `occurrence s i true`.
- `Step target program s next event` is exactly supported target AND existence of
  i with `program[s.pc]? = some i` and `Eval i s next event`.
- `Text.mnemonic : String := "rcp.rn.f32"`.
  `Text.supportedMnemonic name := name == "rcp.rn.f32"`.
  `Text.encode i` returns the exact mnemonic, guard and operands
  `[.word (.reg i.destination), .word i.source]`.
  `Text.decode statement` rejects any other mnemonic with `unsupportedMnemonic`;
  for this mnemonic only it accepts the exact two-operand shape above, otherwise
  returns `invalidOperands`. No approximate, FTZ, f64 or implicit-rounding forms.

Required complete proofs, mirroring the binary leaf contracts with unary source:

```
theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      Ptx.Binary32.Reciprocal.Results (i.source.eval s) value ∧
      next = {s with pc := s.pc+1, regs := Scalar.update s.regs i.destination value} ∧
      event = occurrence s i true

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc+1} ∧ event = occurrence s i false

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) (enabled : i.guard.eval s = true) :
    Ptx.Binary32.Reciprocal.Results (i.source.eval s) (next.regs i.destination)

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (hEval : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) : event = occurrence s i (i.guard.eval s)

theorem eval_exists (i : Instr) (s : Scalar.State) : ∃ next event, Eval i s next event

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (hStep : Step target program s next event) :
    SupportedTarget target ∧ ∃ i,
      program[s.pc]? = some i ∧ event.instruction = i ∧ Eval i s next event

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State)
    (i : Instr) (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event

theorem step_no_fetch (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event

namespace Text
theorem decode_encode (i : Instr) : decode (encode i) = .ok i
theorem decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    decode statement = .ok i ↔ statement = encode i
end Text
```

Definitions themselves must meet the specified contract, not just the theorem
statements. In particular preserve ALL numerical Results, operand evaluation in
the original state, false-guard behavior on zero/NaN, exact fetch and instruction
identity. No source/destination inequality or finite-value premise on Eval/Step.
No extra admitted-state assumption for step existence.

Source: pinned local PTX ISA 9.4, `floating-point-instructions-rcp` (§9.7.3.13),
`floating-point-instructions`, `predicated-execution`, `instruction-statements`,
`floating-point-constants`, `operand-type-information` and `fundamental-types`.
The selected reciprocal is explicitly nearest-even, no FTZ, sm_20+; signed zero
maps to same-sign infinity, infinity to same-sign zero, NaN to NaN. Its numerical
provider already includes these cases. f32/b32 compatible bits are supplied;
there is no register-declaration or raw literal parser. Numeric sm support does
not assert every numeric GPU target actually exists. PTX compatibility and
hardware conformance are separate claims.

Work from the pinned task base. Build from `integration/torchlean`:
`lake build PtxBinary32.ReciprocalInstruction` and
`lake env lean PtxBinary32/ReciprocalInstruction.lean`.
Use only completed kernel-checked proofs: no sorry, admit, new axioms or native_decide.
Inspect every public theorem dependency; allowed axioms are propext,
Classical.choice and Quot.sound. No external model calls or commits, no dependency,
manifest, toolchain, description or independent-check edits. Report exact
obstacles instead of weakening a contract. Coordinator handles acceptance,
Stratic links, documentation, coverage and commits.
