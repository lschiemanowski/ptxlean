# Frozen bounded exponential instruction contract v1

Implement only `integration/torchlean/PtxBinary32/ExponentialInstruction.lean`,
namespace `Ptx.Scalar.Exponential`. Do not change any other files. Use the existing
state and numerical provider. This task is the bounded unary floating leaf and its typed
text/fetch semantics, not a kernel or new numerical algorithm.

Imports: `PtxBinary32.Exponential`, `Ptx.ScalarText`, `Ptx.Environment`.
Reference pattern: `PtxBinary32/Instructions.lean` (binary add/mul). Do not edit
that module, duplicate its arithmetic, or encode exponential as an integer op.

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
  `Ptx.Binary32.Exponential.Results (i.source.eval s) value`; increments pc,
  updates just `i.destination` to value, emits `occurrence s i true`.
- `Step target program s next event` is exactly supported target AND existence of
  i with `program[s.pc]? = some i` and `Eval i s next event`.
- `Text.mnemonic : String := "ex2.approx.f32"`.
  `Text.supportedMnemonic name := name == "ex2.approx.f32"`.
  `Text.encode i` returns the exact mnemonic, guard and operands
  `[.word (.reg i.destination), .word i.source]`.
  `Text.decode statement` rejects any other mnemonic with `unsupportedMnemonic`;
  for this mnemonic only it accepts the exact two-operand shape above, otherwise
  returns `invalidOperands`. No FTZ, f64, integer or implicit-approximation forms.

Required complete proofs with these signatures:

```lean
theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      Ptx.Binary32.Exponential.Results (i.source.eval s) value ∧
      next = {s with pc := s.pc+1, regs := Scalar.update s.regs i.destination value} ∧
      event = occurrence s i true

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc+1} ∧ event = occurrence s i false

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) (enabled : i.guard.eval s = true) :
    Ptx.Binary32.Exponential.Results (i.source.eval s) (next.regs i.destination)

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (hEval : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) : event = occurrence s i (i.guard.eval s)

theorem eval_exists (i : Instr) (s : Scalar.State)
    (admissible : i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s)) :
    ∃ next event, Eval i s next event

theorem eval_exists_iff (i : Instr) (s : Scalar.State) :
    (∃ next event, Eval i s next event) ↔
      i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s)

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (hStep : Step target program s next event) :
    SupportedTarget target ∧ ∃ i,
      program[s.pc]? = some i ∧ event.instruction = i ∧ Eval i s next event

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State)
    (i : Instr) (supported : SupportedTarget target) (fetch : program[s.pc]? = some i)
    (admissible : i.guard.eval s = false ∨ Ptx.Binary32.Exponential.Supported (i.source.eval s)) :
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

Definitions must meet the specified contract. Preserve ALL numerical Results,
original-state operands, exact fetch and instruction identity. Disabled guards
skip ANY operand, including positive finite operands outside the numerical domain.
Enabled positive finite operands have no Eval in this fragment; this is a
coverage restriction, not PTX undefined behavior. Existence MUST expose the
disabled-guard-or-Supported disjunction; do not assume unconditional totality.
Do not impose source/destination inequality. Keep actual numerical effects
connected to the shared provider. Do not read or modify formalization/checks,
reference fixtures, coordinator scripts or evidence; implement from this contract.

Source: pinned local PTX ISA 9.4, `floating-point-instructions-ex2` (§9.7.3.21),
`predicated-execution`, `instruction-statements`, `floating-point-constants`,
`operand-type-information` and `fundamental-types`. ISA94/SM>=20 is the project
policy for no-FTZ handling, not ex2's minimum version. The selected numerical
provider supports finite nonpositive inputs, infinities and NaNs only. Signed
zeros give exactly positive one; -infinity gives +zero; +infinity gives +infinity;
NaN permits any NaN encoding. Strictly negative finite inputs use the reviewed
union of center-spacing/output-spacing two-ULP policies with nearest-even
reference rounding. This is an explicit conservative source interpretation, not
a claim of unique source meaning or physical realizability. Positive finite
inputs, including overflow, remain unsupported. This bounded fragment is NOT
full ex2 coverage and must not enter the accepted full-form ledger as such.
f32/b32 compatible bits are supplied; no register-declaration/raw literal parser.
The numeric target check does not prove a GPU target exists or hardware conforms.

Work from the pinned task base. Build from `integration/torchlean`:
`lake build PtxBinary32.ExponentialInstruction` and
`lake env lean PtxBinary32/ExponentialInstruction.lean`.
Use only completed kernel-checked proofs: no sorry, admit, new axioms or native_decide.
Inspect every public theorem dependency; allowed axioms are propext,
Classical.choice and Quot.sound. No external model calls or commits, no dependency,
manifest, toolchain, description or independent-check edits. Report exact
obstacles instead of weakening a contract. Coordinator handles acceptance,
Stratic links, documentation, coverage and commits.
