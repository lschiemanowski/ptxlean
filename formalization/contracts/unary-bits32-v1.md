# Frozen unary-bits32-v1 contract

Implement only `Ptx/UnaryBits32.lean`, namespace `Ptx.Scalar.UnaryBits32`. Import
`Ptx.Pure32` and `Ptx.ScalarText`; reuse their execution and frontend interfaces.
Do not change any other file.

Use pinned PTX ISA 9.4 in `.ptx-source/9.4/index.html`, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Consult the listed instruction anchors, plus `predicated-execution`,
`instruction-statements`, `operand-type-information`, `source-operands`,
`destination-operands`, `integer-constants` and
`type-information-for-instructions-and-operands`.
All selected forms are introduced in PTX 1.0 and supported on all targets.
Restrict eligibility to `target.isa = 94 ∧ 10 ≤ target.sm`; this is a numeric
feature floor, not validation of target spellings or current assembler support.
Sources and destination are compatible declared 32-bit words supplied by the
caller. Immediate words are already decoded and size-converted values; do not
claim a raw-text parser, register declaration validation or implicit conversions.
All bit patterns, aliases and repeated sources are permitted. Source values are
read from the incoming state. Both instruction-guard polarities are supported.
No predicate-valued instruction forms or other widths are in scope.

Selected forms: not.b32, cnot.b32.
Source anchors: logic-and-shift-instructions-not, logic-and-shift-instructions-cnot.

`not` flips every bit. `cnot` returns one for zero and zero for every nonzero
word; it is not a bitwise complement.

```lean
namespace Ptx.Scalar.UnaryBits32
def SupportedTarget (target : Ptx.Target) : Prop := target.isa = 94 ∧ 10 ≤ target.sm
inductive Operation where
  | bitNot | cnot
  deriving DecidableEq, Repr
structure Instr where
  guard : Scalar.Guard := .always
  operation : Operation
  destination : Nat
  source : Scalar.Operand32
  deriving DecidableEq, Repr
def compute (op : Operation) (a : Word) : Word
-- compute is exactly the operation match specified by compute_eq below.
def family : Pure32.Family Operation
-- Use Pure32.Family.ofFunction with wordArity 1, predicateArity 0,
-- exact compute on input words in order, and SupportedTarget for every operation.
def lower (i : Instr) : Pure32.Instr family
-- Preserve guard, operation, destination and source(s); Fin 0 predicate arguments.
def result (i : Instr) (s : Scalar.State) : Word :=
  compute i.operation (i.source.eval s)
abbrev Occurrence := Pure32.Occurrence family
abbrev Eval (i : Instr) := Pure32.Eval (lower i)
abbrev Step (target : Ptx.Target) (program : List Instr) :=
  Pure32.Step target (program.map lower)
def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence :=
  Pure32.occurrence s (lower i) executed
namespace Text
  def supportedMnemonic : String → Bool
  def encode (i : Instr) : Scalar.Text.Statement
  def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr
end Text
theorem compute_eq (op : Operation) (a : Word) :
    compute op a = match op with
      | .bitNot => ~~~a
      | .cnot => if a = 0 then 1 else 0

theorem results_iff (op : Operation) (words : Fin 1 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0)

theorem lower_operation (i : Instr) :
    (lower i).operation = i.operation

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words 0 = i.source

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    next.regs i.destination = result i s

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧
      next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    event = occurrence s i (i.guard.eval s)

theorem eval_deterministic (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂

theorem eval_exists (i : Instr) (s : Scalar.State) :
    ∃ next event, Eval i s next event

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) :
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event

theorem step_no_fetch (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event

theorem Text.decode_encode (i : Instr) :
    Text.decode (Text.encode i) = .ok i

theorem Text.decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    Text.decode statement = .ok i ↔ statement = Text.encode i
end Ptx.Scalar.UnaryBits32
```

The typed encoder preserves the guard and uses the exact mnemonic for its
operation with a word-register destination followed by one word source.
Known spellings with malformed operands return `invalidOperands`; every other
spelling returns `unsupportedMnemonic`, even with malformed operands.
All enabled direct operand reads are recorded in order after guard reads,
including repeated registers. A skip has only the guard read, no writes or memory
effect. A fetched step checks target support even on a false guard.
The universal theorem signatures above are fixed; no extra premises or axioms.

Run `lake build Ptx.UnaryBits32` and the immutable coordinator driver
`lake env lean formalization/checks/unary-bits32-v1.lean`. Inspect all public theorem
dependencies with `#print axioms`. Only Lean's standard propext, Classical.choice
and Quot.sound are permitted. No sorry/admit, axioms, native_decide, extra model
calls or commits. Do not modify checks, descriptions, imports, manifests or shared
foundations. Report exact remaining obligations if blocked. A completed worker
run is not semantic acceptance; the coordinator will replay and review it.
