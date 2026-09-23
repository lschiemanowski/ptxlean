# Frozen binary32 instruction worker contract v1

Status: coordinator-frozen implementation contract. The associated Stratic child is
unimplemented until a candidate passes source review and independent proof checks.
The only writable worker path is `integration/torchlean/PtxBinary32/Instructions.lean`.
Use namespace `Ptx.Scalar.Binary32`; this is a registered `PtxBinary32` submodule.
All other source, descriptions, checks, package files and toolchain pins are immutable.

## Bounded slice

The integration module `PtxBinary32/Instructions.lean`, namespace
`Ptx.Scalar.Binary32`, implements two floating-point leaf instructions over the
existing `Ptx.Scalar.State`: explicit `add.rn.f32` and `mul.rn.f32`. The arithmetic
contract is exactly `Ptx.Binary32.Results`; the worker must neither reimplement
rounding nor replace the result relation by equality to a selected reference.

Keep `Ptx/Scalar.lean` and `Ptx/ScalarText.lean` unchanged. Their `BinOp` and
`Occurrence.instruction` describe integer instructions. Encoding an FP operation
as `.bin32 .add` and merely changing its result or label would falsify instruction
origin. A new small FP instruction/occurrence type is necessary; a second state,
new memory model, general concurrency framework and new floating-point backend
are not.

The leaf `Eval` relation can later be used by a coordinator-owned mixed scalar/FP
program wrapper. The worker should also provide an FP-only fetched `Step` relation
so instruction origin is already explicit and independently testable. Reaching
the end of that list means there is no fetched FP step, not that a kernel has
halted. No runner, exit opcode or total-kernel execution claim is required in this
slice. Mixing with integer loads/stores/exit can be a subsequent small wrapper
using a genuine sum of instruction and occurrence types.

## Reused interfaces, verified in the current checkout

- `Scalar.State`: `pc : Nat`, `regs : Nat → Word`, `addrs : Nat → BitVec 64`,
  `preds : Nat → Bool`, `memory : List Word`. State is supplied, not initialized
  by the instruction layer.
- `Scalar.Operand32`: `.reg Nat | .imm Word`; evaluate using `Operand32.eval s`.
  Its `reads` lists word registers only for register operands.
- `Scalar.Guard`: `.always | .pred Nat Bool`; `Guard.eval s` handles positive
  and negated predicates, and `Guard.reads` lists the predicate dependency.
- `Scalar.Register`, `Scalar.update` and its `update_same/update_other` lemmas.
- `Scalar.Text.Token`, `Statement`, `DecodeError` for the typed mnemonic boundary.
  The new decoder uses their types, not their integer `decodeOp` implementation.
- `Ptx.Target` from `Ptx.Environment`: ISA numbers are major*10+minor, e.g.94;
  SM numbers use the same convention, e.g.70.
- `Ptx.Binary32.Operation`, `Results`, `reference`, `results_exists`. `Word` is
  the original 32-bit encoded carrier; no host float conversion occurs.

An immediate `.imm bits` in this FP context represents an **already decoded
exact binary32 bit literal**, corresponding to PTX `0f` or `0F` plus eight hexadecimal
digits. It is not an integer-to-float conversion and not a parser for decimal
constants. This contextual interpretation must appear in the module/description.
Both existing Operand32 constructors are supported. In this floating-point context,
word-register operands stand for `.b32` or compatible `.f32` registers; arbitrary
declared `.u32` and `.s32` registers are not thereby made floating-point operands.
The model has no declaration checker, so frontend type compatibility remains an
explicit boundary obligation. Exact literals allow either `0f` or `0F` prefixes.

## Exact declarations

The following is a declaration contract, not a second implementation to copy
without reasoning. Private helper names and proof methods may vary. The public names, types and
contracts below are frozen; additional helpers must not strengthen their premises.
Import `PtxBinary32`, `Ptx.ScalarText` and `Ptx.Environment` as needed; do not
reimplement the reviewed numerical adapter or the existing scalar state.

```lean
namespace Ptx.Scalar.Binary32

structure Instr where
  guard : Scalar.Guard := .always
  operation : Ptx.Binary32.Operation
  destination : Nat
  left : Scalar.Operand32
  right : Scalar.Operand32
  deriving DecidableEq, Repr

structure Occurrence where
  pc : Nat
  instruction : Instr
  executed : Bool
  reads : List Scalar.Register
  writes : List Scalar.Register
  memory : Option Scalar.MemoryEffect
  deriving DecidableEq, Repr

def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence
-- pc=s.pc; instruction=i; reads=i.guard.reads ++
--   (if executed then i.left.reads ++ i.right.reads else []);
-- writes=if executed then [.word i.destination] else []; memory=none.

def SupportedTarget (target : Ptx.Target) : Prop :=
  target.isa = 94 ∧ 20 ≤ target.sm

inductive Eval (i : Instr) : Scalar.State → Scalar.State → Occurrence → Prop
  | skipped : i.guard.eval s = false →
      Eval i s {s with pc := s.pc+1} (occurrence s i false)
  | executed : i.guard.eval s = true →
      Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value →
      Eval i s {s with pc := s.pc+1,
                       regs := Scalar.update s.regs i.destination value}
        (occurrence s i true)

-- Target-neutral Eval is an arithmetic leaf relation, not a claim that all
-- targets support its PTX interpretation. The fetched, target-qualified wrapper
-- is the public PTX slice boundary.
def Step (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) : Prop :=
  SupportedTarget target ∧
    ∃ instruction, program[s.pc]? = some instruction ∧ Eval instruction s next event

namespace Text
  def mnemonic : Ptx.Binary32.Operation → String
  -- add ↦ "add.rn.f32", mul ↦ "mul.rn.f32"
  def supportedMnemonic : String → Bool
  -- exactly these two strings
  def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr
  def encode (instruction : Instr) : Scalar.Text.Statement
end Text
```

`SupportedTarget` pins PTX ISA 9.4 and the source's `sm_20+` gradual-underflow
feature threshold. It is a numeric version/feature slice, not a complete target
validator: `Target.sm` can contain numbers such as 21 and cannot express `a`/`f`
architecture suffixes. Do not claim validation of those target spellings.

The decoder accepts destination `.word (.reg d)` and two source `.word operand`
tokens, retaining the statement guard. Wrong arity or wrong operand categories
for either recognized mnemonic return `invalidOperands`. Any other mnemonic
returns `unsupportedMnemonic`, even if its operands look valid. A target is not
part of the typed `Statement`, so target restriction belongs to `Step`, not to
invented fields in that existing structure.

## Required completed proof obligations

1. **Exact true/false guard characterizations.** Under a true guard, `Eval` iff
   there is an admitted output word, with exactly the specified next state and
   executed occurrence. Under a false guard, `Eval` iff the state advances only
   PC and the skipped occurrence is exact. A false guard never needs a floating
   result premise and emits no destination write or memory effect.
2. **State and occurrence frame.** Every `Eval` advances PC by one; preserves
   all memory, address registers and predicate registers; preserves every word
   register except the executed destination. On a skip even that destination is
   unchanged. `event.pc`, `event.instruction`, `event.executed`, read/write lists
   and `event.memory=none` are proved from the relation, not assumed separately.
   These read lists are direct dependency metadata, not a complete PTX dependency
   semantics; retain the existing list behavior including duplicate source reads.
3. **Aliasing uses the pre-state.** There is no `destination ≠ source` premise.
   The result relation uses both `Operand32.eval s` values before the update.
   Prove the destination result statement with arbitrary aliases. Include
   executable/source-level checks where destination=left, destination=right,
   both source registers coincide, and all three registers coincide.
4. **Constructive leaf existence.** For every `i,s`, `∃ next,event, Eval i s next
   event`, using reference membership when executed and unchanged data on skips.
   This is existence in the conservative reference envelope, not a hardware
   scheduling or exact NaN-realizability claim. Do not use a new choice oracle,
   axiom or assumed theorem about a preferred output.
5. **Actual fetch origin and completeness.** Every `Step` entails exactly the
   fetched instruction at `s.pc`, target eligibility, and its leaf `Eval`.
   Conversely a matching fetch plus `Eval` and eligibility yields `Step`.
   Prove no step for invalid PC and no step outside the selected target slice.
   With eligibility and a valid fetch, prove a next step exists. No fabricated
   integer instruction or relabeled trace is admitted.
6. **Numeric handoff.** For executed `Eval`, prove
   `Results i.operation (i.left.eval s) (i.right.eval s)
            (next.regs i.destination)`.
   This is the important reusable conclusion: the coordinator can combine it
   with `Bounds.results_error` or `Error.add_results/mul_results`. The worker
   should not duplicate those range/error proofs or add expected-value premises.
7. **Typed text round trip and sound support.** `decode (encode i)=.ok i` for
   every `i`, including guards and exact-bit immediates. Prove successful decode
   identifies one of the two exact mnemonics and the corresponding operation,
   destination and operands. This inverse/specification theorem prevents a
   mutually wrong encoder/decoder from being accepted merely by round trip.
8. **Boundary rejection.** Cover bare `add.f32`/`mul.f32`, `.rz/.rm/.rp`, `.ftz`,
   `.sat`, `.f64`, packed `.f32x2`, integer mnemonic lookalikes, and malformed
   operands for both exact supported spellings. These are unsupported by this
   slice, not a blanket assertion that the PTX forms are illegal.

All proofs must be complete with no `sorry`, new axioms or `native_decide`.
Existing reviewed definitions/theorem statements stay fixed. New public theorem
dependencies must be inspected. Do not add an assumption declaring the desired
state update or numerical result; those are consequences of the relation.

## Exact required theorem signatures

All binders are explicit in the order shown. Theorems belong to
`Ptx.Scalar.Binary32` except the two nested `Text` declarations. These signatures
state obligations, not proof placeholders to paste into the implementation.

```lean
theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value ∧
      next = {s with pc := s.pc + 1, regs := Scalar.update s.regs i.destination value} ∧
      event = occurrence s i true

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc + 1} ∧ event = occurrence s i false

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) (enabled : i.guard.eval s = true) :
    Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s)
      (next.regs i.destination)

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (hEval : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) : event = occurrence s i (i.guard.eval s)

theorem eval_exists (i : Instr) (s : Scalar.State) :
    ∃ next event, Eval i s next event

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence)
    (hStep : Step target program s next event) :
    SupportedTarget target ∧ ∃ i,
      program[s.pc]? = some i ∧ event.instruction = i ∧ Eval i s next event

theorem step_exists (target : Ptx.Target) (program : List Instr)
    (s : Scalar.State) (i : Instr) (supported : SupportedTarget target)
    (fetch : program[s.pc]? = some i) :
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

The definitions must themselves have the exact meanings specified above. In
particular, the `Step` conjunction supplies the converse construction from
supported target, actual fetch and `Eval` without another admission assumption.
`Text.encode` uses the exact operation-specific mnemonic and preserves all fields;
`Text.decode_iff` is not permission to choose a mutually wrong pair of bindings.
The independent driver separately checks their source meanings.

## Coordinator-owned independent acceptance driver

Freeze it independently of the worker's proof file and do not let the worker
edit it. Include at least:

- Exact mnemonic-to-operation checks for both forms; independent rejection checks
  for each unsupported qualifier family and malformed operands for **both**
  recognized mnemonics. `unsupportedMnemonic` must differ from `invalidOperands`.
- Actual fetch at a nonzero PC with unrelated prefix instructions; wrong-PC and
  out-of-range-PC cases; metadata ties to that fetched instruction.
- Positive/negative guard tests, including a false guard with NaN operands;
  no floating result is required and guard-only reads are reported on the skip.
- Frame/aliasing tests with arbitrary preexisting memory/address/predicate values,
  not zero-initialized state. Theorems should give arbitrary-state guarantees;
  concrete examples are distinguishing checks, not substitutes.
- A deliberately distinguishing binary32 value such as 1.5+2.25=3.75 and
  1.5*2.25=3.375, encoded with exact hex bits. This catches integer arithmetic and
  add/mul interchange. Keep a signed-zero case and a subnormal-preservation case.
- A NaN reference accepts a different NaN payload in the envelope, while a
  finite reference rejects an arbitrary finite mismatch. Do not assert a
  signaling NaN is hardware-realizable; the acceptance test concerns the declared
  conservative envelope only.
- The actual numeric handoff theorem applied to an aliased destination, followed
  by an existing range/error theorem. It should not need a source/destination
  inequality or a premise already asserting result correctness.

Useful later offline mutations: swap the two mnemonic bindings and matching
worker examples; evaluate a source after writing destination; treat false guards
as true; delete one supported mnemonic from support classification; replace
Results with reference equality and lose NaN freedom; emit an integer occurrence.
The evaluator must distinguish a compile-passing semantic mutation from an
arbitrary build failure. The mutation harness itself need not be part of this
first worker implementation.

## Pinned source anchors and scope commentary

Use the pinned PTX9.4 HTML with SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`:

- `floating-point-instructions-add` (§9.7.3.3) and
  `floating-point-instructions-mul` (§9.7.3.5): selected forms, nearest-even,
  subnormal defaults, explicit-rounding optimization boundary and excluded
  qualifier forms.
- `floating-point-instructions` (§9.7.3): modern gradual-underflow behavior,
  IEEE compliance and unspecified single-precision NaN result. The existing
  reviewed conservative-envelope limitation remains unchanged.
- `predicated-execution` (§9.3) and `instruction-statements` (§4.3.2): optional
  predicate and negation, guard control of execution, destination-first syntax.
- `source-operands` (§6.2), `destination-operands` (§6.3),
  `operand-type-information` (§6.1), `fundamental-types` (§5.2.1): register
  operand/state typing and `.b32`/`.f32` bit compatibility; equal width alone
  does not make integer and floating declared registers interchangeable. No implicit
  numeric cast is provided. The current model has abstract total register banks and is not a PTX
  register-declaration or uninitialized-register checker.
- `floating-point-constants` (§4.5.2): exact `0f` bit literals retain their 32-bit
  value, whereas other floating constants use different parsing/conversion rules.

The model should say exactly what it interprets. Source NaN uncertainty and
conservative results are not kernel failures; unsupported syntax is not silently
expanded coverage; a valid state relation is not evidence about a particular
compiled GPU or PyTorch implementation. Preserve these distinctions in the
worker description and source/proof review.

## Worker execution and completion

Work from base commit `e00a9e51b4ab54649ce087be724f683e547f6789`.
Only create/edit `integration/torchlean/PtxBinary32/Instructions.lean`.
The coordinator provisions pinned dependencies before dispatch; do not change
package configuration, manifests, dependency checkouts or toolchains to make a
build pass. Run these commands from the repository root:

```sh
cd integration/torchlean
lake build PtxBinary32.Instructions
lake env lean PtxBinary32/Instructions.lean
```

Use a temporary `/tmp` driver to inspect dependencies of every public theorem.
Allowed logical dependencies are only `propext`, `Classical.choice` and
`Quot.sound`. Do not use `sorry`, `admit`, new axioms or `native_decide`.
No external model calls, commits, edits to independent checks, or changes outside
the one writable source module. Preserve the exact Results relation and all
arbitrary-state/aliasing conclusions. If a substantive obstacle arises, report
the exact remaining obligation instead of weakening a theorem or excluding inputs.
Report changed definitions, completed theorem names, actual check commands and
source qualifications. The coordinator handles Stratic implementation links,
source review, independent acceptance, integration and commit.
