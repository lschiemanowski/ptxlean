# Binary32 instruction contract: independent preflight review

This is a **preimplementation source/API review**, not acceptance of a worker
candidate. No instruction implementation or completed proof dependency audit was
available during this review. The frozen contract is suitable for the bounded
slice; the coordinator addressed the identified acceptance-driver coverage gaps
before dispatch. Candidate acceptance must revisit the actual definitions, completed
proofs, dependency reports and fresh replay.

Reviewed inputs:

- `formalization/contracts/binary32-instructions-v1.md`, SHA-256
  `5f91146bfc8b31f6f26a19f643f4b5fd2c6dcbd725a4b56ba1199d61e3295ace`.
- `formalization/tasks/binary32-instructions-v1.json`, SHA-256
  `36b338b59d516be77146bb61735c6af6b131d9b976bd5715344ed5e519c2f1fa`.
  Its prompt equals the contract text and all 13 recorded source hashes matched
  the inspected files.
- `formalization/checks/binary32-instructions-v1.lean`, SHA-256
  `95577a11afa94eb133c0dae216e540a535a6a6c4cee0581bb6ea0305d4925196`.
  This is the final preworker driver version, including all preflight corrections
  discussed below.
- The pinned [PTX 9.4 source](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html),
  SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
  The source was read locally, not substituted with an unpinned online edition.

## Source meaning and representation

The selected explicit `add.rn.f32` and `mul.rn.f32` spellings agree with
§9.7.3.3 and §9.7.3.5. Their nearest-even interpretation and preserved subnormals
require the stated `sm_20+` feature boundary. Exact ISA 9.4 is a deliberately
pinned review scope, not the first ISA version providing these operations.
`SupportedTarget` correctly disclaims validating every numeric target or the
architecture-specific suffixes absent from `Target`. No execution or target
conformance claim follows from passing this numeric condition alone.

§6.1 and §5.2.1 permit a same-width bit type to serve as a floating operand.
Accordingly the common word bank denotes `.b32` or compatible `.f32` registers
in this frontend; equal width does not make declared integer and floating types
interchangeable. The contract now states that declaration checking and register
initialization are outside this supplied-state model.

All `Operand32` bit patterns can be retained without a finite-value restriction.
§4.5.2's `0f`/`0F` plus eight hexadecimal digits specifies exact single-precision
bits. This is neither a decimal-constant parser nor an integer-to-float cast.
The source justification uses §4.3.2, which admits constant instruction operands,
together with §4.5.2; §6.2 alone describes register sources and is insufficient
as the entire immediate-literal justification. The typed token loses the original
literal spelling, which is an explicit frontend boundary, not a proved parser.

§9.3 and §4.3.2 support the positive and negated guard behavior. A false guard
must advance the sequential position while preserving the data state; no operand
result is needed. Source operands are evaluated from the supplied pre-state, so
none of the four source/destination overlap patterns needs an inequality premise.
The scalar `Guard`, `Operand32.eval`, `update`, and register metadata APIs inspected
in the current checkout fit these requirements.

A separate FP instruction/occurrence type avoids falsely labeling arithmetic as
an integer instruction. `Step` requires actual fetch at `s.pc` and the explicit
feature/version condition. End-of-list failure means absence of a fetched FP
step; this fragment has no kernel exit or termination contract. Direct read/write
lists remain metadata, not a full PTX dependency semantics.

The [prior binary32 source review](../foundations/binary32-source-review.md)
continues to govern `Results`. It is a conservative NaN envelope; reference
membership and leaf existence do not establish realizability of every admitted
NaN encoding. The instruction layer must not replace the envelope by equality
to FloatLib's particular payload choice.

## Acceptance-driver inspection

The driver independently fixes both mnemonic bindings for arbitrary guards,
destinations and operands, and tests excluded qualifier families and malformed
tokens. It distinguishes add from multiply and integer arithmetic using exact
encoded values. Other checks cover signed zero, subnormal addition at a nonzero
fetched PC, an alternative NaN payload, numeric target boundaries, false guard,
arbitrary supplied-state frames, unrestricted register aliasing, the numerical
handoff to the independently proved finite-range result, and exact public theorem
applications. Its newest checks also reject a wrong finite result and exercise
the exported support classifier independently of decoding.

No obvious Lean syntax or existing-interface mismatch was found by inspection.
**This is not a successful elaboration claim:** the imported instruction module
does not yet exist. Using `rfl` in the decoder examples additionally requires a
simple definitionally reducing implementation; the later replay must distinguish
an evaluator/elaboration issue from a failed semantic contract.

The final driver addresses every gap identified in this preflight: it explicitly
applies the named `Text.decode_encode` endpoint, adds an actual NaN operand
under a false positive guard, exercises wrong destination/category/arity cases
for both mnemonics, and checks nonempty out-of-range fetch and wrong instruction
origin at a valid nonzero PC. The origin rejection correctly derives the fetched
instruction and contradicts a distinct event instruction. The latest additions
have no apparent source/API or Lean syntax mismatch on inspection.

No identified preflight blocker remains. No independent driver or implementation
file was edited by this reviewer. After a candidate exists, update this review
with the actual implementation hash, inspected semantic definitions, all public
theorem dependencies and fresh acceptance result; keep the distinction between
this preflight and completed proof/source acceptance explicit. A later checking
failure must still be diagnosed rather than presumed to be a worker defect.


## Completed semantic review of repaired worker candidate

This section reviews the actual implementation after repair attempt
`binary32-002`. It preserves the preflight record above as historical evidence;
its earlier “no implementation available” statements describe that earlier
review only. This is an independent semantic inspection, not a substitute for
the separate fresh Lean replay and theorem-dependency audit.

Inspected artifacts:

- Worker candidate
  `.formalization-runs/luna/attempts/binary32-001/worktree/integration/torchlean/PtxBinary32/Instructions.lean`,
  SHA-256 `2eef7cb61cbeda81f35780977b397e616e83d5d0381d1e434ee6e0c22d30d93d`.
- Saved repair patch
  `.formalization-runs/luna/attempts/binary32-002/candidate.patch`, SHA-256
  `2a3eeb714cc0d1a4a8d3b1f4e84347aa8c56622adea85217453b8f5f5e3c9201`.
  The patch adds exactly this candidate file; its added bytes were compared with
  the inspected source and matched exactly.
- Frozen contract and independent driver with the hashes recorded in the
  preflight section. Both hashes were rechecked and remained unchanged.
- Existing numerical adapter `integration/torchlean/PtxBinary32.lean`, SHA-256
  `652adf5073b937101b6f1f187719fd14dd9208f1105d39d0e72743916ecd5e13`;
  scalar state/operand/guard definitions in `Ptx/Scalar.lean`, SHA-256
  `d2676870384e35b0517979c145e3b615088668915a9b5d0178d3948813ee07d5`.
- The pinned manual with the unchanged hash above. Add/mul, predication,
  exact-bit literal and operand-compatibility clauses were revisited locally.

### Execution, dataflow and event fidelity

The candidate's two `Eval` constructors have exactly the specified meanings.
The skipped constructor requires the actual incoming guard to be false, advances
only PC, and constructs a skipped occurrence. It has no arithmetic-result
premise, so NaN or infinity operands cannot prevent a supported skipped step.
The executed constructor requires the incoming guard to be true, evaluates both
operands against the incoming state, and writes one result admitted by the
unchanged numerical `Results` relation. The nested record update first changing
PC and then registers has the same meaning as the contract's combined update.

Both operands are read before the destination update. There are no alias
inequalities or finite-value restrictions. Destination=left, destination=right,
left=right, and all registers coinciding are therefore included by the same
universal definition and destination theorem. The old register contents are
used in each case. The original `Guard.eval` supplies positive and negated
predicate behavior; the candidate does not replace it with a custom convention.

Occurrence construction retains the exact floating-point instruction, incoming
PC and execution flag. Its reads are the guard reads followed, only on execution,
by both operand read lists. Duplicate source-register entries are retained,
as required by the list-valued metadata contract. Executed writes contain only
the destination; skipped writes are empty. Memory is always `none`. These are
actual occurrence fields, not assumptions inserted into downstream theorems.
They remain direct read/write metadata, not a complete PTX dependency model.

`Step` is precisely supported target plus fetch at `s.pc` plus that instruction's
`Eval`. No alternate instruction, callback or relabeled integer event can supply
the floating-point step. The origin theorem additionally derives the occurrence's
instruction equality. Out-of-range fetch and unsupported target exclude Step;
there is no implicit halt or fabricated hardware fault. `SupportedTarget` is
exactly ISA94 and numeric SM at least20. Its intentionally limited interpretation
as a version/feature slice is the one recorded in the frozen contract.

### Numerical and typed-text meaning

The candidate imports `PtxBinary32` and uses `Ptx.Binary32.Results` directly in
the executed constructor, exact characterization and destination conclusion.
It neither substitutes host arithmetic nor narrows the relation to equality with
the reference. Consequently every 32-bit operand is admitted, non-NaN results
retain their exact reference bits, and NaN results preserve the existing
conservative envelope. Signed zero, subnormal values, overflow, infinities and
invalid-operation NaNs all follow the reviewed numerical foundation unchanged.
There is no added saturation, flushing, finite-only domain or implicit cast.

`eval_exists` constructs an executed result using the existing `results_exists`,
and handles false guards separately. This establishes nonemptiness of the stated
relation, not hardware execution or exact realizability of every NaN bit pattern.
The prior numerical source qualification remains necessary, particularly the
unresolved quiet/signaling output subset.

The decoder recognizes exactly `add.rn.f32` as addition and `mul.rn.f32` as
multiplication. A recognized spelling accepts exactly a word-register destination
and two word operands, retaining the guard; other operand shapes produce
`invalidOperands`. Every other spelling produces `unsupportedMnemonic`.
The exported support classifier independently names the same two strings.
Bare forms, alternative rounding modes, FTZ, saturation, f64, packed f32x2 and
integer lookalikes cannot be silently interpreted as one of the supported forms.

The encoder uses the same correctly interpreted operation-specific names and
retains guard, destination and both operands. Successful decode is characterized
by exact equality to that encoding. The general inverse theorem complements,
but does not replace, inspecting those names against the source and checking
them independently: mutually wrong bindings could otherwise round-trip.

Immediate words remain already-decoded `0f`/`0F` bit literals, not integer values
to convert. The module comment correctly retains `.b32`/compatible `.f32`
register typing as a frontend obligation. Neither the word bank nor these
proofs validate source declarations, initialization, raw PTX syntax or launch
conditions. The explicit-rounding and sm20 gradual-underflow interpretation
agrees with the selected source clauses; no bare multiply/add contraction
behavior is admitted.

### Disposition and verification boundary

No semantic blocker was found for this exact repaired candidate under the frozen
scope. The named public theorem statements preserve the required arbitrary-state,
aliasing, frame, result-set, fetch and decoder contracts; the nested record-update
spelling does not strengthen their premises or alter their meaning. Source
fidelity is acceptable within the documented numerical-envelope and frontend
limits.

The candidate's signed-zero and subnormal examples merely establish membership
of the selected reference result. They do not independently prove the expected
zero sign or subnormal bits. The frozen coordinator driver supplies the stronger
concrete checks, including exact negative-zero multiplication and subnormal
addition, along with aliases, frames and source bindings. The source review must
not promote those weaker worker examples into evidence they do not supply.

Fresh replay, successful elaboration of the frozen independent driver and a
complete public-declaration dependency audit remain separate acceptance gates.
This reviewer did not run or claim their result here; they are assigned to the
coordinator and independent proof reviewer. No candidate, frozen contract or
independent check file was modified during this review.

## Final example-only candidate: binary32-003

The final patch is SHA-256
`5280b4c9504f4aad4eb232819651fbd9a8d8479498652d6cafb67970631488a6`;
its reconstructed source is SHA-256
`dfa76383c0500eac5752873a59dc337443c3fa81c0f1000d7ce76599deafad6b`.
An exact comparison with the saved candidate-002 patch confirms that the sole
change is five named example theorems before the final namespace end. All prior
semantic definitions, theorem statements and proofs are unchanged. The earlier
semantic acceptance therefore applies to the unchanged core.

The appended examples address the weak demonstration cases identified above:

- `signed_zero_bits` fixes `-0 * +1` to the negative-zero encoding, rather than
  merely naming an unspecified reference result. This matches the selected
  IEEE-754-compliant multiplication interpretation stated in
  [§9.7.3](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions)
  and [mul](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-mul).
- `subnormal_bits` fixes the sum of two minimum positive subnormals to encoding
  `2`. The [add clause](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-add)
  preserves subnormals on the selected sm_20-or-later slice without `.ftz`.
- `negative_guard_exec` executes when the incoming predicate is false and
  produces the exact encoding of `1.5 * 2.25 = 3.375`.
  `negative_guard_skip` skips that same negated-guard instruction when the
  incoming predicate is true, changing only PC. Both agree with
  [§9.3](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#predicated-execution).
- `alias_add_bits` reads the same incoming register twice and writes the exact
  encoding of `1.5 + 1.5 = 3.0` back to it. The only value premise describes
  the incoming register; no result premise or nonalias assumption is introduced.

The fixed-bit conclusions require Lean to convert the reviewed reference to
those particular bits when applying `envelope_self`; they are stronger than
symbolic reference-membership examples. Their finite inputs do not narrow the
instruction relation's domain or change the conservative NaN policy. They are
leaf instruction examples, not fetched-program, termination or hardware proofs.

No independent semantic blocker remains for this exact final candidate. The
separate [proof review](binary32-instructions-proof-review.md) records fresh
source elaboration and the five additional dependency reports. The coordinator's
isolated replay remains its own mechanical acceptance gate; this source review
does not claim a replay result it did not inspect. No worker proof code or frozen
acceptance assertions were edited during this review.
