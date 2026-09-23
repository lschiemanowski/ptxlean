# Independent proof review: binary32 instruction candidate

This review covers the `binary32-002` core and the subsequent example-only
`binary32-003` repair. The required core proofs have no identified soundness or
specification-weakening issue. The repair addresses the concrete-example gaps
identified below without changing the core or earlier examples. The coordinator's separate fresh replay subsequently passed, as recorded below;
whole-project integration remains a distinct check. The earlier
snapshot and evaluator diagnostics are retained as history.

Candidate patch SHA-256:
`2a3eeb714cc0d1a4a8d3b1f4e84347aa8c56622adea85217453b8f5f5e3c9201`.
Reviewed `integration/torchlean/PtxBinary32/Instructions.lean` SHA-256:
`2eef7cb61cbeda81f35780977b397e616e83d5d0381d1e434ee6e0c22d30d93d`.
The candidate resides in the original `binary32-001` worker checkout because the
repair resumes that checkout; this review does not mistake its name for the
accepted attempt or a fresh replay.

## Definitions and required contracts

`Instr` and `Occurrence` are distinct FP types over the existing scalar state.
The event records the actual instruction and incoming PC; operand read lists are
included only on execution, with duplicate source registers preserved. The guard
read remains present on a skip. Writes identify only the executed destination,
and memory effects are always absent.

`Eval` has exactly the skipped and executed constructors. Skipping requires a
false guard and changes only PC. Execution requires a true guard and the original
`Ptx.Binary32.Results` relation over both **pre-state** operands. Its nested
record updates advance PC and replace only the destination register; they have
the same meaning as the frozen contract's simultaneous field update. There is no
extra admissibility, source/destination inequality, selected-result equality,
finite-input restriction or desired-output hypothesis.

Both guard equivalences characterize the whole state and occurrence, not only
the arithmetic destination. The destination theorem eliminates the impossible
skip branch and uses the actual register update. The frame/other-register/event
theorems follow from both constructors and retain arbitrary supplied registers,
address registers, predicates and memory. `eval_exists` splits on the actual
guard; it reuses reviewed reference-envelope nonemptiness on the true branch and
needs no floating result on the false branch.

`Step` is precisely numeric target eligibility plus actual fetch at `s.pc` and
leaf evaluation. Origin is derived from that fetch and constructor metadata.
Valid-fetch existence uses `eval_exists`; no-fetch and unsupported-target
statements exclude their corresponding cases. The target predicate is exactly
ISA 94 and SM at least 20, with the contract's numeric-feature limitation.
There is no exit instruction, whole-program completion or GPU-execution theorem.

The decoder recognizes exactly the two explicit `.rn.f32` spellings, accepts only
a word-register destination and two word operands, preserves the guard, and
distinguishes unsupported mnemonics from malformed supported operands. The
encoder maps each operation to the correct spelling. `decode_encode` preserves
all fields; `decode_iff` additionally excludes noncanonical successful statements.
The independent source review remains responsible for PTX fidelity, including
register typing, exact-bit immediates and conservative NaN-output freedom.

## Checked proofs and dependencies

The 13 required named theorems were inspected and audited:

- `eval_true_iff`, `eval_false_iff`, `eval_destination`, `eval_frame`,
  `eval_other`, `eval_event`, `eval_exists`;
- `step_origin`, `step_exists`, `step_no_fetch`, `step_unsupported_target`;
- `Text.decode_encode`, `Text.decode_iff`.

Ten type/definition endpoints were also audited: `Instr`, `Occurrence`,
`occurrence`, `SupportedTarget`, `Eval`, `Step`, and `Text.mnemonic`,
`Text.supportedMnemonic`, `Text.decode`, `Text.encode`.

There are 28 additional anonymous `example` commands and no additional named
public theorem. All example statements and proof bodies were inspected. For
individual dependency reports, a temporary copy replaced only each `example`
keyword with `theorem review_example_N` and appended `#print axioms` commands.
That copy retained the original definitions, private constants, statements and
proof bodies, and elaborated afresh. The candidate file was not edited. All 51
reports (13 named proofs, ten definitions/types, 28 anonymous proof bodies) were
checked for exact count and standard dependencies using `audit_dependencies`.
Only `propext`, `Classical.choice` and `Quot.sound` occur; some declarations have
no axiom dependencies. The lexical source guard found no omitted-proof token,
new axiom or `native_decide`.

Checks ran in the worker checkout's pinned integration package:

```sh
lake --no-cache build PtxBinary32.Instructions
lake --no-cache env lean PtxBinary32/Instructions.lean
lake --no-cache env lean /tmp/ptx-binary32-instruction-audit.lean
lake --no-cache env lean /tmp/ptx-binary32-instruction-examples.lean
```

All four commands passed; the target build reported 2,518 jobs. These checks
freshly elaborate the source and proof drivers but **are not a fresh replay** of
the patch in a newly provisioned base checkout. The exact audited names are
recorded in `/tmp/ptx-binary32-instruction-review.json`; logs use the prefix
`/tmp/ptx-binary32-instructions-`.

## Concrete examples versus universal proofs

The fixed 1.5/2.25 arithmetic examples use explicit expected output bits, so kernel
conversion genuinely checks the distinguishing add and multiply results.
In contrast, the signed-zero and subnormal worker examples merely assert
`Results ... (reference ...)`: they demonstrate membership, not preservation of
the intended zero sign or subnormal bits. The four overlap examples invoke
universal existence using a zero-register demonstration state; they do not check
an actual aliased result value. The source includes a true positive guard and a
false positive guard with NaN operands, but no concrete negated-guard example.
These facts must not be reported as stronger worker-provided execution examples.

The universal proofs themselves do support arbitrary aliases and both guard
polarities because they use the existing `Operand32.eval` and `Guard.eval`.
The coordinator-owned driver contains stronger distinguishing tests, including
encoded signed-zero/subnormal values, arbitrary alias handoff and a false
negated guard. Nonetheless the worker contract separately requests meaningful
source examples. Their remaining obligations should be repaired or explicitly
disposed of before reporting full contract completion; a successful proof audit
does not erase this coverage distinction.

## Independent acceptance preflight

The frozen driver has SHA-256
`95577a11afa94eb133c0dae216e540a535a6a6c4cee0581bb6ea0305d4925196`.
Its first invocation in the worker checkout encountered a missing
`PtxBinary32Bounds.olean`, before driver elaboration. Building the already pinned
`PtxBinary32Bounds` prerequisite succeeded; no source or package pin was changed.
The subsequent frozen-driver run completed with two deterministic elaboration
timeouts, at lines 131 and 135: the generic alias examples call
`eval_destination _ s next e h rfl`. Lean exhausted 2,000,000 heartbeats at
`whnf` while elaborating those applications. No other error was reported. This
is not a successful acceptance run and not evidence of a contradictory result.
The core named theorem itself had already compiled and passed its dependency
audit. A temporary driver with only those two instruction arguments made explicit
**passed** with no diagnostics, at the original heartbeat setting. It preserves
every statement and all other tests. The explicit instructions are
`⟨.always, .mul, d, .reg l, .reg r⟩` and
`⟨.always, .add, d, .reg d, .reg d⟩`, each annotated `: I`.
This establishes that the observed failure was elaboration cost in argument
inference, not a failing alias contract. The original frozen driver was not
changed by this reviewer. The passing temporary command was:

```sh
lake --no-cache env lean /tmp/ptx-binary32-instructions-explicit-driver.lean
```

Its log is `/tmp/ptx-binary32-instructions-explicit-driver.log`.
This is a worker-checkout acceptance **preflight**, not an isolated patch replay.

The coordinator preserved original replay metadata and added the missing Bounds
build target in `formalization/checks/binary32-instructions-v2.json`, retaining
the same frozen Lean driver. Missing prerequisite and later elaboration cost are
separate evaluator issues, not worker semantic repairs. Fresh replay remains
the coordinator's separate acceptance obligation.


## Example-only repair: binary32-003

Final candidate patch SHA-256:
`5280b4c9504f4aad4eb232819651fbd9a8d8479498652d6cafb67970631488a6`.
Final reviewed source SHA-256:
`dfa76383c0500eac5752873a59dc337443c3fa81c0f1000d7ce76599deafad6b`.

A byte comparison against the preserved candidate-002 source confirms that the
entire previous module prefix is unchanged: all definitions, the 13 required
proofs through `end Text`, private demonstration values and all 28 anonymous
examples. Exactly five named theorems were appended immediately before the
unchanged final namespace end:

- `signed_zero_bits` fixes both inputs and the negative-zero output bits. Its
  use of `envelope_self` must kernel-convert the actual reference to those fixed
  output bits; it is no longer just a symbolic reference-membership example.
- `subnormal_bits` similarly fixes minimum-subnormal inputs `1`, `1` and output
  `2`, checking preserved subnormal addition through kernel conversion.
- `negative_guard_exec` uses an arbitrary supplied state whose predicate is
  false. The negated guard executes, stores the exact 3.375 product bits, and
  preserves all other state fields through the specified update.
- `negative_guard_skip` uses an arbitrary supplied state whose predicate is
  true. The same negated-guard instruction changes only PC and records a skipped
  event; no floating result premise is supplied.
- `alias_add_bits` assumes only the incoming register's 1.5 encoding and fixes
  all source/destination registers to the same register. It constructs the
  exact post-state with the 3.0 encoding, demonstrating pre-state reads under
  complete overlap. It assumes no output fact or nonalias condition.

These additions resolve the previously identified meaningful-example gaps.
They do not alter the conservative NaN relation, promote examples to universal
coverage, or introduce hardware/kernel-execution claims.

`lake --no-cache build PtxBinary32.Instructions` passed (2,518 jobs), and fresh
`lake --no-cache env lean PtxBinary32/Instructions.lean` elaboration passed.
An independent temporary driver audited all five new names; exact-count checking
accepted only `propext`, `Classical.choice` and `Quot.sound`. No forbidden proof
token was found. The cumulative review covers 18 named public theorems, ten
core definitions/types and 28 anonymous example proofs, for 56 dependency
reports across the unchanged core and appended repair.

The repair checks ran in the resumed worker checkout; they are not the separate
fresh replay launched by the coordinator. Logs are
`/tmp/ptx-binary32-instructions-003-build.log`,
`/tmp/ptx-binary32-instructions-003-fresh.log` and
`/tmp/ptx-binary32-instructions-003-audit.log`.
No candidate file was changed by this reviewer. No outstanding independent
proof-review blocker remains for this exact candidate.


## Subsequent isolated replay observation

After the candidate-003 review, the coordinator completed
`/tmp/ptxlean-binary32-replay-003/result.json` with `mechanical: pass` for the
same patch hash. The corrected v2 driver SHA-256 is
`41332b7e362168bb9c60cfb0dec101a7a05d75935741a7f12ccd03bb1472ab6d`.
This replay builds the missing Bounds prerequisite and makes only the two
previously discussed instruction arguments explicit. The accepted statements
remain unchanged. This recorded fresh-replay pass is separate from the earlier
worker-checkout checks, and does not replace the project's later integration
checks or the stated PTX source-fidelity boundaries.
