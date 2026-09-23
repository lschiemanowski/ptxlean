# Second Luna task: 32-bit population and leading-zero counts

This is an independently prepared source review and acceptance package, not an
implemented instruction slice. The task is `formalization/tasks/bitcount-u32-v1.json`;
its exact base commit is
`abd21234e3b59ca427bf155bd8a53c6b75369f2e`, the completed collective-foundation
milestone. The package was prepared with an invalid draft base before that
milestone was supplied, and the runner's rejection of the draft was checked.
The final package validates against the supplied commit and pinned source bytes.
No worker has been launched as part of this preparation. The frozen acceptance
driver is outside the pinned base and is run by the coordinator; all required
public theorem signatures are included directly in the immutable task prompt.

The package name uses `u32` for the result type. The two PTX mnemonics are exactly
`popc.b32` and `clz.b32`, not `popc.u32` or `clz.u32`.

## Pinned source and complete instruction clauses

Source: `references/nvidia/ptx-isa-9.4/index.html`, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.

| Source anchor | Obligation |
| --- | --- |
| `integer-arithmetic-instructions-popc`, §9.7.1.15, lines 9685–9721 | Count every one bit in the source; destination is a 32-bit `.u32` register. |
| `integer-arithmetic-instructions-clz`, §9.7.1.16, lines 9722–9764 | Count consecutive zeros starting at the most significant bit; stop at the first one, or after all 32 bits. Destination is `.u32`. |
| `integer-arithmetic-instructions`, §9.7.1 | Integer instructions accept register and constant-immediate input forms. |
| `operand-type-information`, §6.1 | Operand declarations must be compatible; bit-size types accept equal-sized types. The typed word representation preserves bits, not raw declaration checking. |
| `source-operands`, §6.2; `destination-operands`, §6.3 | ALU register-state-space operands and a register destination; the arithmetic-family clause additionally permits constants as inputs. |
| `predicated-execution`, §9.3 | Optional positive or negated guard; no guard means unconditional execution. |

Both complete instruction sections were read, including their pseudocode,
examples, version and target notes. Both instructions were introduced in PTX 2.0
and require target `sm_20` or later. Their complete syntax lists `.b32` and `.b64`,
with no saturation, rounding or other optional modifier. Only `.b32` is assigned
to this task. Rejecting `.b64` as unsupported does not claim it is invalid PTX.

There is no exceptional input or undefined zero-input case in these clauses.
For `popc`, zero causes no iterations, yielding zero. For `clz`, zero continues
until the explicit width bound, yielding 32. The high bit is ordinary data, not
a sign bit. The pseudocode's shifting temporary does not write the source
register; only destination `d` is the instruction result. Reading and writing
the same register must therefore use its incoming bit pattern.

## Small extension to the current machine

`BinOp` requires two inputs. Encoding these operations there would invent an
operand that PTX does not have and corrupt operand/read metadata. Add one unary
operation enumeration with exactly `clz` and `popc`, its evaluator, and one
`Op.unary32` constructor. Extend existing execution, trace metadata and typed
text handling, retaining the same register update and predicate rules.

The allowed worker paths are `Ptx/Scalar.lean`, `Ptx/ScalarText.lean`, a new
`Ptx/IntegerBitCount.lean`, and `Ptx/ScalarRules.lean` only for mechanical proof
repairs caused by the new unary constructor, with existing statements unchanged. No common imports, central audit, checks, descriptions,
source files or toolchain changes are allowed. Existing generic scalar safety
and frame proofs use case splitting with structural discharge of non-memory
instructions; this new case should fit that mechanism. A full baseline build is
still required: this inspection is not proof that every downstream consumer
continues to compile. Any required change outside the allowlist must be reported
for coordinator review, not replaced by weakening existing theorem statements.

Architecture/version facts are recorded source conditions. The existing
memory-only eligibility checker does not validate them for arithmetic, and this
small task does not silently enlarge that checker's responsibility. Raw parsing,
register declarations and declarations' compatible-type rules remain separate
from the typed mnemonic interface.

## Universal proof obligations

In namespace `Ptx.Scalar.IntegerBitCount`, `popc_toNat` must identify the actual
unary evaluator's result with the length of the true-bit filter over indices
0 through 31. `clz_toNat` must identify its result with the initial false-bit
prefix when those indices are reversed. The independent driver fixes the exact
Lean statements. This formulation directly exposes bit order and width without
requiring an unrelated logarithm identity or a particular implementation loop.

`popc_bound` and `clz_bound` bound the natural result by 32 for every `Word`.
`popc_zero_iff` identifies zero population count exactly with zero input;
`clz_width_iff` identifies result 32 exactly with zero input. The full universal
contracts cannot be replaced by boundary examples or hypotheses about inputs.

`unary_exec` states equality of the actual `.next` result, including the state
record and occurrence. It permits every input state, register or immediate
source, destination, true guard and candidate read override. Only the program
counter and destination change. `unary_false` states the exact skipped result;
`unary_preserves_other` exposes the unchanged arbitrary non-destination register.
These prove absence of memory access and frame behavior through the actual
machine, rather than an isolated helper function. Trace read/write lists are
also checked independently instead of using new metadata functions as the oracle.

The typed decoder must accept only a word-register destination followed by one
word source, preserve the guard, encode canonical mnemonics and retain both
existing general text theorems. Wrong operand category/arity is `invalidOperands`;
unsupported width, signedness or modifier spelling is `unsupportedMnemonic`.

## Independent expected cases

| Input | `popc.b32` | `clz.b32` | Purpose |
| --- | ---: | ---: | --- |
| `0` | 0 | 32 | Defined zero behavior |
| `1` | 1 | 31 | Leading versus trailing direction |
| `2` | 1 | 30 | Position off by one |
| `0x80000000` | 1 | 0 | Most significant bit included |
| `0xffffffff` | 32 | 0 | Every bit counted |
| `0x7fffffff` | 31 | 1 | Distinguish high bit and word width |
| `0x00f00001` | 5 | 8 | Several set bits separated by zeros |
| `0xaaaaaaaa` | 16 | 0 | Alternating bits with high bit set |
| `0x55555555` | 16 | 1 | Alternating bits with high bit clear |

The driver also checks changing source/destination alias cases for both
operations, false positive and negative guards, a true negative guard with a
literal source and irrelevant memory override, register/literal decoding,
encoding, malformed destination/categories/arity, unsupported forms, and a small
selection of old scalar/text behavior. Fresh replay still builds the existing
baseline audit and candidate module in addition to running the driver.

`formalization/checks/bitcount-u32.json` lists nine required worker declarations
and the two existing general text theorems for dependency inspection. The full
candidate driver cannot compile before the requested operations exist; it is
not reported as having passed. Its baseline-compatible prefix was extracted to
`/tmp/bitcount-baseline-checks.lean`, with only the import changed to
`Ptx.ScalarText` and the namespace closed, and checked successfully with
`lake env lean /tmp/bitcount-baseline-checks.lean`. That verifies the oracle's
concrete counts, state/observation helper types and old-operation probes only.

The completed candidate must subsequently pass fresh offline reconstruction,
full build, the unchanged candidate driver and dependency inspection, followed
by independent semantic and proof review. Kernel proof checking cannot by itself
establish that an implementation definition matches the intended PTX instruction.
Useful future mutations include swapping the operations, scanning zeros from the
low end, returning zero for `clz 0`, excluding bit 31, skipping the actual write,
ignoring a false guard, and accepting an unsupported type spelling. A mutation
counts as detected only after its wrong implementation itself compiles.

## Evaluator repair after the first completed candidate

The fresh replay of `bitcount-002`, patch SHA-256
`49581ab681b41b4f705e18a12dabd261f4f394e610ede7000b01f76a6360ad43`, passed the
clean existing-project check and candidate-module build, then failed the frozen
v1 driver. The failed replay is retained at
`.formalization-runs/replays/bitcount-002/result.json`.

There were two independent issues. The candidate declared its execution
lemmas under `Ptx.Scalar`, omitting the required `Ptx.Scalar.IntegerBitCount`
names. Separately, the coordinator's v1 driver placed the second field of a
record update at an invalid indentation for Lean's parser. The earlier baseline
prefix check did not include this candidate-only declaration, so it did not
expose that evaluator error. This is an evaluator defect, not a candidate
semantic defect.

The original `formalization/checks/bitcount-u32.lean` remains unchanged, with
SHA-256 `015e832282761e6a3a27f1057969e42152aa6eaa62eb68456810a08266d0da23`.
The new `formalization/checks/bitcount-u32-v2.lean` merely places that record
update's two fields on one line. All non-whitespace bytes are identical; no
assertion, signature, name or expected result changed. Its SHA-256 is
`59bddc3cceb558578f8ace3e71dc2c107a31a0895b4bf649d363296c3a83c27a`.
The existing check manifest now points to v2; its SHA-256 is
`29cbfcee7274a5f92100cd378e884fcf75e8bd782cdf30f1ef3f6cadbf49d1c3`.

The v2 baseline-compatible prefix compiles. Running full v2 against the freshly
reconstructed `bitcount-002` produces exactly three unknown-identifier errors,
for `IntegerBitCount.unary_exec`, `IntegerBitCount.unary_false` and
`IntegerBitCount.unary_preserves_other`. The names remain required: checks were
not retargeted to the candidate's alternative namespace. The temporary
`sorryAx` reports in that failed driver arise from Lean's error recovery and do
not make the failed run accepted; they are not candidate theorem dependencies.

Independent review of this exact candidate found the bit-order definitions
faithful to the two pinned source clauses, the type/version/target notes accurate,
and no input-domain weakening or desired-output assumptions. All 31 existing
named Scalar theorem statements and seven ScalarText statements are unchanged.
The eight new named IntegerBitCount theorems, three generic unary execution
lemmas and three new helper definitions were inspected in the fresh replay
checkout: all 14 dependency reports contain only the allowed standard Lean
axioms (`propext`, `Quot.sound`, `Classical.choice`) or no axioms. This does not
accept the candidate with its missing required API. A repaired candidate must
pass a new fresh replay with v2 and the unchanged declaration obligations.
