# Review of the binary and unary bit leaves

The accepted slice consists of `and.b32`, `or.b32`, `xor.b32`, `not.b32` and
`cnot.b32`. Source interpretation was checked independently of Luna's explanation
against the pinned PTX 9.4 manual, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The relevant publisher sections are
[and](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-and),
[or](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-or),
[xor](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-xor),
[not](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-not)
and [cnot](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-cnot).
Section hashes, common operand/guard anchors and exact file hashes are in the
accepted-form ledger. Publisher links provide navigation; the local source hash
identifies the reviewed bytes.

AND, OR and XOR combine corresponding bits. Their Lean definitions use the
respective `BitVec 32` operators. `not` complements every bit; `cnot` tests the
whole word for zero and returns exactly one or zero. The definitions impose no
range or sign restriction and do not introduce integer-to-floating conversion.
The distinction between `not 0 = 0xffffffff` and `cnot 0 = 1`, along with high-bit
and nonzero cnot examples, is checked independently of the worker's own proofs.

All five forms require matching operand sizes in the source, without requiring
identical declared types. This typed layer assumes compatible 32-bit register
declarations and already decoded, converted word immediates. It does not parse
raw literals or validate declarations. Other widths and predicate-valued forms
are not implemented; `cnot.pred` is not a legal sibling being claimed missing.
The selected forms have PTX 1.0 introduction and no additional target feature
restriction. As in the existing Pure32 leaves, fetched steps deliberately select
ISA exactly 94 and numeric SM at least 10. This is not validation of a current
assembler target spelling or architecture suffix.

The coordinator inspected `compute`, `family`, `lower`, `result`, the typed
encoder/decoder and all public theorem statements. Lowering supplies the actual
operation and incoming operand values to the existing Pure32 transition. It
preserves guard and destination; no private substitute execution relation or
new instruction assumption is introduced. Sources may repeat or name the
destination. Enabled occurrences retain guard reads followed by every register
source; skipped occurrences contain only the guard read. No memory event is
invented. Fetched steps preserve instruction origin and target checks on either
guard outcome. These are direct operand records, not a complete PTX memory
independence or causality analysis.

The universal decoder inverse proves exactly successful decoding, not the error
classification of malformed inputs. Separate examples check both malformed
recognized spellings and unsupported spellings. Independent drivers also check
all operation spellings, guard preservation, repeated reads, source/destination
aliasing, nonzero program counters and the target boundary. Their original v1
had namespace ambiguities; v2 fixed qualification but exposed finite-index and
numeric-projection elaboration issues. V3 makes those types explicit. All three
versions and failures are retained; no expected outcome or semantic hypothesis
was weakened. These are coordinator evaluator repairs, not model semantic errors.

`Bitwise32` completed in one recorded Luna invocation. `UnaryBits32` required
three: two returned an incomplete decoder proof, and the final repair followed a
coordinator suggestion to split recognized mnemonic equalities before operand
shapes. No candidate proof was supplied or edited by the coordinator. Each final
saved patch was applied to a fresh checkout of its recorded base, built, checked
with the independent v3 driver, scanned for placeholders and unchecked axioms,
and audited for all 30 public definitions/theorems. Both fresh replays passed;
only Lean's standard logical axioms appear. The exact accepted patch is preserved
in each trial archive and was integrated without changing its leaf bytes.

Separate OpenRouter reviews are advisory evidence; their protocol failures and
findings are recorded in the reviewer-pilot report. The coordinator's source
inspection and independent proof replay supply acceptance. No model verdict is
being promoted into a source-fidelity theorem. Full instructions at other types,
complete-kernel execution, and hardware correspondence remain outside these leaves.
