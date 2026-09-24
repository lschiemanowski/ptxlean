# Plain three-input logic: assisted continuation review

This review uses the same pinned PTX ISA 9.4 manual as the original trial
(SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`).
The `logic-and-shift-instructions-lop3` section was reread for this continuation.
Vendor text remains in the local source cache and is not distributed here.

## Source interpretation

Plain `lop3.b32` computes the same Boolean function independently at each of the
32 bit positions. Its immediate parameter selects one of 256 three-input truth
tables. The manual's three input patterns order the first input as the most
significant of the three table-index bits, the second as the middle and the third
as the least significant. Thus the index is 4a + 2b + c for input bits a, b, c.
This ordering distinguishes the projection tables 0xF0, 0xCC and 0xAA.
The universal `compute_bit` statement covers every table, every input word and
every valid output bit, without operand-range assumptions.

The table is a constant from 0 through 255; it is not another runtime register.
The typed interface therefore uses a `BitVec 8` operation parameter. Encoding
places its unsigned value in a 32-bit immediate operand. Decoding must reject a
register in that position and must check the immediate range before narrowing.
Both decoder directions matter: successful encoding must reconstruct the original
operation, and every successfully decoded statement must be exactly its encoding.
The latter excludes silent truncation of out-of-range table operands.

The selected form requires PTX 4.3 or later and SM 50 or higher. The formal step
selects ISA exactly 9.4 and a numeric SM floor of 50, including skipped steps.
It does not validate GPU architecture names. The later Boolean qualifiers that
also produce a predicate, and their discarded word-destination option, remain
excluded; they require different state effects. Their PTX 8.2 / SM70 requirements
are not applied to the selected plain form.

## Shared execution boundary

The Pure32 engine evaluates all three source operands in the incoming state,
allowing repeated registers and destination overlap. Only the destination and
next program counter change on an enabled instruction. A skipped instruction
advances the counter without a register write. Memory, address registers,
predicates and other word registers are preserved. The table parameter causes no
register read; occurrence metadata retains the guard and ordered source reads,
or just the guard when skipped. Existence and determinism concern one step;
they do not establish termination of an arbitrary program.

Inputs are typed compatible 32-bit registers or already converted immediate words.
There is no raw PTX parser, declaration validator, full ISA claim or hardware
conformance claim. The generic bit-vector helpers add mathematical facts about
Lean values only. Their width/range conditions are explicit and they do not
replace the instruction's source-derived output law.

## Proof review boundary

The earlier private conditional-observation helper had an incorrectly grouped
Boolean expression. The new shared helper explicitly equates two Boolean values;
its proof works for every width and index. The narrowing inverse requires that
the original number fit in the smaller width. Neither helper assumes a LOP3
result or decoder conclusion. All original instruction-level obligations remain
unchanged; the final candidate's completion and exact dependency checks are
recorded in the continuation report.

The reviewer's source opinion is advisory and recorded separately. Completion
requires Lean checking plus source/statement inspection; a model's acceptance is
not a proof of semantic fidelity. The original pilot's failures and unavailable
review verdicts remain historical facts, even if this continuation succeeds.

The final candidate retains the original eight-minterm computation. A minterm
selects one combination of three input bits; only that combination contributes
the corresponding table bit. The private observation helper now has the intended
Boolean equality, and the unchanged public output law follows by eight input-bit
cases. Both decoder directions are complete, using the eight-bit value bound or
the successful decode branch's range check as appropriate. Fresh replay passed
all original obligations and the full public dependency audit. The independent
GLM opinion accepted with no findings; its PTX introduction notes do not change
the formal interface's exact-9.4 version choice.
