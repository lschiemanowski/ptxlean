# Selection and signed integer leaves

Selection chooses one of two 32-bit words using a true-or-false predicate
register: `selp.b32` copies the first source when the predicate is true and the
second otherwise. This selector is separate from the instruction guard, which
can skip the entire instruction. The selector uses a positive predicate register;
positive and negated instruction guards are supported.

Signed minimum and maximum interpret each 32-bit word as a two's-complement
integer, ranging from −2147483648 to 2147483647. `min.s32` copies the source with
the smaller signed value, and `max.s32` copies the larger. A high leading bit
therefore denotes a negative value rather than a large positive integer. Every
32-bit pattern is supported; there is no nonnegative-input restriction.

These leaves reuse the pure-family execution mechanism. Sources can be register
values or already decoded 32-bit immediate values. They are read before the
single destination is written, including when sources repeat or name that
destination. Executed occurrences retain all direct operand reads in argument
order; skipped occurrences contain only the guard read and no write. No leaf
accesses memory. Actual fetched steps require the selected PTX 9.4 version and
the numeric target-feature floor `sm_10`; this is not a validator for target
names or a claim that a current assembler accepts historical targets.

The typed text boundary accepts exactly `selp.b32`, `min.s32`, and `max.s32`,
with word-register destinations and the required operand categories. It rejects
other widths, saturation modifiers, packed forms and extra qualifiers. It is
not a raw-text lexer, register-declaration checker, or literal-expression parser.
The caller must supply registers compatible with the chosen instruction type.
Each decoder must preserve instruction guards and have a universal encode/decode
round trip, independently checked against the source meaning of each mnemonic.

Worker acceptance requires completed all-input proofs, exact fetched-instruction
origin, state frames, existence, deterministic results and independent checks
for high-bit signed comparisons, selection, aliasing, skipped metadata and
unsupported text. A type-correct proof establishes its Lean statement; separate
source review establishes how the definitions represent the pinned manual.
These leaves add no memory-order, kernel-termination or hardware-conformance claim.
