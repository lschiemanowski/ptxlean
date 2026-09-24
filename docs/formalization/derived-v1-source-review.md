# Source review for insertion and three-input logic

This review concerns selected `bfi.b32` and plain `lop3.b32` forms in the pinned
PTX ISA 9.4 manual. The instruction anchors are
`integer-arithmetic-instructions-bfi` and `logic-and-shift-instructions-lop3`.
Review recipes bind those sections, the general operand and predication sections,
and all supporting code to exact hashes. Vendor text is reconstructed from the
local manual and is not distributed here.

## Bit-field insertion

The first word provides replacement bits; the second is the word being modified.
The third and fourth inputs are unsigned positions and lengths, each interpreted
through its low eight bits. Bit zero is the least significant bit. For output bit
j, use replacement bit j-pos exactly when pos <= j < pos+len; otherwise retain
base bit j. Only output positions 0 through 31 exist, so a field crossing the
upper boundary is clipped. Zero length and positions beyond bit 31 leave the
base unchanged. The manual's pseudocode explicitly masks the position and length;
the formal contract retains that operation on all 32-bit operand patterns rather
than adding a caller range premise.

The selected form was introduced in PTX 2.0 and requires SM 20 or higher. The leaf
selects ISA exactly 9.4 and a numeric SM feature floor of 20. It does not validate
architecture names or formalize `bfi.b64`. The `compute_bit` obligation quantifies
over all input words and all 32 valid output positions. This source-derived law
specifies the output independently of the candidate computation's construction.

## Three-input Boolean logic

For each bit position, the source convention gives the first input weight four,
the second weight two and the third weight one in an eight-entry truth table.
The table is an immediate integer in 0..255. A table encoding first-input
projection is 0xF0, second-input projection 0xCC, and third-input projection 0xAA.
The all-input `compute_bit` obligation fixes that ordering and covers all 256
tables; it is not merely a test of common AND/OR functions.

The typed interface stores the table as a `BitVec 8` operation parameter. It is
not a fourth runtime register read. Encoding appends the table as a word immediate;
decoding rejects a register there and rejects decoded immediate values above 255.
The source data operands still allow compatible word registers or already
converted immediates. Raw text, original literal parsing and register declarations
remain outside this typed decoder.

Plain `lop3.b32` was introduced in PTX 4.3 and requires SM 50 or higher. The leaf
selects ISA 9.4 and that numeric feature floor. The later `.and`/`.or` forms also
produce a predicate and admit a discarded word destination. They require a
different interface and are explicitly excluded, not represented by silently
omitting their predicate write.

## Shared proof and execution boundary

Both leaves use Pure32's existing incoming-state operand evaluation and guard
semantics. Sources may repeat or overlap the destination. The guard is distinct
from the table parameter and is the only predicate input. Enabled events retain
syntactic register-read order and repetitions; skipped events retain only the
guard read. The target condition still applies on a skip. The selected word
register and next program counter are the only changes; word memory, address
registers, predicates and other word registers are preserved.

The required universal statements separately bind results to computation,
lowering to actual operands, enabled and skipped transitions, destination and
frame properties, origin, one-step existence, determinism, and both directions
of exact typed decoding. Fresh replay must build and audit the actual candidate,
not just accept its claimed tests. A source-correct computation with an unfinished
proof is not an accepted leaf. The trial report records repairs and final outcomes.

## Adjudicating the reviewer's examples

The compiling insertion mutation omits masking the position. The reviewer's
position 256, length 1, replacement 1, base 0 is a valid distinguishing input:
masking makes the position zero. The independent driver also tests nonzero
positions with upper bits present.

The compiling logic mutation exchanges the weights of the first and third input.
The reviewer correctly locates and explains that fault, but its proposed table
0x80 example is invalid: table bits at indices four and one are both zero.
The AND function is symmetric in its inputs and cannot distinguish this swap.
A valid replacement is table 0xF0 with input bits (1,0,0): table bit four is one,
whereas bit one is zero. The independent fixture driver already tests that
projection. [Adjudication checks](../../formalization/review/derived-v1/adjudication.lean)
verify these concrete table-bit claims in Lean. Fault detection and counterexample
correctness are therefore reported separately.

Two controls and two faults cannot establish general reviewer accuracy. Neither
an advisory model verdict nor these checks prove that every source interpretation
is faithful or that a GPU implements the model. Final acceptance also requires
completed proofs under the pinned toolchain and coordinator inspection.

The accepting BFI candidate review also reuses the letter i for two different
indices and includes an invalid intermediate equivalence. With distinct names,
the source loop offset k and output position j satisfy j = pos + k. Then
0 <= k < len and j < 32 describe precisely the selected output bits
pos <= j < pos + len within the word. The verdict agrees with this corrected
reasoning, but the reviewer's algebraic wording is not used as evidence.
