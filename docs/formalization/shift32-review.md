# Source and proof review of the selected shifts

The accepted forms are `shl.b32`, `shr.u32` and `shr.s32`. The coordinator reviewed
NVIDIA's pinned PTX 9.4 [left-shift](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-shl)
and [right-shift](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#logic-and-shift-instructions-shr)
sections independently of the worker. The manual SHA-256 is
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`;
section hashes are in the accepted-form ledger. Publisher links navigate to the
source; hashes identify the bytes actually reviewed.

The right operand is an unsigned 32-bit count. Left and logical-right shifts
fill with zero; signed-right shift fills with the input sign bit. Oversized
counts are clamped to the width, not reduced modulo it. The implementation
handles counts below 32 with the respective `BitVec` shift and handles larger
counts directly, avoiding enormous host shifts. The signed large-count result
is all ones for a set sign bit and zero otherwise. Zero, 31, 32, 33, and the
largest unsigned count are checked, along with positive and negative bit patterns.

These forms were introduced in PTX 1.0 without an additional target feature
requirement. The leaf deliberately uses the existing exact-ISA-94, numeric-SM-10
slice, including for skipped fetched instructions. This does not validate GPU
names or current assembler support. The destination and first source are
compatible 32-bit words; the count is interpreted as unsigned. Declarations and
literal conversion belong to the caller. All words, repeated sources and
source/destination overlaps remain permitted. Other widths and `shr.b32` are
excluded from this exact typed spelling interface, without claiming they are
illegal PTX.

The coordinator inspected the definitions, lowering, decoder, theorem statements
and hypotheses. The shared Pure32 relation remains authoritative; there is no
replacement transition or added instruction axiom. The implementation reads
incoming operands, writes only the destination, preserves the guard and direct
operand records, and checks targets at fetched steps. Successful decoding is
characterized exactly by encoding; separate cases distinguish malformed known
spellings from unsupported spellings.

Luna produced the candidate in one invocation, with no feedback or candidate
edits by the coordinator. The original frozen driver incorrectly tried to decide
equality of whole states, which contain functions. The second driver attempted
to lift a word equality but had a tactic-scoping error. The third uses an explicit
word equality lifted through the state-write function. All versions retain the
same assertions and hypotheses. The failed replay and successful fresh replay
are preserved. The final replay built the exact saved patch, passed the independent
driver and audited all 28 public definitions/theorems using only standard Lean
logical axioms. No `sorry`, unchecked axiom or proof patch was accepted.

The GLM reviewer received a fresh fixed packet using the unchanged v4 protocol
and accepted it in one call, without findings or uncertainty. Coordinator
inspection agrees within the selected scope. Its opinion is advisory: it did
not run Lean, and agreement does not prove semantic fidelity. The recorded
OpenRouter cost is $0.001587735; Codex usage is recorded separately. The worker
contract and review protocol were frozen before their invocations, but evaluator
repairs mean this is not a fully frozen productivity measurement. One related
family does not establish general instruction coverage or reviewer accuracy.

The catalog links this leaf into complete arena programs. Existing scalar left
and unsigned-right shift result definitions agree for every input and count.
Whole-program proofs, concurrent PTX admission and hardware conformance remain
separate obligations. See the [retained trial](../../formalization/results/shift32/README.md).
