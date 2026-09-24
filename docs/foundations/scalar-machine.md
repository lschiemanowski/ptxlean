# Executing a scalar program

The scalar machine executes integer instructions with registers, predicates,
computed addresses, branches, and explicit thread termination. Its concrete
memory mode is a sequential arena interpreter. This supplies a useful execution
discipline for kernels whose accessed memory is owned or otherwise suitably
isolated. It is not a replacement for PTX's weak-memory model.

Start with [`Ptx/Scalar.lean`](../../Ptx/Scalar.lean), then read the typed mnemonic
boundary in [`Ptx/ScalarText.lean`](../../Ptx/ScalarText.lean). The definitions use
the pinned Lean toolchain and bundled libraries. Their relationship to NVIDIA's
[pinned PTX 9.4 manual](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html) is explained
below. Kernel checking establishes properties of these definitions; it does not
establish that the definitions faithfully describe every PTX execution.

## A state and one instruction

`Scalar.State` contains a program counter, a 32-bit register bank, a 64-bit address
register bank, predicates, and a list of 32-bit memory words. Register identifiers
are natural numbers in three separate typed banks. Every initial register value,
predicate, and memory word is an explicit caller input. The model does not assert
that PTX registers start at zero. A source frontend would additionally have to
validate declarations and initialization requirements; this is not implemented.

An `Instr` pairs an operation with either an unconditional guard or a predicate
register and its polarity. `Operand32` and `Operand64` select a register or an
immediate value. `eval` reads source values from the pre-instruction state and
writes destinations in the successor state, so source/destination aliasing does
not change which source value is used. `update_same` and `update_other` express
register replacement precisely.

For a supported instruction whose guard is false, the machine advances the PC
without executing the operation. `eval_skipped` proves this behavior. The dynamic
trace retains that skipped occurrence, its PC, and the guard-register read. An
explicit `unsupported` operation is rejected before checking its guard, because
the model has not established whether the unknown operation permits predication.

## Exactly which instructions are represented

The following spellings are the canonical forms accepted by the typed decoder.
Only the listed operand sizes and qualifiers are supported.

| Canonical forms | Machine behavior | Pinned source |
| --- | --- | --- |
| `mov.b32`, `mov.b64` | Copy a register or immediate of the matching width. | [mov][mov] |
| `add.u32`, `sub.u32` | Arithmetic modulo 2^32, without saturation or carry state. | [add][add], [sub][sub] |
| `mul.lo.u32` | Retain the low 32 bits of the product. | [mul][mul] |
| `and.b32`, `or.b32`, `xor.b32` | Bitwise operations. | [and][and], [or][or], [xor][xor] |
| `shl.b32`, `shr.u32` | Zero-filling shifts by an unsigned 32-bit count; counts at least 32 yield zero. | [shl][shl], [shr][shr] |
| `add.u64` | Address-register arithmetic modulo 2^64. | [add][add] |
| `cvt.u64.u32` | Zero-extend an unsigned 32-bit value into an address register. | [cvt][cvt] |
| `setp.eq.u32`, `setp.ne.u32`, `setp.lt.u32`, `setp.le.u32`, `setp.gt.u32`, `setp.ge.u32` | Unsigned comparison with one predicate destination. | [setp][setp] |
| `ld.relaxed.gpu.global.u32`, `st.relaxed.gpu.global.u32` | Aligned four-byte access through an evaluated 64-bit byte address; store data must come from a 32-bit register. | [ld][ld], [st][st] |
| `bra`, optionally predicated | Set the next PC to a resolved label target. | [bra][bra] |
| `exit`, optionally predicated | Terminate this scalar thread. No barriers or other participants are represented. | [exit][exit] |

The machine does not support signed arithmetic, saturation, carry flags, wide or
high-half multiplication, general 64-bit bit operations, packed arithmetic,
floating point, atomics, fences, barriers, asynchronous instructions, or warp
collectives. `bra.uni` is excluded because its uniformity requirement concerns
other active threads. PTX's barrier consequences of `exit` have no instance in
this no-barrier machine. The integer/control forms above are longstanding PTX
operations; the selected relaxed global-memory forms require an eligible
`sm_70` or later target. Target and launch validation are separate responsibilities.

`add_modulo`, `sub_modulo`, and `mul_low_modulo` expose the exact natural-number
meaning of the 32-bit arithmetic. `add64_modulo` makes address wrapping explicit.
The shift implementation deliberately tests the entire unsigned count rather
than masking its low five bits. `shift_left_clamped`, `shift_right_clamped`, and
`shift_boundary_examples` cover the width boundary. For example, shifting 1 left
by 32 yields 0, not 1. `unsigned_wrap_examples` checks overflow and underflow
examples with kernel-reduced proofs.

## Byte addresses and invalid accesses

An address register holds a `BitVec 64`; it is not a mathematical natural-number
pointer. `add.u64` may wrap. The chosen arena interpretation maps byte address
`4*i` to memory word `i`, with arena base address zero. It has no virtual aliases,
allocation lifetime, pointer provenance, host memory, or alternative state spaces.
Connecting an actual allocation to this arena requires an external mapping and
appropriate ownership or isolation conditions.

`addressIndex` first checks alignment, then bounds. A misaligned pointer produces
`Fault.misaligned`; an aligned index beyond the arena produces
`Fault.outOfBounds`. The successful branch is characterized by
`addressIndex_ok_iff`. `validAddress_bytes` proves that success covers all four
bytes, not only the first byte. A store replaces an existing word and cannot
resize the arena. Computed pointers therefore need real arithmetic/bounds proofs
in kernel verification; they do not inherit safety merely from being typed.

The instruction evaluator uses an indexed list lookup after the successful
bounds check. Its internal total lookup default is unreachable on that branch;
it does not assign a value to out-of-bounds loads. `eval_memory_safe` and
`step_memory_safe` establish safety for every emitted memory effect.

These fault statuses are explicit outcomes of this safe fragment interpreter.
They do not claim that NVIDIA specifies a particular trapping behavior for every
invalid PTX memory access.

## Fuel, completion, and traces

`step` fetches one instruction using the PC and returns one of four outcomes:

- `next`: successor state and a dynamic occurrence;
- `halted`: state and the executed exit occurrence;
- `fault`: an invalid PC or memory-access reason;
- `unsupported`: an instruction spelling outside the represented semantics.

Falling off the instruction list is an invalid-PC fault, not implicit success.
A branch target is checked when the machine next fetches it. Thus a budget ending
immediately after a branch can report exhaustion before a later invalid-PC fault
is discovered. Source label resolution should reject invalid targets before
execution; the machine still protects the fetch boundary.

`run fuel program state` consumes one unit per dispatch, including an instruction
skipped by predication and an explicit exit. Its result contains the final state,
a status, and a list of occurrences. `Stop.exhausted` means only that the budget
was consumed. It does not mean that the program terminated, faulted, or could
never finish. A claim of completion must establish `Stop.halted`.

`Runs` gives an inductive derivation of the same finite execution behavior.
`runWith_sound` builds a derivation from the executable runner; `Runs.exists_run`
shows that every derivation is realized by some finite budget. Exhausted prefixes
are explicit constructors of the relation. `runWith_trace_length` bounds emitted
occurrences by the dispatch budget. `run_add` splits a concrete execution budget
while preserving exact states, statuses, and trace concatenation. Its `resume`
operation continues only exhausted results, never terminal or error results.

Every memory effect in every produced trace is aligned and in bounds relative
to the original arena extent. `run_trace_safe` proves this even for a prefix
that later exhausts its budget or faults. `run_memory_length` supplies the needed
arena-length invariant. This safety result does not assert that a faulting run
has completed successfully; unsuccessful accesses produce a fault instead of an
accepted memory effect.

## Candidate reads and the weak-memory boundary

The concrete `step` and `run` read the current sequential arena. `stepWith`
optionally replaces a load's value with an explicitly supplied candidate value;
`runWith` supplies these choices by dynamic dispatch index. Candidate loads
still check their addresses. Skipped instructions and non-load instructions
consume a dispatch position but ignore its candidate value.

The resulting traces record executed instructions, actual memory values and byte
addresses, directly read/written register identifiers, predicate reads, and
whether each operation executed. This exposes the computations that produced
store values, addresses, and control flow. It is useful input to a future
candidate-execution construction and dependency analysis. It is not yet a formal
PTX data/address/control dependency relation.

An arbitrary candidate load can affect a later store or branch. Such a trace is
not admitted merely because `runWith` terminates or its addresses are safe.
In particular, checking the earlier restricted `Graph.Valid` predicate alone
would not discharge the no-thin-air obligation for these newly expressible
register-dependent programs. No theorem in the scalar machine makes that claim.
The concrete sequential mode gives values from an existing memory state at every
step. General weak-memory admission and a semantic bridge from these richer
traces require additional work and must state their assumptions explicitly.

## The typed mnemonic boundary

`Text.Statement` contains a predicate guard, a mnemonic string, and typed operand
tokens. A memory operand explicitly carries brackets through its `Token.memory`
category; a destination must be a register of the required bank; a branch operand
is a resolved label token. The token's numeric PC is an internal representation
of the resolved label, not valid textual PTX branch syntax.

`Text.decode` accepts only the supported mnemonic/operand combinations. Unknown
qualifiers and opcodes return `unsupportedMnemonic`; wrong operand shapes for a
known mnemonic return `invalidOperands`. Bare `ld.global.u32` is deliberately
rejected: omitting a memory-order qualifier denotes a weak form in PTX and must
not silently mean the supported relaxed form. Immediates are already typed bit
vectors, so lexical numeral syntax and range validation belong to the preceding
unimplemented frontend.

The scalar interpreter also permits an immediate store as an internal convenience.
PTX `st` requires its data operand to be a register, so this internal form is
excluded by `Text.Supported`, rejected by the decoder, and encoded with an
explicit `internal.store-immediate.u32` marker rather than a PTX mnemonic.
A frontend must insert an appropriate register move to represent such a constant
store as actual instructions; no lowering-equivalence theorem is claimed here.

`Text.encode` chooses one canonical mnemonic and token sequence for each supported
machine instruction. `decode_encode` proves that decoding this encoding recovers
the exact instruction, including its predicate. `decode_supported` proves that a
successful decode cannot manufacture an unsupported operation. These are boundary
proofs for a typed instruction fragment. They do not establish parsing or assembly
of a complete PTX source file, directive handling, register declarations, label
resolution, or target validity.

[add]: ../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-add
[sub]: ../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-sub
[mul]: ../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-mul
[and]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-and
[or]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-or
[xor]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-xor
[shl]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-shl
[shr]: ../../references/nvidia/ptx-isa-9.4/index.html#logic-and-shift-instructions-shr
[setp]: ../../references/nvidia/ptx-isa-9.4/index.html#comparison-and-selection-instructions-setp
[mov]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-mov
[cvt]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-cvt
[ld]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld
[st]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st
[bra]: ../../references/nvidia/ptx-isa-9.4/index.html#control-flow-instructions-bra
[exit]: ../../references/nvidia/ptx-isa-9.4/index.html#control-flow-instructions-exit
