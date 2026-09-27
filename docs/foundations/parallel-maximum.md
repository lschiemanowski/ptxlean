# A parallel maximum for stable softmax

Stable softmax first subtracts the largest score in a row. We now have a small
parallel component for that step. It works on a power-of-two number of finite
binary32 inputs, from one through 1024, using one cooperating thread array:
a group of threads that can exchange shared memory and wait at a common barrier.
It does not yet execute a complete softmax kernel.

The result is an original input word. Interpreted as a real number, it is at
least every input and equals one of them. This is exact selection, with no
rounding error. Both signs of zero and all finite subnormal values are included.
A subnormal is a nonzero value smaller than the smallest normal value of its
floating-point format. NaNs and infinities are outside this real-number theorem;
the bit computation remains defined for every 32-bit word.

## Why use integer instructions?

The model already supports integer comparison, XOR and register moves. These
suffice to compare finite binary32 encodings exactly. We therefore do not need
a new floating-point maximum instruction or another numerical provider.

Construct an unsigned integer key for each input:

- For a nonnegative encoding, flip its sign bit.
- For a negative encoding, flip every bit.

Within positive finite numbers, the encoding already increases with value.
Negative encodings run in the opposite direction; complementing them reverses
that order. Flipping the positive sign bit also puts the entire nonnegative
half above the negative half. Negative zero sorts just below positive zero,
although both represent the real number zero. This is intentional: positive
zero wins when both are present. Identical keys keep the left operand.

The nine-instruction pair selector is:

```ptx
// r4 and r5: inputs; r6: result; r8/r9 and p1: scratch
setp.ge.u32 p1, r4, 0x80000000;
xor.b32     r8, r4, 0x80000000;
@p1 xor.b32 r8, r4, 0xffffffff;
setp.ge.u32 p1, r5, 0x80000000;
xor.b32     r9, r5, 0x80000000;
@p1 xor.b32 r9, r5, 0xffffffff;
setp.lt.u32 p1, r8, r9;
mov.b32     r6, r4;
@p1 mov.b32 r6, r5;
```

This is a readable rendering of the Lean instruction list, not a complete
launchable PTX source file. Predicate p0, used to decide which threads are
active in a reduction round, is separate from selector scratch predicate p1.
The selector never changes p0 or an address register.

[`Maximum.lean`](../../integration/torchlean/PtxBinary32/Maximum.lean) proves
the key ordering from the decoded sign, exponent and fraction, including
subnormals and signed zeros. `choose_real` identifies the selected real value
with the mathematical maximum. The proof uses ordinary integer and real
lemmas, without a native bit-vector proof oracle.
[`MaximumSelect.lean`](../../integration/torchlean/PtxBinary32/MaximumSelect.lean)
connects that bit operation to the nine existing modeled instructions.

## Follow an eight-entry row

Suppose the stored scores are `[-7, -2, -9, -4, -8, -3, -6, -5]`.
The example deliberately has no nonnegative entry: zero would be an incorrect
initial maximum.

| Shared plane | Active writers | Values they publish |
|---|---:|---|
| 0 | all eight threads | -7, -2, -9, -4, -8, -3, -6, -5 |
| 1 | threads 0–3 | -2, -4, -3, -5 |
| 2 | threads 0–1 | -2, -3 |
| 3 | thread 0 | -2 |

Before plane 0, each thread loads its own global input. At every later level,
thread t reads cells 2t and 2t+1 of the previous plane and writes their maximum
to cell t of a fresh plane. Each plane reserves eight words, even when only
some are used. Every thread reaches every barrier, including inactive threads.
After the last barrier, thread zero loads the root and writes the global output;
all threads exit. A one-entry row has no reduction rounds but still publishes,
synchronizes, loads its root and stores the result.

For n=2^depth, shared storage contains at least `(depth+1)*n` words, and global
storage contains at least `n+1` words. Global cells 0 through n−1 are inputs;
cell n is the output. Plane k starts at shared word k*n. The program computes
byte addresses by multiplying these word indices by four. Its checked bounds
prevent wrapping and ensure alignment and valid array access.

Fresh planes are a deliberate first representation choice. They give every
shared location a unique writer and avoid an overwrite racing with an earlier
read. This costs more storage than an in-place reduction. Proving an in-place
variant or reducing storage is a separate task, not an implied performance result.

## What the execution proofs establish

[`MaximumProgram.lean`](../../integration/torchlean/PtxBinary32/MaximumProgram.lean)
is the supplied fetched instruction list. The address and control proofs
establish its actual load/store sites, addresses and active-thread conditions.
The visibility proofs use completed barriers and unique writers to identify
which actual earlier store supplies each admitted shared read. Input reads
observe initialization because the only global store is to the separate output.

[`MaximumUniversal.lean`](../../integration/torchlean/PtxBinary32/MaximumUniversal.lean)
proves that **every completed admitted candidate execution** stores the exact
selection-tree word. A candidate execution includes a schedule and proposed
load values; admission checks its memory graph against the existing ordering
rules. The proof does not assume the proposed loads already contain subtree
maxima. It derives those values by induction over actual prior stores, using
the fetched instruction effects. Finite input interpretation then gives the
attained real maximum. The input prefix is preserved, memory sizes are unchanged,
and every emitted memory access is valid in the allocated arena.

Separately,
[`MaximumExecution.lean`](../../integration/torchlean/PtxBinary32/MaximumExecution.lean)
constructs a finite schedule, a completed execution and an admitted memory graph.
This establishes existence, not eventual completion under every possible
scheduler. Safety of emitted accesses is also distinct from existence: a safe
prefix alone would not prove that the program can finish.

The formal machine supplies thread identities in register r0, the group size,
and list-backed global and shared arenas. Other initial registers and shared
contents may be arbitrary. Host allocation, launch/ABI correspondence, PTX
assembly, hardware conformance, GPU fairness and measured performance are not
proved here. The configuration is the project's PTX 9.4 / SM 70 target. The
integer selector introduces no new ISA semantics; its semantic fidelity rests
on the already reviewed integer and barrier/memory fragment.

## Connect it to shifted exponentiation

[`MaximumTree.lean`](../../integration/torchlean/PtxBinary32/MaximumTree.lean)
separates the arithmetic tree from execution. Because the root is an input word,
any common magnitude bound on inputs also bounds the maximum. In particular,
if every score has absolute value at most 2^124, the root m makes every score x
satisfy the shifted-exponential input conditions: x≤m and both magnitudes bounded
by 2^124. An attaining score has x=m, so the existing shifted-exponential theorem
returns exactly positive one for it.

This is the proved interface between two components. A combined fetched softmax
program still needs exponential storage, a sum with numerical bounds, reciprocal
and normalization, execution proofs and the final composed error theorem.
Arbitrary row lengths and masked rows require explicit policies. Padding with
zero is not valid for an all-negative maximum; duplicating an actual input would
preserve the maximum but needs its own checked layout and execution connection.

## Check locally

After provisioning the repository's pinned Lean/TorchLean dependencies:

```sh
python3 integration/torchlean/check.py
```

The integration check builds these modules, reruns the executable regression
checks and inspects every public declaration's axiom dependencies. Kernel checking
establishes validity of these formal proofs; source review addresses whether the
modeled instructions and memory rules faithfully describe the intended PTX fragment.
