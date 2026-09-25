# A sequential floating-point dot product

A dot product multiplies corresponding entries of two arrays and adds the
products. Its real-valued signature is

```text
dot : ℝⁿ × ℝⁿ → ℝ
dot(left,right) = ∑ᵢ left[i] * right[i]
```

This is the accumulation needed by a vector-input neuron. The component verifies
that accumulation alone; adding a bias, applying ReLU, connecting to a TorchLean
graph and implementing its backward are separate work. The introductory
[scalar ReLU example](relu-neuron.md) remains unchanged.

The [Stratic description](../../stratic/descriptions/dot-product.md) gives the
contract. This guide walks through the actual instructions, the termination
argument and the numerical bound.

## What executes

The kernel starts at positive zero and processes entries in increasing index
order. A multiplication and an addition are separate binary32 instructions:

```text
acc₀ = +0
productᵢ = round(left[i] * right[i])
accᵢ₊₁ = round(productᵢ + accᵢ)
```

Rounding is to nearest, with ties to even. This is not a fused multiply-add.
The accumulator is a 32-bit floating-point encoding stored in a word register.
An empty input still initializes the accumulator, stores positive zero, and exits.

The following is the complete instruction body of
[Dot.program](../../integration/torchlean/PtxBinary32/Dot.lean). The caller
supplies `%a0` and `%a1` as input byte addresses, `%a2` as the output byte address,
and `%r3` as the number of pairs. Register declarations and launch argument setup
are outside this instruction body and its execution proof.

```ptx
    mov.b32 %r4, 0;
loop:
    setp.eq.u32 %p0, %r3, 0;
    @%p0 bra done;
    ld.relaxed.gpu.global.u32 %r0, [%a0];
    ld.relaxed.gpu.global.u32 %r1, [%a1];
    mul.rn.f32 %r2, %r0, %r1;
    add.rn.f32 %r4, %r2, %r4;
    add.u64 %a0, %a0, 4;
    add.u64 %a1, %a1, 4;
    sub.u32 %r3, %r3, 1;
    bra loop;
done:
    st.relaxed.gpu.global.u32 [%a2], %r4;
    exit;
```

Word registers `%r0`–`%r4`, address registers `%a0`–`%a2`, and the Boolean
predicate `%p0` are separate register banks in the model. The labels resolve to
instruction positions 1 and 11. There are thirteen instruction positions, but
the loop body executes repeatedly.

The code uses only existing instruction definitions. Their recorded source
interpretations are described in [mixed execution](mixed-affine.md),
[binary32 instructions](binary32-instructions.md) and the
[instruction reference](../instructions/index.html). The new proofs establish
composition in the existing model; they are not an additional hardware or
instruction-fidelity audit.

## Supply the storage

Memory is an initialized list of 32-bit words, called the arena. `Stored` relates
a list of operand pairs to two contiguous slices of this arena. The list of pairs
is a proof-level description of corresponding inputs, not a requirement to
interleave the two arrays in memory.

For example, three pairs can occupy this layout:

| Word index | Byte address | Contents |
| --- | --- | --- |
| 0, 1, 2 | 0, 4, 8 | Left array |
| 3, 4, 5 | 12, 16, 20 | Right array |
| 6 | 24 | Output, initially arbitrary |

`initial` supplies the entry program counter, pointers and count. It preserves
the caller's memory and all other register values. In particular it does not
initialize the accumulator: the first actual `mov.b32` instruction does that.

`Bounds` requires `n < 2^32`, both input slices to fit in the allocation, and
each final one-past input address to fit in 64 bits. The output needs a separate
in-bounds, representable address. These conditions prevent truncated counts and
wrapped pointers from silently changing the computation. The one-past addresses
are calculated but never read. Every executed load or store retains the model's
alignment and bounds checks.

The reusable theorem permits overlapping input arrays and an output that aliases
an input word. This is sound because the only store occurs after all reads.
`other_memory` proves that every word except the output remains unchanged.
Use a disjoint output, as in the table, to preserve all inputs.

## Follow one iteration

At the loop head, `%r3` records the remaining number of pairs, `%a0` and `%a1`
point at the next inputs, and `%r4` holds an allowed accumulated result for the
processed prefix. Memory has not yet been changed.

For a nonempty suffix, the zero test is false. Two loads obtain exactly the next
stored pair. The multiplication may choose any result in its instruction
contract; the addition consumes that same product and the current accumulator.
Two pointer increments and a decrement restore the loop-head conditions for the
shorter suffix. The unconditional branch actually returns to position 1.

`Fold` records this ordered chain of allowed multiply/add results. It does not
assume that a kernel realizes the chain. `total_loop` proves that the actual
instruction transitions produce one; `correct` concludes that every terminal
run halts and stores an output satisfying `Fold`.

## Why it terminates for every permitted result

A single witness would show that an execution exists, but would not exclude a
nonterminating alternative. The reusable
[Total certificate](../../integration/torchlean/PtxBinary32/Total.lean) instead
checks every dispatch outcome. Each advancing instruction reduces the remaining
count by one; the final counted instruction must actually halt and satisfy the
specified final-state property. Faults and unsupported instructions cannot meet
the certificate. The original dispatch-existence theorem supplies at least one
outcome on eligible targets.

This certificate is a proof about the original instruction relation, not a
fuel-limited replacement for it. Floating-point result choices remain unrestricted
within the existing contracts, including their conservative NaN freedom.

Each nonempty iteration has ten instructions. The final zero test, taken branch,
store and exit have four; accumulator initialization contributes one. Thus:

```text
complete event count = 10*n + 5
```

`execution_exists` constructs a completed execution. `correct` proves its
postcondition and count for every completed run. `prefix_termination` proves
that every advancing prefix is shorter than this count and can finish, with
exactly the remaining number of events. `no_infinite_execution` excludes an
infinite sequence of advancing instructions. These are instruction-model results,
not claims about GPU scheduling or wall-clock time.

## Follow the numerical error

The [numerical layer](../../integration/torchlean/PtxBinary32/DotError.lean)
distinguishes an ideal input `lᵢ,rᵢ` from the finite real values `lhᵢ,rhᵢ` actually
encoded in memory. Each `Input` supplies bounds `elᵢ,erᵢ` on those two encoding
errors, and a product-range condition.

Starting with `a₀ = 0`, define the rounded real prefix solely from those initial
values:

```text
pᵢ = round(lhᵢ * rhᵢ)
aᵢ₊₁ = round(pᵢ + aᵢ)
```

`Safe` checks, at every prefix, the sufficient range condition

```text
|lhᵢ*rhᵢ| + eps(lhᵢ*rhᵢ) + |aᵢ| ≤ maxFinite
```

Here `eps(t)` is the existing binary32 half-ULP rounding allowance: half the local
spacing of representable numbers at `t`. `maxFinite` is the largest finite
binary32 magnitude. Together with the product condition, these guards let the
existing arithmetic theorems derive that both actual instruction results are
finite. The rounded prefixes are explicit expressions in the initial inputs;
the caller does not supply facts about unknown intermediate words.

For each term, the bound adds

```text
eps(pᵢ + aᵢ) + eps(lhᵢ*rhᵢ)
+ |lᵢ|*erᵢ + |rᵢ|*elᵢ + elᵢ*erᵢ.
```

The first two terms account for the two roundings; the remaining terms propagate
input encoding error through multiplication. Addition carries the previous
absolute error forward. `budget` sums these contributions over all terms.
`fold_accuracy` derives the interpretation and accumulated error for every
allowed result chain. `stored_accuracy` connects that statement to the actual
word stored by any completed instruction run:

```text
|storedReal - ∑ᵢ lᵢ*rᵢ| ≤ budget(inputs, 0).
```

The bound is absolute, so it remains meaningful when the exact dot product is
zero. It can be conservative and can be large under severe cancellation. No
uniform small relative error or bitwise PyTorch agreement is claimed.

## Checked boundaries and how to run them

[DotExamples.lean](../../integration/torchlean/PtxBinary32/DotExamples.lean)
checks these distinguishing cases:

- Empty input still writes positive zero, regardless of initial registers.
- Left-to-right `2^24 + 1 - 2^24` returns zero: the middle addition rounds away
  the one. Reordering the last two terms returns one. The real sum is one in
  both cases, so operation order cannot be erased from the implementation.
- The cancellation case has an actual 35-event execution from nonzero scratch
  registers and output storage.
- A nonempty exact-zero input satisfies the numerical range conditions, showing
  that the numerical domain is inhabited beyond the empty case.

After following the [README setup](../../README.md#run-the-checks-and-examples),
run from the repository root:

```sh
./scripts/check.sh
./integration/torchlean/check.sh
```

For a focused rebuild:

```sh
cd integration/torchlean
lake build PtxBinary32.DotExamples
```

The full integration check also audits the new public declarations, rejects proof
placeholders and unexpected axioms, and verifies dependency pins. These commands
check Lean proofs; they do not execute the PTX on a GPU.

The fragment uses one thread, isolated initialized word storage, PTX 9.4 and the
existing numeric sm_70-or-later target condition. A runtime must establish launch
arguments and freedom from interference. Concurrent or parallel reductions,
fused arithmetic, mixed precision, full byte-aliasing semantics and hardware
conformance are outside this component.
