# From encoded exponentials to normalized values

A stable softmax row subtracts a maximum, computes exponentials, sums them and
normalizes each exponential by that sum. The maximum and shifted-exponential
components are already separate verified pieces. This study explains the next
two pieces and the numerical interface between them. It does not describe a
single complete softmax kernel.

## The concrete parallel sum

The first sum uses the existing dense forward kernel with one output row, unit
weights, zero bias and no activation. In mathematical notation, its computation
is `1*u₀ + 1*u₁ + ... + 1*uₙ₋₁ + 0`. Its additions follow a balanced tree,
rounding at every node. The multiplications by one and final addition of zero
are actual instructions in that program; the proof does not erase them from
the execution. They preserve the real value of a finite word. Adding positive
zero can change a negative-zero encoding, so the numerical statement does not
promise bitwise identity with an imagined program omitting those instructions.

Why reuse this kernel? It already has proofs of actual address calculations,
shared-memory observations, universal completed-run correctness, safe accesses
and a completed admitted execution. Specialization keeps these difficult
connections intact. It also carries extra constant storage, loads and arithmetic.
This is an inspectable reference implementation; an optimized dedicated sum
would need its own instruction correspondence proof.

For n=2^depth inputs, with depth between zero and ten:

| Region | Contents |
|---|---|
| Global words 0 through n−1 | Encoded exponential inputs |
| Global words n through 2n−1 | Encoded positive-one weights |
| Global word 2n | Encoded positive-zero bias |
| Global word 2n+1 | Output |
| Shared storage | (depth+1)*n words, with a fresh plane for each level |

All n threads belong to one cooperating thread array: a group able to share
memory and wait at a group barrier. Every thread reaches each barrier, including
threads whose part of the reduction is already finished. The instruction list
has 42+16*depth entries per thread. The formal model supplies the initial thread
identity and these memory arenas. It does not verify a host allocator, launch
ABI, assembly toolchain or GPU hardware execution.

For four inputs, the arithmetic is

```
p₀ = round(1*u₀)        p₁ = round(1*u₁)
p₂ = round(1*u₂)        p₃ = round(1*u₃)
a  = round(p₀+p₁)       b  = round(p₂+p₃)
S  = round(a+b)
out = round(S+0)
```

Here `round` means nearest-even binary32 rounding. The code and execution
wrappers are [SumProgram.lean](../../integration/torchlean/PtxBinary32/SumProgram.lean)
and [SumExecution.lean](../../integration/torchlean/PtxBinary32/SumExecution.lean).
The universal theorem covers all completed admitted executions, including their
schedules and candidate read values. The existence theorem constructs one
completed execution with a valid memory graph. It is not a fairness theorem.

## Derive the sum's range and error

The input condition is finite encoded values with |uᵢ|≤2. It does not require
uᵢ≥0. Our conservative approximate-exponential relation allows tiny negative
values close to zero, and removing them from this proof would silently narrow
the permitted behavior.

[ShiftedExpRange.lean](../../integration/torchlean/PtxBinary32/ShiftedExpRange.lean)
shows that every output of the checked shifted-exponential sequence meets this
magnitude bound. Its actual base-two argument is nonpositive, so the exact
base-two exponential lies between zero and one. The instruction's uniform
absolute error of 5*2^-24 then bounds the output's magnitude by two. This range
argument does not need the natural-exponential error budget to be small.

At tree level k, a subtree contains 2^k inputs. The proof derives a magnitude
bound of 2^(k+1) for its rounded result. The two endpoint values are exactly
representable, and monotonic rounding cannot push an intermediate sum outside
that interval. Thus every addition in the supported row has input magnitude
at most 2048, well within binary32's finite range.

On this interval, half of one floating-point grid step is at most 2^-13. There
are n−1 internal addition nodes, giving the conservative absolute sum allowance

```
sigma = (n−1)/8192.
```

It is zero for a singleton and strictly below 1/8 for all supported rows. This
bound is intentionally simple. It counts only the tree's rounding error relative
to the exact sum of its actual encoded inputs; exponential approximation error
is separate. [SumTree.lean](../../integration/torchlean/PtxBinary32/SumTree.lean)
proves the finite ranges and allowance without asking callers to certify each
intermediate sum. [SumCorrect.lean](../../integration/torchlean/PtxBinary32/SumCorrect.lean)
connects it to the word actually stored by the fetched parallel program.

## The two normalization instructions

For numerator u and the actual computed denominator S, the sequence is:

```ptx
rcp.rn.f32 reciprocal, denominator;
mul.rn.f32 reciprocal, numerator, reciprocal;
```

This is a rendering of the typed instruction list. The destination doubles as
scratch and final output. It can reuse the denominator register, but must not
reuse the numerator register: the numerator is still needed by the second
instruction. A regression example demonstrates the failure: overwriting the
numerator in 2/4 produces (1/4)*(1/4)=1/16 rather than 1/2.

With finite S≥1/2 and |u|≤2, the rounded reciprocal R lies in [0,2]. Therefore
u*R has magnitude at most four. Both results are finite, and the output is
`round(u*round(1/S))`. Its error accounting retains two separate terms:

- Reciprocal error: `rho = eps32(1/S)`.
- Product error: `tauᵢ = eps32(uᵢ*round(1/S))`.

`eps32` is the half-grid-step rounding allowance. Theorems in
[NormalizeCorrect.lean](../../integration/torchlean/PtxBinary32/NormalizeCorrect.lean)
apply these bounds to the destination of every actual fetched two-step execution.
They also construct a finite-result execution and preserve unrelated registers,
address registers, predicates and memory. This is a scalar sequence; parallel
loads, broadcasts and output stores for normalization are still separate work.

## Keep the upstream errors visible

Let eᵢ be the ideal shifted exponential and deltaᵢ bound |uᵢ−eᵢ|. The exact
stable denominator is at least one because some score attains the maximum.
Define `D = sigma + sum(deltaᵢ)`. When D≤1/2, the computed denominator is at
least one half. That range is derived from the two preceding error bounds;
it is not an assumption that reciprocal execution happened to produce a finite
result.

The existing softmax composition then bounds each actual normalized coordinate
against eᵢ/sum(eⱼ) by

```
tauᵢ + (1+deltaᵢ)*rho + (deltaᵢ+D)/(1−D).
```

[SoftmaxNormalize.lean](../../integration/torchlean/PtxBinary32/SoftmaxNormalize.lean)
derives the reciprocal and product obligations from encoded arithmetic. The
exponential errors and total-error guard remain explicit. A later composed
softmax program must connect the maximum, exponentials, sum and normalization
through actual storage and scheduling, then instantiate the ideal weights from
the pinned TorchLean softmax specification. These component results do not
establish that complete program or its backward computation.

## Reproduce the checks

After provisioning the pinned Lean and TorchLean dependencies, run:

```sh
python3 integration/torchlean/check.py
```

The check builds the proofs, runs the executable regression cases and audits
public proof dependencies. Sum regressions include signed cancellation, subnormal
values, singleton rows and the largest supported numerical error allowance.
Normalization regressions cover register aliasing, instruction fetch and target
requirements. These are software checks; GPU execution and benchmarking remain
deferred.

The checked connector in [SumNormalize.lean](../../integration/torchlean/PtxBinary32/SumNormalize.lean)
initializes a separate scalar state with an original numerator in register 0, the
actual stored sum in register 1, and register 2 as scratch. It combines a
completed admitted sum run with actual normalization runs to prove the coordinate
error bound. This explicit register handoff is still a mathematical interface;
PTX loads, broadcast and combined kernel execution need their own implementation
and proof.
