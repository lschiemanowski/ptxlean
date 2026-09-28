# Parallel softmax backward

A softmax backward pass answers this question: if a surrounding computation is
sensitive to each softmax output, how sensitive is it to each input score?
For real scores `x`, let `p = softmax(x)` and let `g` be the incoming
sensitivities. The answer is

```
q = sum_j p_j * g_j
inputGradient_i = p_i * (g_i - q).
```

This is a vector–Jacobian product (VJP): it combines the derivatives of all
outputs using `g` as their coefficients. The reference is the pinned TorchLean
softmax backward specification, whose existing theorem identifies it with the
true derivative of the real function. The PTX program is supplied separately.
It approximates this derivative; it does not differentiate floating-point
rounding or the approximate exponential used by the forward implementation.

## What executes

Start with the **actual stored outputs** of the
[parallel forward pipeline](softmax-forward.md), denoted `pHat`, and a supplied
row of encoded incoming sensitivities. Three separate parallel launches follow:

1. A balanced dot-product reduction computes `qHat` from `g_j * pHat_j`.
   Each leaf multiplies two loaded binary32 words; each tree node adds its two
   rounded children. Reusing the dense reduction adds a final positive-zero
   bias. This preserves the finite real result but need not preserve a negative
   zero's bit pattern.
2. Each lane loads its own `g_i` and the stored `qHat`, multiplies `qHat` by
   exact minus one, adds this to `g_i`, and stores a difference.
3. Each lane loads its stored `pHat_i` and difference, multiplies them, and
   stores the input gradient.

Binary32 is the usual 32-bit floating-point format. The arithmetic above uses
nearest-even rounding. Difference deliberately reuses the existing multiply and
add instruction rules; this work does not add a subtraction instruction leaf.
There is no fused multiply-add or fused forward/backward kernel. Parallel
reduction barriers and their memory contracts come from the existing dense
implementation. The pointwise passes allow arbitrary lane interleavings, with
one writer per output and read-only source regions.

For a row of `n` words, backward storage is:

| Word indices | Contents | Introduced |
| --- | --- | --- |
| `0 .. n-1` | Actual forward outputs | Retained from forward |
| `n .. 2n-1` | Incoming sensitivities | Supplied input |
| `2n` | Positive-zero bias | Backward entry |
| `2n+1` | Dot-product output | Backward entry, then written by reduction |
| `2n+2 .. 3n+1` | Differences | Zero-filled scratch before difference pass |
| `3n+2 .. 4n+1` | Input gradients | Zero-filled scratch before multiplication pass |

Forward scratch is released before backward. The entry theorem identifies the
new arena as `forward.take n ++ incoming ++ [0, 0]`: the retained prefix contains
exactly the produced words. Each later extension preserves the entire previous
arena. Allocation and storage views do no gradient arithmetic. Original inputs and values passed between launches come from actual fetched
loads. Register intermediates come from actual arithmetic instructions, and
values passed to the next phase come from actual stores.

Entry address registers and completed phase boundaries are explicit interfaces
of the model. They do not implement CUDA argument passing, allocation, launch,
waiting or device visibility. Consequently this is a composed execution proof,
not a claim about a deployed GPU binary.

## Range conditions and the error bound

The row length is `n = 2^d`, with `d <= 10`: one nonempty row of at most 1024
entries. Original scores are finite and have magnitude at most `2^124`.
Accuracy also requires the existing forward guard: the accumulated exponential
and sum error allowance is at most one half. That condition derives a safe
normalization denominator. Incoming sensitivities are finite and bounded by
`2^60`. They may be signed; no positivity condition is imposed on them.

The proof **derives** a magnitude bound of four for every actual forward output.
It then derives bounds of `2^62` for leaf products, `2^72` for the dot result,
`2^73` for differences and `2^75` for final gradients. These are conservative
representability bounds, not estimates of typical neural-network values. The
choice of `2^60` leaves ample room for accumulation while keeping the same
reusable binary32 range arguments. Intermediate finiteness is proved from these
original input conditions, never supplied as a successful-execution assumption.

Let `epsilon_i` be the forward theorem's error allowance for `pHat_i` relative
to ideal `p_i`. Let `sigmaDot` be the sum of rounding allowances at **every actual
leaf multiplication and tree addition**. At each node the allowance is
`eps32(exact operation on its rounded inputs)`, where `eps32` is half the
floating-point grid spacing. This retains the reduction's actual operation
order, including cancellation and tiny values.

For ideal `q = sum_j p_j*g_j`, define

```
Q = sigmaDot + sum_j abs(g_j) * epsilon_j
subError_i = eps32(g_i - qHat)
difference_i = round32(g_i - qHat)
mulError_i = eps32(pHat_i * difference_i).
```

Every stored gradient has absolute error at most

```
mulError_i
+ abs(g_i - q) * epsilon_i
+ abs(pHat_i) * (subError_i + Q)
```

against the true TorchLean VJP. Multiplication of the finite dot by minus one is
exact as a real value, so it needs no additional error term. The incoming
reference is the **exact real interpretation of the supplied words**; an error
from quantizing some earlier real sensitivity is not silently included. The
reusable abstract backward bound supports such an extra error, but this composed
interface sets it to zero by choosing the stored values as its reference.

The theorem covers every result permitted by the existing forward approximation
relations, including their conservative tiny negative outputs. It does not
assume that computed weights are positive or sum to exactly one. This is an
absolute-error guarantee, not bitwise agreement with a particular PyTorch
backend. As with forward, Lean checking validates the stated formal model;
source fidelity and hardware conformance remain distinct questions.

## Correctness, existence and safety

`SoftmaxBackward.correct` recovers the actual dot/difference/product instruction
relations and preserved input regions from every completed admitted backward
execution. Here *admitted* means that the emitted loads and stores satisfy the
existing memory model, rather than being assigned convenient values.
`PtxTorchLean.SoftmaxBackward.correct` combines this execution evidence with the
forward theorem to bound every final stored gradient against TorchLean.

Existence is separate. `SoftmaxBackward.execution_exists` constructs all three
backward launches for arbitrary input words, including exceptional floating-point
values. `full_execution_exists` constructs a complete forward/backward execution
from the original finite-score domain, without the forward accuracy guard or any
incoming finiteness assumption. `accurate_execution_exists` combines that
construction with the stronger accuracy conditions. A witness schedule is not a
scheduler fairness or GPU progress theorem.

`SoftmaxBackward.access_safe` retains actual completed phase traces and proves
allocation bounds and alignment for their emitted memory accesses. The
underlying launch relations separately retain memory admission. Read-only
prefix preservation and unique destination ownership follow from the fetched
programs and the existing pointwise contracts.

## Reading and checking

- [SoftmaxBackwardDot.lean](../../integration/torchlean/PtxBinary32/SoftmaxBackwardDot.lean) specializes the existing reduction to the actual stored operands.
- [PointwiseProgram.lean](../../integration/torchlean/PtxBinary32/PointwiseProgram.lean) supplies the explicit difference instruction sequence.
- [SoftmaxBackward.lean](../../integration/torchlean/PtxBinary32/SoftmaxBackward.lean) connects the three launches and proves storage correctness, existence and safety.
- [SoftmaxBackwardFull.lean](../../integration/torchlean/PtxBinary32/SoftmaxBackwardFull.lean) connects the actual forward prefix to backward entry.
- [BackwardDot.lean](../../integration/torchlean/PtxBinary32/BackwardDot.lean) and [SoftmaxBackwardNumeric.lean](../../integration/torchlean/PtxBinary32/SoftmaxBackwardNumeric.lean) derive finite intermediate values and local rounding bounds.
- [PtxSoftmaxBackwardReference.lean](../../integration/torchlean/PtxSoftmaxBackwardReference.lean) identifies the actual TorchLean VJP and derives the stored forward-weight bound.
- [PtxSoftmaxBackward.lean](../../integration/torchlean/PtxSoftmaxBackward.lean) states the full stored-gradient accuracy theorem.

From the repository root, with the pinned dependencies already provisioned:

```sh
python3 integration/torchlean/check.py
```

This builds all integration proofs, reruns executable fixtures and checks exact
public dependency reports. No GPU run or benchmark is involved. To run just the
new backward interpreter fixtures:

```sh
cd integration/torchlean
lake --no-cache build PtxBinary32.SoftmaxBackwardExecutionChecks
lake --no-cache env lean PtxBinary32/SoftmaxBackwardExecutionChecks.lean
```

Those fixtures exercise the actual three phases, interleaved pointwise schedules
and trace replay. One case uses weights `(1/4, 3/4)` and sensitivities `(2, -2)`,
producing gradients `(3/4, -3/4)`; another checks constant sensitivities.
Separate dot fixtures cover cancellation and negative zero; numerical fixtures
include subnormal values. These finite tests complement the general proofs.
`SoftmaxBackward.Checks.singleton_exact` additionally proves that **every**
supported complete singleton forward/backward execution stores real gradient
zero, for arbitrary allowed score and sensitivity; `singleton_exists` constructs
such an execution. Neither theorem promises a particular zero-sign bit.

Masking, arbitrary row sizes, fused kernels, GPU progress, execution and
benchmarking remain outside this fragment.
