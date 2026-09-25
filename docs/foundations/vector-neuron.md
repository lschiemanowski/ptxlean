# A vector-input ReLU neuron

This example joins the [ordered dot product](dot-product.md) to the
[scalar ReLU example](relu-neuron.md). Its signature is

```text
forward  : (x : Real[n], w : Real[n], b : Real) -> Real
backward : (x : Real[n], w : Real[n], b : Real, d : Real)
           -> (dx : Real[n], dw : Real[n], db : Real)
```

Here `a = sum_i w[i]*x[i] + b` and `forward = max(a, 0)`. The backward's `d`
is an incoming loss sensitivity: how much the loss changes per unit change in
this neuron's output. For the derivative of the output itself, use `d = 1`.
With `g = d` when `a > 0`, and `g = 0` otherwise, the result is
`dx[i] = g*w[i]`, `dw[i] = g*x[i]`, `db = g`.

At `a = 0` this is TorchLean's chosen zero convention. The theorem identifying
it with the ordinary mathematical derivative requires `a != 0`. An empty vector
has sum zero; it still has a bias, output, and bias gradient.

## Two separately constructed computations

[PtxVectorVJP.lean](../../integration/torchlean/PtxVectorVJP.lean) constructs an
actual upstream TorchLean graph: elementwise multiplication, sum, scalar
addition, ReLU. TorchLean constructs the backward. `generated_vjp` proves its
coordinate formula, `checked_result` proves that graph validation returns
success, and `sensitivities_adjoint` identifies it with the mathematical
vector-Jacobian product away from zero. That product is the derivative applied
backward to `d`. The graph supports any fixed tensor shape, with coordinates
flattened in TorchLean's usual order; `[n]` gives the vector case.

[PtxVectorKernel.lean](../../integration/torchlean/PtxVectorKernel.lean) supplies
a separate reference implementation using already verified instruction programs.
For clarity it uses several launches, each with one thread. A launch means an
instruction execution followed by publication of its writes to the next launch
in the project's serialized storage model. No CUDA wrapper is supplied.

The forward uses three launches:

1. The 13-instruction dot-product loop reads contiguous weights and inputs,
   initializes its accumulator to positive zero, and computes left to right.
2. The seven-instruction affine kernel multiplies that result by an initialized
   `1.0f` and adds the bias. Both instructions round separately.
3. The eight-instruction gate kernel stores the positive affine value or zero.

The cache-free backward recomputes stages 1 and 2, then gates the incoming seed.
For each coordinate it launches the affine kernel twice, computing `g*w[i]+0`
and `g*x[i]+0`. These are actual multiplication and addition instructions, whose
rounding is included in the proofs. The total is `3 + 2*n` launches. This is a
simple reusable verification example, not an efficient GPU implementation.

The kernels and their PTX listings are explained in the linked dot-product and
scalar ReLU guides. `Stage.program`, `Stage.args`, and `registers` specify exactly
which instruction list and launch arguments are used here. No additional PTX
instruction semantics are introduced by this example.

## Storage you can inspect

A single allocation contains the following words. Every word has four bytes;
launch addresses are four times the indices in this table.

| Word indices | Meaning |
|---|---|
| 0 | dot-product scratch |
| 1 | initialized binary32 +1 |
| 2 | bias |
| 3 | affine scratch |
| 4 | forward output |
| 5 | incoming seed |
| 6 | gated seed, also the bias gradient |
| 7 | initialized binary32 +0 |
| `8 .. 8+n-1` | weights |
| `8+n .. 8+2*n-1` | inputs |
| `8+2*n .. 8+3*n-1` | input gradients |
| `8+3*n .. 8+4*n-1` | weight gradients |

Any trailing words are preserved. `Buffer n` describes the fixed part;
`words` appends the caller's trailing storage. No result is assumed to be in
scratch initially. All other register contents may also be arbitrary. The dot
launch supplies its count register explicitly. The length must be below `2^32`;
this also suffices to rule out 64-bit pointer wrap for this layout, including
one-past pointers in the empty case.

`run_exists` constructs actual terminating instruction runs for each stage.
`pipeline_exists` composes them into launches, independently of numerical range
conditions. `pipeline_correct` extracts arithmetic results from every actual
completed launch sequence. It does not assume those arithmetic results as a
substitute for execution. `gradient_values` handles an arbitrary list of gradient
stages, including repetitions, using the fact that gradient writes cannot change
their source values. `Evaluation.frame`, `launch_memory_safe`, and
`pipeline_frame` account for untouched words, valid accesses, and other allocations.

## What the numerical theorem says

[PtxVectorAccuracy.lean](../../integration/torchlean/PtxVectorAccuracy.lean)
compares stored binary32 words with real-valued tensors and the actual graph.
The supplied conditions describe initial inputs:

- Each weight/input word denotes a finite real number, with a bound on its
  difference from the intended real parameter/input.
- The ordered reduction and bias step satisfy explicit finite-range conditions.
  Their rounded expressions are calculated from initial values, not assumed
  properties of an unknown execution.
- Constants at slots 1 and 7 are exactly the words for +1 and +0.
- For backward, the incoming seed is finite and has a stated encoding error.
  Each gradient product and its addition of zero satisfy finite-range conditions.

Let `A` be the ideal real affine value, `Ah` the specified rounded affine value,
and `E` its proved absolute error budget. Forward accuracy is
`abs(max(Ah,0) - max(A,0)) <= E`: ReLU does not enlarge this error.

Backward additionally requires `E < abs(A)`. This proves both that `A` is nonzero
and that `Ah` chooses the same activation branch. The proof does not assume branch
agreement. Near the kink that condition can fail even when forward accuracy is
excellent. The theorem then makes no derivative-accuracy promise.

`BackwardAccuracy` states the finite stored bias, input and weight gradients,
with a separate absolute error bound for every coordinate. `BackwardInputs.generated`
identifies their real reference values with TorchLean's generated backward.
`stored_forward_accuracy` and `stored_backward_accuracy` apply these statements to
actual completed launch chains. `stored_backward_adjoint` packages the gradient
bounds with the ordinary-derivative theorem; `empty_forward` and `kink_backward`
check the empty and nondifferentiable boundary cases. Error-bound agreement does not mean bitwise
agreement with PyTorch. These results also make no claim about GPU execution,
concurrent reductions, fused operations, or mixed precision.

## Check and read

From the repository root, after provisioning the pinned integration dependencies
as described in [its README](../../integration/torchlean/README.md):

```sh
(cd integration/torchlean && lake build PtxVectorVJP PtxVectorKernel PtxVectorAccuracy)
bash integration/torchlean/check.sh
```

The second command builds the integration and checks the complete registered
theorem dependency audit, rejecting `sorryAx` and any axiom beyond the existing
allowlist of Lean's `propext`, `Classical.choice`, and `Quot.sound`.

A short reading order is `forward_value` and `generated_vjp`, then the buffer table
and `Stage.args`, then `pipeline_correct`/`pipeline_exists`, then `Inputs` and
`BackwardInputs`, and finally the two stored-accuracy theorems. Stratic's
**A vector-input ReLU neuron** description gives the same contracts at project
level; this guide supplies the extended walkthrough.
