# A ReLU neuron, from a real function to stored gradients

The README example is a single neuron, `F(x,w,b) = max(w*x+b,0)`.
The input `x`, weight `w`, and bias `b` are scalar tensors: each contains one
number. Both parameters are inputs to differentiation. This example uses the
actual pinned TorchLean multiplication, addition and ReLU graph nodes.

## Follow the derivative

Write `A = w*x+b`. For `A > 0`, the neuron returns `A`; for `A < 0`, it
returns zero. If a loss `L` uses this output, the backward receives
`upstream = ∂L/∂F` and returns the sensitivities of that loss:

| Condition | Gradient for x | Gradient for w | Gradient for b |
| --- | --- | --- | --- |
| `A > 0` | `upstream*w` | `upstream*x` | `upstream` |
| `A < 0` | `0` | `0` | `0` |
| `A = 0` | `0` by convention | `0` by convention | `0` by convention |

Setting `upstream = 1` asks for the gradient of the neuron itself. The Lean
argument is called `d`. This incoming sensitivity is an input to the backward,
not an extra trainable parameter.

At zero, varying the bias crosses a corner of ReLU, so the neuron has no ordinary
joint derivative with respect to its three inputs. A zero backward value there
is a convention, not a proof of differentiability. We therefore use a graph with
point-specific derivative evidence rather than claim that every node is globally
differentiable.

In [PtxReluVJP.lean](../../integration/torchlean/PtxReluVJP.lean),
`generated_vjp` proves the three formulas for the actual generated reverse sweep.
`checked_result` also proves that the checked backward succeeds and returns the
correct forward value. Both hold at all real inputs, including zero.
`graph_correct_at` supplies derivative evidence at each actual intermediate value
when `A ≠ 0`; `sensitivities_adjoint` then proves that the generated result is the
transpose of the mathematical derivative applied to the incoming sensitivity.
For a scalar output, this is the familiar chain rule.

## Follow the stored values

The PTX implementation is authored separately from TorchLean's automatic
backward construction. It uses two forward launches and four backward launches.
Each launch executes a single thread and returns before the next begins.
The complete instruction bodies appear in the [README](../../README.md#forward-ptx).

One initialized allocation holds the following 32-bit words. A byte offset is the
number of bytes from the allocation's start; the four-byte spacing keeps each
word aligned. Scratch words may initially contain arbitrary bits.

| Byte offset | Contents | Role |
| --- | --- | --- |
| 0 | x | Input |
| 4 | w | Weight |
| 8 | b | Bias |
| 12 | A | Affine scratch result |
| 16 | y | Forward output |
| 20 | upstream | Incoming gradient |
| 24 | db | Bias gradient and gated incoming gradient |
| 28 | positive zero | Constant used by gradient kernels |
| 32 | dx | Input gradient |
| 36 | dw | Weight gradient |
| 40 onward | trailing storage | Preserved |

The first forward launch computes `A = round(round(w*x)+b)` using the existing
multiply-add kernel. Multiplication and addition round separately; this is not a
fused operation. The second launch gates `A` into `y`.

The backward recomputes `A`, gates `upstream` into `db`, computes
`dx = round(round(db*w)+0)`, and computes `dw = round(round(db*x)+0)`.
It does not rely on saved forward scratch or output. The additions of positive
zero are actual instructions, retained to reuse the verified affine kernel;
the numerical proof includes their rounding behavior.

[ReluGate.lean](../../integration/torchlean/PtxBinary32/ReluGate.lean) implements the
gate with two unsigned word comparisons and two predicated moves. A predicated
move runs only when its Boolean condition holds. The gate clears the payload if
the test word is positive zero or has its sign bit set; otherwise it retains the
payload. Thus both signed zeros produce positive zero. The
[finite-value proof](../../integration/torchlean/PtxBinary32/Relu.lean) connects
these bit tests to strict positivity of the represented real number, including
very small nonzero values. Exceptional encodings still have a bit-level result,
but this gate makes no claim to implement a particular NaN policy for ReLU.

In [PtxReluKernel.lean](../../integration/torchlean/PtxReluKernel.lean),
`pipeline_correct` obtains the arithmetic of each stage from actual fetched
instruction runs, not from an assumed final formula. `pipeline_exists` constructs
a terminating execution for either sequence, for every input bit pattern and
arbitrary initial register contents, on an eligible target with the stated
allocation. `launch_memory_safe` proves that every executed memory access is
aligned and within the allocation. `pipeline_frame` preserves other allocations;
`Evaluation.inputs_frame`, combined with `pipeline_correct`, preserves the input,
parameters, incoming gradient and trailing storage.

The sequential launch model supplies completed, visible writes with no
interference between launches. A host runtime must establish that contract.
These theorems do not themselves verify a CUDA launch wrapper, a GPU scheduler,
or hardware conformance.

## Follow the error bounds

The ideal real inputs need not equal the real values encoded by their binary32
words. In [PtxReluAccuracy.lean](../../integration/torchlean/PtxReluAccuracy.lean),
`Inputs` names both versions, bounds their encoding errors, and imposes explicit
range conditions that keep the affine multiplication and addition finite.
The existing binary32 arithmetic theorems then derive an affine error budget
`E` and a finite rounded value `Ahat` satisfying `|Ahat-A| ≤ E`.
Finiteness and the intermediate error are conclusions, not additional promises
about the stored result.

ReLU cannot enlarge absolute error:

```text
|max(Ahat,0) - max(A,0)| ≤ |Ahat-A| ≤ E.
```

`stored_forward_accuracy` therefore bounds the stored forward output relative
to the actual TorchLean graph, even when rounding crosses zero.

The derivative has a jump at zero. For example, a slightly negative ideal `A`
and a slightly positive rounded `Ahat` produce different backward branches, even
though the two forward values are close. The backward theorem consequently
requires the sufficient condition `E < |A|`. Together with the derived affine
error bound this proves that both values have the same sign; it also implies
`A ≠ 0`. It does not assume branch agreement separately.

`BackwardInputs` adds this margin, a finite incoming gradient with a bound on its
encoding error, and range conditions for the two gradient products and their
zero additions. These conditions are functions of the initial inputs and the
specified rounded arithmetic, not assumptions that the final gradients are
correct. `stored_backward_accuracy` derives finite stored gradients and explicit
absolute error bounds for all three components of the actual TorchLean-generated
backward. `BackwardInputs.away` and `sensitivities_adjoint` give their ordinary
mathematical derivative interpretation on this domain.

Outside the margin condition, execution existence and the exact-real zero
convention still hold, but this numerical backward theorem does not apply.
The example does not differentiate the discrete rounding operation, promise
bitwise equality with PyTorch, or cover arbitrary tensors and concurrent kernels.
Lean checks the stated model and proofs; fidelity of the instruction contracts
and of the external launch assumptions remains a separate responsibility.

## Reproduce the checks

Follow the [README setup](../../README.md#run-the-checks-and-examples) once to
install the pinned toolchain and provision the pinned dependencies. Then, from
the repository root:

```sh
./scripts/check.sh
./integration/torchlean/check.sh
```

The second command builds the ReLU modules and audits their public declarations
alongside the retained squared-affine example. It rejects forbidden proof tokens
and unexpected axiom dependencies. This checks general proofs, rather than
executing a GPU benchmark. For a focused rebuild after editing this example:

```sh
cd integration/torchlean
lake build PtxReluAccuracy
```

That focused command is useful during development; the full integration check
also verifies dependency pins, source stability, and the explicit axiom audit.
