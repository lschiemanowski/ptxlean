# TorchLean integration feasibility audit

Audited 2026-09-23. The initial source inspection was followed by an isolated
Lean 4.34 integration build described below. The root PTX toolchain was not
changed. The earlier exploratory project was not used as a design source.

## Source and compatibility

The authoritative repository is [lean-dojo/TorchLean](https://github.com/lean-dojo/TorchLean).
The inspected revision is `de3192df4779877ceb65cfe470a4d4ce9d480a5b`, dated
2026-09-21 (`Fix FloatLib API documentation link`). All links below identify that
revision, not a moving branch. A shallow checkout was inspected directly;
search-engine summaries had older version information and were not used for pins.

| Dependency | Inspected upstream | Current ptxlean baseline |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.34.0` | `leanprover/lean4:v4.33.0` |
| mathlib | tag `v4.34.0`; manifest commit `5ed2965256430c3649e86755f9576b54eca72435` | No dependency |

Sources: [toolchain](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/lean-toolchain), [Lake package](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/lakefile.lean#L449),
[resolved manifest](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/lake-manifest.json). These versions differ. The isolated integration package successfully builds this
exact upstream revision under Lean 4.34; root PTX compatibility remains untested.
A joint package must choose and test a common toolchain before changing the main
project's pin. It could evaluate a ptxlean toolchain migration;
using an older upstream revision would require a new coverage audit rather than
assuming the same APIs and proofs exist there.

## What automatic backward construction actually provides

An output seed is a tensor of weights on the outputs; a vector-Jacobian product
(VJP) returns derivatives of their weighted sum. TorchLean has three relevant
surfaces, with different guarantees:

1. **Application execution.** `TorchLean.autograd.vjp` differentiates a recorded
   tensor program. `TorchLean.autograd.model.vjp` returns both model-state and input
   gradients. These are `IO` operations using registered primitives; they are not
   a theorem-generating transformation of arbitrary Lean functions. See
   [function API](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/API/Autograd/Function.lean#L70),
   [model API](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/API/Autograd/Model.lean#L213), and
   [API guarantees](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/API/Autograd/README.md#L184).
2. **Proof-carrying graphs.** `Proofs.Autograd.DGraph` stores graph derivative
   certificates and retains them under composition. `DGraph.toTypedGraph` selects
   an output for the checked runtime; `DGraph.vjpChecked_adjoint_fderiv` identifies
   a successful reverse result with the mathematical VJP over real numbers.
   Crucially, it takes successful checked execution as a premise. Domain
   validation can reject an input; this theorem alone does not prove success.
   See [the complete bridge](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Runtime/Link/GraphComposition.lean).
3. **Proof automation.** Importing `NN.Tactic.Autograd` supplies `by autograd`,
   registered derivative rules and tensor/explicit-graph certificate assembly.
   New primitives require proved local rules; domain conditions must be discharged.
   See [tactic documentation and examples](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Tactic/README.md#L36).

There is a lower-level result with a stronger success conclusion for its specific
construction: `Proofs.Autograd.Algebra.Graph.backwardDenseAll_lowerGraphToTape_adjoint_fderiv_at`
proves that the exact reverse sweep on `lowerGraphToTape` returns `.ok` and that its
input derivatives equal the mathematical VJP. It requires a
`GraphFDerivCorrectAt` certificate for the graph at the actual input. Its seed is
an arbitrary tensor at a selected typed output, so it is not limited to scalar
losses. See [exact theorem](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Runtime/Link/BackwardDenseGraph.lean#L408).
This success result concerns the pure exact tape computation, not PTX execution
existence, GPU progress, or the checked application's domain-validation path.

`GraphFDerivCorrectAt` requires each local forward operation to have the specified
mathematical derivative at the intermediate values encountered, and its local
forward derivative computation to agree with that derivative. Algebraic agreement
between forward and reverse derivative rules alone does not discharge this
analytic obligation. See [certificate definitions](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Tape/Core/FDeriv.lean#L978).
The general checked runtime bridge additionally requires equality between the
proof graph's operation data and the executed graph's data:
[`TypedGraphWithData.vjpChecked_adjoint_fderiv`](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Runtime/Link/Checked.lean#L126).

## Coverage and boundaries

The [upstream coverage account](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Coverage.lean) lists arithmetic,
matrix and shape operations, smooth elementwise functions, softmax, normalization,
attention and selected transformer compositions. Domain-sensitive operations have
conditions: for example, ReLU's classical derivative theorem excludes its corner
at zero. This is useful infrastructure, not full model coverage. The same account
explicitly leaves model-to-runtime lowering and complete model stacks among the
remaining obligations. Listed coverage was not independently rebuilt in this audit.

A concrete [cross-entropy derivative certificate](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/NN/Proofs/Autograd/Tape/Nodes/Losses/CrossEntropy.lean#L169)
already exists. Its selected logits and target tensors and its reduction definition
must be matched to our chosen loss; its name does not establish the desired mask,
normalization or parameter boundary automatically.

The [trust-boundary account](https://github.com/lean-dojo/TorchLean/blob/de3192df4779877ceb65cfe470a4d4ce9d480a5b/docs/TRUST_BOUNDARIES.md) separates exact proofs,
conditional contracts, native implementations and executable replacements. The
real-valued VJP results do not establish Float rounding accuracy, PyTorch agreement,
or CUDA/PTX kernel correctness. A focused textual scan found no proof-hole or
axiom declarations in `NN/Proofs/Autograd` and `NN/Spec/Autograd`; that is neither a
transitive dependency audit nor a substitute for building and printing theorem
axioms. Native `extern`, opaque declarations and `implemented_by` replacements
also require boundary inspection even when no custom logical axiom appears.

## Initial integration design

Use an isolated package to import the actual pinned upstream graph and runtime
bridge. Construct a small affine-plus-square graph with its weight and bias tensors
as differentiable inputs, select the output and use an arbitrary output seed.
Reuse upstream local derivative certificates or its `autograd` tactic, then prove
the checked graph succeeds on the stated domain and instantiate its VJP theorem.
This exercises automatic reverse composition and parameter derivatives without
pretending a separately recreated expression language is TorchLean integration.

Before calling that experiment complete:

- Resolve Lean/mathlib compatibility and record a reproducible dependency pin.
- Build the concrete graph against upstream; audit the used theorem dependencies
  with `#print axioms` and inspect executable replacements along the claimed path.
- Discharge graph-data equality, derivative certificates and execution-success
  premises; do not assume the desired backward result in a generic interface.
- State the parameter and fixed-data boundary, output seed shape and treatment of
  shared parameters. A parameter hidden in fixed graph data receives no gradient
  merely because another input does.
- Keep subsequent numerical comparison and separately authored PTX forward/backward
  proofs as distinct obligations. Their memory layout, permitted execution,
  numerical error and termination contracts remain to be implemented.

The source supports the intended strategy of automatically composing a certified
backward specification. It does not remove the need to certify new primitives,
connect a concrete model to that graph, or prove the separately supplied PTX code.

## Checked isolated integration result

The [isolated package](../../integration/torchlean/README.md) now builds against
the exact revision and transitive manifest above, using Lean 4.34 while the root
remains on 4.33. It constructs an actual upstream `DGraph` computing a pointwise
affine map followed by squaring, with input, weight and bias tensors all variable
and an arbitrary output seed. This is a diagonal affine example, not a dense
matrix layer.

`checked_success` discharges validation and proves that the real-valued checked
API returns `.ok` for every input and seed. `checked_success_vjp` consequently
establishes the selected-output mathematical VJP without assuming successful
execution. `exact_tape_success_vjp` separately establishes success and VJP
correspondence for the lower-level generated tape. The dependency reports for
these endpoints contain only `propext`, `Classical.choice` and `Quot.sound`.

The focused build completed successfully; CUDA and LibTorch were disabled. The
local dependency/build tree occupied approximately 8.9 GB, and installing Lean
4.34 added a 2.9 GB toolchain, apart from shared mathlib cache downloads.
No project-wide toolchain migration or native numerical execution was performed.
Broader model lowering, combined PTX/TorchLean imports, numerical bounds, and
separately authored PTX forward/backward implementations remain open obligations.

The VJP endpoint differentiates the actual graph forward map. The independent
`forward_polynomial` theorem proves that its selected output has the displayed
coordinate-polynomial value for every tensor shape, input, weight, bias and
coordinate. Thus the intended forward computation is connected by proof to the
graph whose backward pass is certified.
