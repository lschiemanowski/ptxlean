# Independent review of the generated affine-square VJP

No blocking semantic or proof issue was found in the scalar exact-real contract.
The reviewed source is `integration/torchlean/PtxAffineSquareVJP.lean`, SHA-256
`c0623f364c61bd87ea0e609b886e9c71df4ffb15f0a29236d4c64b7392ffd96f`.
Its graph adapter `PtxTorchLean.lean` has SHA-256
`8e1d4cd79e82a924e7e10d9903b92cacbdd976e71c0e42c22d9fed94607545d8`.
The pinned upstream TorchLean checkout is
`de3192df4779877ceb65cfe470a4d4ce9d480a5b`; its tracked tree was clean during
review. The Stratic `affine-square-vjp` description and its study guide match
the checked theorem scope.

## What the statements actually prove

The graph is the existing three-node `DGraph`: multiply input x by variable
weight w, add variable bias b, then square. All three values are differentiable
inputs. Unit auxiliary data contains no fixed weight or bias. `forward_value`
and `forward_tensor` establish the actual selected output, first as a real
coordinate and then as the entire rank-zero tensor.

`generated_vjp` unfolds this graph's actual `vjpWithSeed`. It does not define
that operation to be `sensitivities` or assume a desired gradient. It reduces
upstream `GraphData.backpropCtx`, its saved forward contexts and tensor-pack
accumulation, then proves equality of all three resulting scalar coordinates.
The displayed polynomial `sensitivities` is the right-hand side of the proved
equality. Private index and splitting lemmas are definitional equalities.
The square uses `TapeNodes.mul idx idx`, so both operand contributions must
reach the same input; their sum is retained. The arbitrary real seed d is
present throughout, not specialized to one.

`checked_result` additionally concerns the real upstream `vjpChecked` call.
That API first uses checked tape construction and then runs the tape's reverse
pass. The existing `checked_success` proof discharges its validation condition
by reduction for these unconditional arithmetic nodes; the result has no
successful-call premise. Upstream `vjpChecked_eq` connects that checked tape
execution to the graph reverse rules. Thus replacing a reverse result manually
would not satisfy this equality. `checked_example` checks input order and a
nonunit seed: (x,w,b,d)=(2,3,1,2) yields (84,56,28) and forward output 49.

`sensitivities_adjoint` uses the composed graph's derivative theorem, not only
a formal occurrence of mathlib's totalized `fderiv`. The graph carries actual
`mulFderiv`, `addFderiv` and `squareFderiv` certificates; the upstream theorem
uses those certificates to establish the forward map's derivative. No
input-domain, differentiability, gradient or success premise is hidden here.

## Upstream meaning inspected

At the pinned revision, the relevant primary sources are:

- `NN/Runtime/Autograd/Torch/Core/TypedGraph.lean`: seeded reverse operation and
  checked tape-based API.
- `NN/Runtime/Autograd/TypedGraph/Core.lean`: checked node validation and tape
  construction.
- `NN/Proofs/Autograd/Tape/Algebra/Soundness.lean`: recursive reverse accumulation.
- `NN/Proofs/Autograd/Tape/Nodes/Arithmetic.lean`: actual add/multiply/square
  nodes and their derivative certificates.
- `NN/Proofs/Autograd/Runtime/Link/Checked.lean` and `GraphComposition.lean`:
  checked-result equality and derivative-adjoint correspondence.

“Generated” here means the upstream reverse traversal and tape construction
compose the upstream proved primitive reverse rules. It does not mean that
this project automatically derives primitive derivative proofs from arbitrary
Lean functions.

## Independent checks and remaining boundaries

From `integration/torchlean`, fresh `lake --no-cache env lean
PtxAffineSquareVJP.lean` completed without warnings or errors. An independently
written import driver printed the axioms of all ten public declarations:
`scalarShape`, `inputs`, `graph`, `sensitivities`, `forward_value`,
`generated_vjp`, `forward_tensor`, `checked_result`, `sensitivities_adjoint`,
and `checked_example`. The existing exact-name dependency auditor accepted all
ten reports; only `propext`, `Classical.choice` and `Quot.sound` occur. The
forbidden-token source scanner also passed. The complete dependency output is
[affine-square-vjp-audit.txt](affine-square-vjp-audit.txt). Source hashes were
checked again after execution. Increased elaboration limits and the local
transparency option do not bypass kernel proof checking.

This establishes a total successful exact-real checked reverse result for this
finite scalar graph. It is not a resource/time bound on an executable real
number implementation. Tensor-wide closed formulas, floating-point backward
accuracy, a separately supplied PTX backward kernel and its execution or
numerical correspondence, Python/PyTorch equivalence and hardware behavior
remain separate obligations. No specification weakening is needed for the
completed scalar claim.
