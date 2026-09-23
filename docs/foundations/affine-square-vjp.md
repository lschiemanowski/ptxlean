# Understanding the generated affine-square backward

The scalar contract is implemented in
[`PtxAffineSquareVJP.lean`](../../integration/torchlean/PtxAffineSquareVJP.lean).
The description preceded implementation; the completed proofs compute the actual
upstream reverse operation.

The actual TorchLean graph first computes p=x*w, then a=p+b, then y=a*a.
Both occurrences of a in the last multiplication contribute to its sensitivity.
Starting with an arbitrary output weight d, reverse propagation therefore sends
`d*a + d*a = 2*d*a` to a. Addition sends this same value to p and b.
Multiplication sends it times w to x and times x to w.

`checked_result` proves that the actual checked backward call returns:

| Input | Returned sensitivity |
|---|---|
| x | `2*d*(x*w+b)*w` |
| w | `2*d*(x*w+b)*x` |
| b | `2*d*(x*w+b)` |

The seed d is the weight attached to the output. For d=1 these are the usual
three scalar partial derivatives. An arbitrary seed tests the reusable
vector-Jacobian interface rather than a special unit-seed case. The result is
ordered exactly like the graph input pack: x, w, b.

`generated_vjp` reduces the actual `vjpWithSeed` returned by the
existing `PtxTorchLean.affineSquare` graph. A standalone derivative of a polynomial
would not by itself establish that its generated backward returns these values.
The existing checked-success theorem removes any success premise, and the
existing derivative-adjoint theorem gives the generated result its mathematical
meaning. `checked_result` uses the success theorem, while `sensitivities_adjoint`
identifies the displayed formulas with the derivative-adjoint. No successful
call or desired derivative appears as a premise.

This example uses tensors with rank zero, meaning one real value with no array
dimensions. It is exact real arithmetic. No floating-point rounding or PTX
backward implementation is supplied by these formulas. A separately authored
PTX backward would need its own execution, safety, termination and numerical
correspondence proofs.

For example, x=2, w=3 and b=1 give the forward value 49. With seed d=2,
`checked_example` proves that the actual checked call returns sensitivities
84, 56 and 28 in that order, together with 49. A nonunit seed makes the
output weighting visible.

The proof first expands the actual three-node reverse computation and its
saved tensor contexts. Small private projection and context-splitting lemmas
are definitional equalities. It then compares the three scalar coordinates and
normalizes real polynomial expressions. A local elaborator transparency option
permits comparison of dependent shape indices; it introduces no axiom and does
not bypass Lean's kernel. `forward_value` and `forward_tensor` expose both the
scalar value and complete rank-zero tensor returned by the actual forward graph.

The implementation has ten public declarations, including six public theorems.
A fresh dependency audit reports only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms. No `sorry`, new axiom or native
computation oracle is used. The proofs establish the pinned TorchLean graph's
exact-real result; they do not by themselves establish a Python/PyTorch runtime
or GPU correspondence.
