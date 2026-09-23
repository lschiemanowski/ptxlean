# Independent review of the gradient storage view

No blocking issue was found. Reviewed `integration/torchlean/PtxGradientView.lean`
SHA-256: `921ee67ea0f310628ae93502c96f7724b60f1d3c347945f204130d61f37353a8`.
The `gradient-storage-view` Stratic description, implementation links and study
guide accurately state this observation interface's scope.

## Exact observation and component order

`Words` retains the three exact 32-bit observations as dx, dw, db. `decode`
uses `Ptx.Binary32.finiteReal` on all three words and constructs the actual
TorchLean `TensorPack` through `AffineSquareVJP.inputs`. Its coordinates are
input sensitivity, weight sensitivity and bias sensitivity in that order.
No local replacement tensor type or list-of-reals surrogate is substituted.

`component` reads the three scalar tensors' items. `componentwise_iff` covers
all three coordinates of arbitrary packs, not only those built by `inputs`.
`component_inputs` and `componentwise_inputs_iff` fix the coordinate mapping.
The allowances ex, ew and eb follow exactly the same order. These are absolute
component errors, with no hidden norm or selected global tolerance. A negative
allowance cannot satisfy the corresponding absolute-value inequality; no
additional nonnegativity assumption is needed.

`decode_some_iff` characterizes successful decoding in both directions and
identifies the exact returned pack. `decode_none_iff` characterizes failure.
The underlying finite interpretation tests the encoded format's finiteness
before calling its real interpretation, so an exceptional encoding cannot use
that model's real-value fallback. `nonfinite_rejected` handles every component,
and `not_approximates_of_nonfinite` lifts rejection to the approximation
relation for every reference and every allowance. There is no default tensor.

## Connection to the actual generated backward

`Approximates` includes actual successful decoding and componentwise agreement.
`approximates_iff` exposes its three numerical obligations once the finite
interpretations are supplied. `generated_iff` specializes the reference to the
actual `graph.vjpWithSeed`, using the previously proved `generated_vjp`. The
reference formulas are correctly ordered: dx uses w, dw uses x, db uses neither
additional factor. The real seed d remains arbitrary.

`generated_of_bounds_checked` intentionally consumes independently proved finite
interpretations and numerical bounds. It proves approximation of the actual
generated result and pairs that with the actual checked call's success theorem;
it does not assume backward success or invent a reverse computation. The bounds
are an explicit interface obligation, not something this view claims to derive.
Execution and arithmetic producers must supply them together with evidence that
these words are the stored outputs.

`signed_zero_same_view` proves both inequality of the exact observations and
equality of their decoded real packs. Positive and negative zero therefore
provide a checked counterexample to inferring bitwise equality from equal real
values (or zero real error). The theorem uses the actual encoded zero meanings.

## Independent checks and remaining obligations

Fresh `lake --no-cache env lean PtxGradientView.lean` passed without warnings or
errors from the pinned integration package. An independent namespace-aware
inventory, with the explicit `Triple` abbreviation included, matched all 18
public declarations: two type declarations, four definitions and twelve
theorems. A fresh import driver produced exactly those 18 `#print axioms`
reports, all accepted by the existing exact-name audit with only `propext`,
`Classical.choice` and `Quot.sound`. The forbidden-token scan passed and the
source hash was checked again afterward. The complete reports are in
[gradient-storage-view-audit.txt](gradient-storage-view-audit.txt).

This interface performs no allocation lookup or unchecked/default memory read.
Selecting words from the correct live allocation, execution and memory safety,
proving the numerical bounds, saved-forward provenance and full backward
kernel correctness remain separate obligations. There is no tensor-wide
layout, Python/PyTorch equivalence or runtime/hardware correspondence claim.
No source change was required by this review.
