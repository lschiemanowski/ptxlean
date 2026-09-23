# Reading three stored gradients

This interface connects selected binary32 codewords to three real scalar
TorchLean tensors. Its description preceded the implementation in
[`PtxGradientView.lean`](../../integration/torchlean/PtxGradientView.lean).

The word order is dx, dw, db: sensitivity to the input, weight and bias. The
caller has to obtain these actual words from its proven memory layout. The view
has no allocation, pointer or default read, so it cannot substitute for an
execution or memory-safety proof.

`decode` returns no real pack if any selected encoding is nonfinite. If all
three decode as rx, rw, rb, it returns the existing TorchLean scalar pack
`AffineSquareVJP.inputs rx rw rb`. The componentwise error contract compares this
pack with a reference pack, using a separate absolute-error allowance for each
coordinate.

For the actual generated backward of `(x*w+b)^2`, the reference coordinates are
`2*d*(x*w+b)*w`, `2*d*(x*w+b)*x`, and `2*d*(x*w+b)`. The output seed d is an
arbitrary real multiplier for the output's sensitivity. `generated_of_bounds_checked` accepts three proved numerical bounds and yields
approximation of the actual
`graph.vjpWithSeed` result, together with actual `vjpChecked` success. It does
not reimplement reverse differentiation.

Both signed zero encodings represent real zero. Therefore zero real error does
not imply bitwise equality. NaNs and infinities are rejected rather than
silently mapped to zero. The words remain available in the observation, so a
separate bitwise assertion can compare their exact values when needed.

`componentwise_iff` expands the all-coordinates condition to three numerical
inequalities for any actual three-scalar reference pack. `approximates_iff`
then uses the finite interpretations of the selected words. `generated_iff`
specializes that reference to the actual generated backward computation by
using the already proved `AffineSquareVJP.generated_vjp`; it introduces no
independent reverse algorithm or assumed derivative.

`decode_some_iff` characterizes every successful view: all three `finiteReal`
interpretations exist, and the returned tensor pack contains precisely those
values. `decode_none_iff` and `nonfinite_rejected` explain failure. The theorem
`not_approximates_of_nonfinite` makes rejection apply to approximation claims as
well, for any reference and any numerical allowances.

`signed_zero_same_view` checks two distinct exact observations: words
`[0x00000000,0x00000000,0x00000000]` and
`[0x80000000,0x00000000,0x00000000]`. Both decode to the same real zero pack.
Their inequality as codewords and equality as real observations are both
proved. This prevents interpreting an error bound of zero as bitwise identity.

Bounds are stated as absolute errors, so useful finite bounds must be
nonnegative; negative allowances simply cannot satisfy a component inequality.
There is no unmentioned norm, tolerance, fallback value or positivity premise.
The numerical producer proves the three inequalities, and the execution/layout
producer proves that the supplied exact words are the stored gradients.
