# Combining incoming error with binary32 rounding

An actual encoded operand may already approximate an ideal value. For example,
a rounded intermediate xh may differ from the real quantity x that the program
is intended to compute. A useful local arithmetic theorem must carry that
incoming discrepancy forward and add the next rounding contribution.

[PtxBinary32Error](../../integration/torchlean/PtxBinary32Error.lean) does this for
addition, multiplication and a two-step affine expression. It uses the existing
binary32 result envelope and finite-input range adapter; it does not add a PTX
instruction frontend or assume a GPU's numerical behavior.

Write `eps(t)` for `TorchLean.Floats.eps32 t`, the absolute local rounding bound
at t. Suppose actual finite inputs xh and yh approximate x and y with
`|xh-x| ≤ ex` and `|yh-y| ≤ ey`. The deviation premises themselves imply
`ex ≥ 0` and `ey ≥ 0`.

The purely real propagation lemmas first establish:

```
|(xh+yh)-(x+y)| ≤ ex+ey
|xh*yh-x*y| ≤ |x|*ey + |y|*ex + ex*ey
```

The second formula follows by expanding the product in the two perturbations
and applying the triangle inequality. It retains the product `ex*ey`; there is
no assumption that second-order error is negligible.

`add_results` and `mul_results` then connect those inequalities to actual words.
Given finite interpretations of the input words, the range guard for the exact
actual sum or product, and any output admitted by `Results`, they prove the
output is finite and its real value z satisfies:

```
addition:       |z-(x+y)| ≤ eps(xh+yh) + ex + ey
multiplication: |z-x*y|   ≤ eps(xh*yh) + |x|*ey + |y|*ex + ex*ey
```

The local rounding term is evaluated at the actual pre-rounding expression,
not the ideal one. The range guard is `|xh+yh| ≤ M` or `|xh*yh| ≤ M`, with M the
largest finite binary32 value. It proves output finiteness before the real
rounding bridge is used. An encoded output's desired accuracy is never a premise.
`add_exists` and `mul_exists` provide admitted finite witnesses with the same
bounds. These statements concern every admitted output, not an experiment with
a selected test value.

## Two rounds for a multiply-then-add expression

The ideal expression is `x*y+b`. Actual input words have finite values xh, yh
and bh, with three stated deviation bounds ex, ey and eb. `AffineResults`
requires two actual relation instances joined by the same intermediate word:

```
input words ── multiply and round ── intermediate word
intermediate word + bias word ── add and round ── output word
```

Let `p = fp32Round(xh*yh)`. The first range guard is `|xh*yh| ≤ M`.
A conservative sufficient guard for the second stage is:

```
|xh*yh| + eps(xh*yh) + |bh| ≤ M
```

`rounded_add_range` derives `|p+bh| ≤ M` from that input-only expression and the
proved local rounding inequality. The caller does not provide a guessed
intermediate value or assume it is accurate. The first encoded operation fixes
its own actual finite value p through the rounded-real bridge.

`affine_results` proves both intermediate and final words finite and bounds the
final real output z by:

```
|z-(x*y+b)| ≤ eps(p+bh) + eps(xh*yh)
             + |x|*ey + |y|*ex + ex*ey + eb
```

There are two rounding contributions because the multiplication is rounded
before the addition reads its encoded result. This is not the formula for an
FMA, which combines the exact product and addend before one rounding.
`affine_exists` constructs both encoded reference stages and proves the same
finiteness and error conclusion. It requires no externally supplied intermediate
or final result premise.

The range conditions are deliberately sufficient. The conservative second guard
can reject a safe case where the later addition cancels; it does not claim that
such a case is invalid PTX. Subnormal inputs and results remain allowed, signed
zeros retain their bits, and all bounds here are absolute. Larger reductions,
matrices, backward programs and networks must preserve their own operation order
and prove their own input deviations and intermediate ranges. No mixed-precision
or Gemma policy is selected by these scalar composition rules.
