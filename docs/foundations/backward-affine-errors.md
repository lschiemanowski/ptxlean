# Propagating errors through the chosen backward

The exact scalar network is F(x,w,b)=(x*w+b)^2. Its weighted derivatives for
incoming weight d are (2*d*A*w, 2*d*A*x, 2*d*A), with A=x*w+b. TorchLean's actual
generated reverse computation is already proved to return these quantities.
This guide explains the arithmetic contract of a separately selected numerical
implementation, not a new differentiation rule.

The chosen order is four affine stages, each containing a rounded multiply and
an explicit rounded positive-zero add:

| Stage | Encoded inputs | Stored result | Ideal target |
|---|---|---|---|
| q | +2, seed, +0 | q | 2*d |
| db | actual q, saved A, +0 | db | 2*d*A |
| dx | actual db, weight, +0 | dx | 2*d*A*w |
| dw | actual db, input, +0 | dw | 2*d*A*x |

The exact same q word feeds db, and the exact same db word feeds both dx and dw.
The constant `0x40000000` is proved to decode to finite +2 through the pinned
library's normal-field interpretation; the existing positive-zero proof supplies
+0. Their mathematical meanings are not assumptions.

For a stage, `roundedProduct(lh,rh)` means round(round(lh*rh)+0). `StageRange`
requires both `|lh*rh| ≤ maxFinite` and `|lh*rh|+eps32(lh*rh) ≤ maxFinite`.
The generic affine theorem then proves product/output finiteness. `stage_error`
returns the output's actual finite interpretation and its error about l*r, using
the two incoming error bounds and both rounding contributions.

For all four stages, `Guards` substitutes explicit expressions in the initial
finite values. Q=roundedProduct(2,dh); G=roundedProduct(Q,ah). It checks the four
products (2,dh), (Q,ah), (G,wh) and (G,xh). These are input expressions; it does
not request a claim that an actual returned q, db, dx or dw is already finite.
`results_error` establishes that interpretation from the actual result relations.

`qBudget` includes seed error, with zero representation error for constant two.
`baseBudget` propagates the q error and saved-value error into db.
`parameterBudget` propagates db error and the relevant original input error into
dx or dw. Each is an application of the existing affine formula, which retains
the product of the two operand errors and both local roundings. This deliberately
simple bound can be conservative, including for addition of zero. It is not a
claim that the budget is small enough for an arbitrary network.

This arithmetic layer accepts a bound on how far the saved value differs from
ideal A. It cannot establish where that value came from. The recomputing backward
example discharges that promise with an actual preceding affine-kernel execution,
using only initial x/w/b input conditions. Numerical correctness of a saved value
and its actual memory/execution provenance are both necessary at that boundary.

`results_exists` separately constructs all eight arithmetic results for every
input bit pattern. NaNs retain the reviewed conservative envelope. This theorem
asserts semantic nonemptiness, not that every NaN payload can occur on a GPU,
and not by itself that any kernel or runtime execution exists.

The source is `integration/torchlean/PtxBinary32/BackwardError.lean`.
`./integration/torchlean/check.sh` builds it and audits its public dependencies.
The independent review and audit record are in `backward-affine-errors-review.md`
and `backward-affine-errors-audit.txt` alongside this guide.
