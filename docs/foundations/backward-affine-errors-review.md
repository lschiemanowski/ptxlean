# Independent review of the four-stage backward error contract

No blocking proof or numerical-contract issue was found. Reviewed source:
`integration/torchlean/PtxBinary32/BackwardError.lean`, SHA-256
`f455c4088698b29df46a173c456834bdb48496d9707c924db868489c73030531`.
The directly inspected arithmetic dependencies were `SquareError.lean`
(`42edcaf72e7483a4fc3e70511381dcbcf8ba411fda54d6389a475bee53b232eb`)
and `PtxBinary32Error.lean`
(`fd2ddedbd7837787fc263694b33de40ee151663c716e9fe18e72369631100ac7`).

## Encoded arithmetic and proof meaning

`two_real` interprets the actual word `0x40000000`: positive sign, normal
exponent field 128 and zero fraction give exact real +2. It uses the encoded
format theorem, not a host floating-point conversion. The zero addend is the
actual positive-zero word, whose finite interpretation is proved by
`SquareError.zero_real`.

`Results` contains four `Error.AffineResults` pairs. In order these compute
q=2*seed+0, db=q*saved+0, dx=db*w+0 and dw=db*x+0. There are eight permitted
encoded operation results, with explicit product words before each zero
addition. The later relations consume the actual earlier q and db words;
they do not substitute ideal intermediate values. The two final branches use
the same db. No fused multiply-add or reassociation appears.

Write R(lh,rh)=round(round(lh*rh)+0), Q=R(2,dh) and G=R(Q,ah).
The `Guards` conditions are `StageRange` for (2,dh), (Q,ah), (G,wh), (G,xh).
Every expression is calculated from the four initial finite interpretations;
none mentions actual intermediate/output words. Each stage requires both
`|lh*rh| ≤ maxFinite` and `|lh*rh| + eps32(lh*rh) ≤ maxFinite`.
The latter conservatively bounds the actual rounded product before the zero
addition. These sufficient conditions may reject some safe inputs; they are
not claimed necessary. The encoded-result finiteness bridge makes the unbounded
rounded-real function applicable to the actual finite-format results.

`stage_error` derives the stage's output real value and error from both actual
operation results. Its budget retains both local rounding allowances and
`|l|*er + |r|*el + el*er` for incoming error. Valid absolute-error premises
already imply nonnegative error allowances, so no missing independent sign
hypotheses are needed. The q error feeds the db error, and db's error feeds
both final branches. Each explicit zero addition retains a rounding allowance;
the bound does not silently identify a real zero with every signed-zero bit
behavior.

`results_error` universally proves q, db, dx and dw finite interpretations and
the three absolute errors for all permitted encoded results. It does not assume
finite or correct outputs. The saved word's finite interpretation and its error
relative to `idealA` are explicit premises. `idealA` is a free real parameter:
a consumer must instantiate it as the desired forward activation (for example,
`idealX*idealW+idealB`) and prove that saved-value premise. This module does not
prove forward provenance or TorchLean derivative correspondence by itself.

`results_exists` independently constructs all eight operation results for
arbitrary input bits, without finite-range/error assumptions. This is
nonemptiness of the modeled conservative result envelopes, not a claim that
every NaN payload in an envelope is realized by hardware or that a PTX program
executes. Combining this existence with satisfied numerical premises gives
nonvacuous finite accuracy, without changing the arithmetic relation.

## Independent verification and remaining work

Fresh `lake --no-cache env lean PtxBinary32/BackwardError.lean`, run from the
integration package, passed without warnings or errors. An independent
namespace-aware inventory found all 13 public declarations: nine definitions
(`roundedProduct`, `roundedBase`, `StageRange`, `Guards`, `stageBudget`,
`qBudget`, `baseBudget`, `parameterBudget`, `Results`) and four theorems
(`two_real`, `stage_error`, `results_error`, `results_exists`). A fresh import
and `#print axioms` driver produced exactly those 13 dependency reports.
The existing exact-name audit accepted only `propext`, `Classical.choice` and
`Quot.sound`; the forbidden-token source scan passed. The source hash was
checked again afterward. Complete reports are in
[backward-affine-errors-audit.txt](backward-affine-errors-audit.txt).

The `backward-affine-errors` description accurately states the numerical scope.
Its implementation metadata still said unimplemented at review time; the
coordinator was asked to finalize that status and its links after acceptance.
The actual four-launch execution, saved-forward provenance, observation of the
three stored sensitivities, their connection to TorchLean's generated VJP,
and runtime/hardware correspondence remain separate obligations. No source
change or weakened numerical specification was required by this review.
