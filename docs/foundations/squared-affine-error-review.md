# Independent SquareError review

Reviewed `integration/torchlean/PtxBinary32/SquareError.lean`, SHA256
`42edcaf72e7483a4fc3e70511381dcbcf8ba411fda54d6389a475bee53b232eb`.
No numerical code was changed. No semantic/proof blocker found.

`Results` contains exactly four admitted operations: multiplication and addition
for the first affine calculation, followed by multiplication of the same actual
intermediate Word with itself and addition of the positive-zero Word. It neither
substitutes a real result for that word nor fuses the stages.

`affine_value` derives the intermediate's finite real interpretation as
`R = fp32Round (fp32Round (xh*wh) + bh)` from initial finite-word interpretations,
the two original input-only range guards and the actual first `AffineResults`.
It uses `Bounds.round_of_range` for both real operations and the already proved
rounded-add range bound. The result is not an intermediate-value hypothesis.

`results_error` retains the same initial-word and input-deviation conditions.
Its second pair of guards, `|R*R| ≤ maxFinite` and
`|R*R| + eps32(R*R) ≤ maxFinite`, refer only to that explicit expression in the
initial real inputs. They do not assume anything about the actual square or
final output. Both occurrences of the actual intermediate word are linked to R
by the derived theorem, not merely chosen to have a convenient real value.

The first affine error is applied twice as the error budget for the two factors
of the square. `budget_expansion` correctly yields both second-stage rounding
contributions plus `2*|x*w+b|*E + E*E`. It retains the quadratic perturbation term
and the absolute value around the ideal first output. The final positive-zero
addition contributes a conservative rounding allowance, even when a sharper
specialized zero-add bound would remove it; this is sound reuse, not a changed
instruction count. Deviation/error inequalities supply any necessary
nonnegativity through the existing proofs. No finiteness or desired-value premise
on an intermediate or output is introduced.

`results_exists` separately constructs four actual relation members for arbitrary
input bit patterns without the numerical range promises. It preserves the
reviewed conservative NaN envelope and does not claim hardware realizability of
every admitted NaN encoding. This module proves arithmetic composition only;
its statement does not claim persistent memory, launch visibility or completed
kernel executions. Those remain the launch theorem's obligations.

The numerical source meaning is inherited unchanged from the independently
reviewed explicit `.rn.f32` multiplication/addition slice: IEEE-compliant rounding,
sm_20-or-later gradual underflow without FTZ, bit-preserving words and conservative
NaN freedom. No new instruction form, modifier or target rule is added.

Independent commands from `integration/torchlean`:

    lake env lean PtxBinary32/SquareError.lean
    lake env lean /tmp/square-error-independent-audit.lean

Both passed. Fresh elaboration produced only unused-simp warnings at line 54.
The independent audit checked all eight public declarations: roundedAffine,
Results, budget, zero_real, affine_value, budget_expansion, results_error and
results_exists. Every dependency report contains only propext, Classical.choice
and Quot.sound; no new unchecked axiom or proof hole appears. Exact output is
`/tmp/square-error-independent-audit.log`; elaboration output is
`/tmp/square-error-independent-elaboration.log`.
