# One shifted exponential, from registers to a real error bound

This is the first complete instruction sequence for softmax's numerator. It
approximates `exp(x-m)` for one stored score `x` and a supplied upper bound `m`.
It does not compute the row maximum, sum the numerators, or normalize a row.
Both inputs denote the exact real values of finite binary32 words. Comparing
with values before they were stored would require an additional input-error bound.

## The four instructions

With the score in `%r0`, the supplied maximum in `%r1`, and scratch/output `%r2`:

```ptx
mul.rn.f32     %r2, %r1, 0fBF800000; // exactly representable -1
add.rn.f32     %r2, %r0, %r2;        // rounded x - m
mul.rn.f32     %r2, %r2, 0f3FB8AA3B; // approximation to log2(e)
ex2.approx.f32 %r2, %r2;
```

The hexadecimal literals specify binary32 bits, not integer-to-float conversion.
The internal text interface has already classified operands and decoded these
bits; raw text parsing and register declarations remain separate obligations.
`.rn` selects rounding to nearest, with ties to an even final bit. Keeping it
explicit also preserves the intended separate arithmetic steps. No `.ftz`
modifier is used: small subnormal values are retained.

The first multiply negates `m` exactly as a real value. We prove this using
representability of the finite input, rather than assigning a second rounding
error to negation. Thus the addition implements the rounded difference. This
reuses already reviewed instruction leaves and avoids introducing a separate
`sub.rn.f32` model in this slice. It is not a performance claim or a proof about
a compiler replacing instructions.

The parameterized program needs its scratch register to differ from the score
register. It may overwrite the maximum register: the maximum is consumed by
the first instruction, whereas the score must survive until the second.
The standalone program begins at instruction position zero and takes four
fetched steps, ending at position four. It preserves all other word registers,
address registers, predicates and memory, and makes no memory accesses.

## Why intermediate results exist and stay in range

The input conditions are

```text
x <= m
abs(x) <= 2^124
abs(m) <= 2^124
```

These are deliberately sufficient conditions, not a characterization of every
safe input. The exact difference has magnitude at most `2^125`. Rounding is
monotone, fixes representable bounds, and maps zero to real zero. We use these
facts to derive a finite, nonpositive rounded difference `z = round32(x-m)`
with magnitude at most `2^126`. That looser bound feeds the previously proved
base-conversion range theorem. The actual multiplication by `0x3fb8aa3b` also
has a finite, nonpositive result, so it lies inside the supported exponential
input domain. No successful intermediate operation or desired final output is
assumed.

An execution witness constructs all four states and instruction occurrences.
The accuracy theorem separately applies to every execution of those four
instructions, including every result permitted by the approximate exponential.
Existence is finite local execution, not GPU progress, a launch guarantee or a
parallel memory theorem. The target is the existing PTX 9.4 / SM>=20 model.

## What is proved about the answer

Let `eps32(t)` denote the half-ULP rounding allowance at real value `t`; ULP is
the spacing of the floating-point grid. Let `c = 12102203/8388608`, the exact
value of the encoded conversion constant, and set

```text
z = round32(x-m)
h = eps32(x-m)
B = eps32(z*c) + abs(z)*abs(c - 1/log(2)) + h/log(2)
```

Every admitted final word is finite, and its real value `u` satisfies

```text
abs(u - exp(x-m)) <= 5*2^-24 + log(2)*B.
```

The three terms of `B` account for multiplication rounding, the conversion
constant's approximation, and the shift's rounding error. The separate
`5*2^-24` term includes the exponential allowance and its reference rounding.
The inherited conservative exponential relation covers its two named ULP
spacing conventions; it is not proof of a unique interpretation of the source
or of hardware realizability of every permitted output.

There is a stronger result when `x=m`: **the final bits are exactly positive
one**. The rounded difference and base-two argument have real value zero, and
the exponential's special rule admits only encoded `+1`. This includes mixed
signs of zero. A later maximum reduction that proves its result is attained can
use this fact, but summation and denominator bounds still need their own proofs.

## Definitions, proofs and checks

- [Numerical composition](../../integration/torchlean/PtxBinary32/ShiftedExp.lean):
  `shift_real`, `error`, `stages_exist`, and `equal_scores`.
- [Fetched program](../../integration/torchlean/PtxBinary32/ShiftedExpProgram.lean):
  `program`, `run_results`, `correct`, `maximal_score`, and `execution_exists`.
- [Boundary checks](../../integration/torchlean/PtxBinary32/ShiftedExpChecks.lean):
  missing fetch, unsupported target, maximum-register reuse, retained subnormal
  shift, opposite magnitude endpoints, mixed-zero execution and a negative shift.
- [Independent review](../formalization/shifted-exponential-review.md): source
  interpretation and proof review remain distinct from Lean checking.

From the repository root, with the pinned Lean setup installed:

```sh
bash scripts/check.sh
python3 integration/torchlean/check.py
```

The integration command builds the new modules, freshly checks the boundary
proofs, and audits every public declaration. GPU execution and benchmarking remain
deferred. Parallel maximum, summation, normalization and backward programs remain
outside this four-step component.
