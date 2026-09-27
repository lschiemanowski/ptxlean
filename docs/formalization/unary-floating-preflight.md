# Unary floating arithmetic: instruction preflight

Status: coordinator foundation and source interpretation notes. This is not a
frozen worker task, an independent review, a dispatched Luna run, or instruction
coverage. No `ex2` or `rcp` implementation has been added to the coverage ledger.

The source is PTX ISA 9.4, with the exact SHA-256 and publisher anchors recorded
in the [stable-softmax guide](../foundations/stable-softmax.md). It was rechecked
locally; no NVIDIA text is bundled here. Lean proof validity and this source
interpretation are separate evidence.

## Decisions and checked support

Use explicit `rcp.rn.f32` for the first softmax reciprocal. Its rounding rule is
specified directly and supports subnormals by default on `sm_20+`. Restrict the
initial instruction form to no `.ftz` and the project's pinned PTX 9.4 target
policy. `Reciprocal.Results` is the exact numerical provider: FloatLib's encoded
nearest-even division of one by the original input, with the established NaN
result envelope. The result-existence theorem covers every input encoding;
finite real equality/error theorems additionally require a finite nonzero input
and a quotient range bound. Nothing treats real division by zero as machine
reciprocal behavior. The arithmetic tests check signed zero and infinity cases,
NaN freedom, gradual underflow and overflow.

Use the center-spacing ULP convention for the current exponential numerical
foundation. `RoundedReal.Results k ideal output` measures distance from an actual
encoded nearest-even center using `k*ulp32(round32 ideal)`. A new input-range
proof constructs that center; it is no longer a caller-supplied object. All
nonpositive real exponents have finite centers for `2^x`. The corresponding
two-ULP numerical bound is `5*2^-24` against the ideal value, including rounding.
A checked example distinguishes this convention from counting neighboring
encodings at the power-of-two boundary one.

The pinned `ex2` wording specifies the correctly rounded reference but does not
resolve all ULP boundary conventions. The numerical relation is not sufficient
by itself for accepting a faithful full PTX `ex2` contract. Review must address
that interpretation and sign, zero, infinity, NaN, underflow and positive-input
overflow cases. Do not hide the remaining cases by claiming that an arbitrary
finite operand always has a finite exponential, or that only nonpositive
operands are the full instruction domain. Do not silently instantiate the
approximate reciprocal with the same reference convention as `ex2`.

## Luna boundary for the reciprocal instruction

The shared scalar state, guard, operands, exact floating bit literals and
supported-target conventions already exist. A worker should reuse those and
`Reciprocal.Results`; it must not rewrite division, change the NaN envelope,
or disguise a unary operation as an integer or binary floating instruction.
The coordinator must freeze the interface and a separate acceptance driver
before dispatch through the existing headless runner.

Required guarantees and distinguishing checks:

- Exact `rcp.rn.f32` mnemonic and unary operand count; reject `.approx`, `.ftz`,
  other rounding modes/types and malformed operands for this bounded form.
- Actual fetch at the current PC, including a nonzero PC and unrelated prefix;
  explicit PTX-version and target conditions; no step on missing fetch.
- Enabled and disabled positive/negative guards. A disabled instruction advances
  without requiring arithmetic, including when its operand is NaN or zero.
- Read the input in the original state, including source/destination aliasing.
  Preserve other registers, predicates, addresses and memory; record a genuine
  unary floating occurrence and the correct read/write metadata.
- Existential leaf and fetched-step results for arbitrary supplied states,
  using the unconditional numerical `results_exists` theorem.
- Connect an enabled destination to `Reciprocal.Results`, then instantiate the
  range and error theorem on that actual input/output. Do not require a premise
  already asserting the destination's correct value.
- Independently check the signed-zero/infinity table, NaN payload freedom,
  `1/3` rounding, subnormal result and overflow. Reject integer division and a
  hard-coded center independent of the input.

Keep the worker's writable module separate from source documents, frozen checks,
Stratic, build configuration and dependency pins. Evaluate via fresh pinned Lean
checking, exact axiom dependencies, source review and replay. Acceptance of a
numerical provider is not acceptance of that future instruction implementation.

## Still needed for softmax

The generalized real-to-word construction supplies mathematical existence, not
an executable exponential. Argument subtraction/base conversion need their own
rounding/range/error proofs. The maximum and sum need actual parallel programs;
the sum's rounding can depend on the chosen tree. Stored input/output meaning,
all permitted executions, memory safety and admitted existence remain kernel
obligations. GPU execution, timings and performance claims remain deferred.
