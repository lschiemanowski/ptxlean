# Rounded binary32 reciprocal review

The selected form is `rcp.rn.f32` without `.ftz`, interpreted at PTX ISA9.4
and numeric target level `sm_20` or higher. The numerical provider and frozen
contract passed an independent source review. A separate independent candidate
review found no discrepancy with that contract. Mechanical replay is recorded
separately in the acceptance evidence; these reviews do not substitute for it.

The source is the locally pinned NVIDIA PTX9.4 document with SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Relevant publisher sections are
[reciprocal](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-rcp),
[general floating-point rules](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions),
[predication](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#predicated-execution),
[instruction statements](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#instruction-statements),
[operand types](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#operand-type-information),
and [exact floating constants](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-constants).
These links identify source sections; the hash identifies the reviewed revision.
No publisher text is distributed here.

## Source interpretation

The rounded form divides one by the source, with nearest-even rounding. The
provider uses FloatLib's encoded division of exactly represented positive one
by the input, so there is no separately rounded intermediate numerator. The
pinned implementation refines its division specification using exact scaled
rational arithmetic and nearest-even rounding. General rounding modifiers for
single precision require PTX2.0 and `sm_20+`; the project intentionally accepts
only its pinned ISA9.4 version.

The form without FTZ supports gradual underflow. Signed zero reciprocates to
same-sign infinity, infinity to same-sign zero, and NaN remains NaN. The reciprocal
section's displayed special-case table is located under its approximate-form
discussion. For this rounded form, the justification also uses its explicit
IEEE754-compliant semantics and the general floating rules; the approximate table
alone is not used as the full contract. The conservative existing NaN envelope
admits alternative NaN bits without claiming that every such encoding occurs on
hardware. No approximate reciprocal error convention is borrowed for `.rn`.

## Candidate and proof boundary

The candidate is a new unary leaf over the existing scalar state. The enabled
constructor retains **every** `Reciprocal.Results` output, evaluates the operand
in the incoming state, advances the PC and updates just the destination. Source
and destination may coincide. A disabled predicate advances only the PC and
requires no arithmetic premise, even for zero or NaN. Read/write records reflect
that choice; memory, address registers and predicate registers are preserved.

A fetched step requires the selected target and an actual instruction at the
current PC. Its occurrence retains that instruction and PC. One-step existence
uses the provider's unconditional witness; finiteness, nonzero inputs, range
bounds and a desired post-state are not assumptions of execution. The finite
accuracy handoff is a separate consequence when the numerical premises hold.

The typed decoder accepts only the exact mnemonic and unary operand shape.
It distinguishes malformed supported forms from unsupported spellings. It does
not parse raw PTX modules, check register declarations or initialization, convert
integer literals to floats, or validate physical target names. Word operands
stand for compatible `.b32`/`.f32` register bits or predecoded exact `0f`/`0F`
literals. The numerical target check is a feature floor, not target-name validation.

The independent driver checks exact spelling, target/fetch rejection, both guard
polarities, exceptional encodings, gradual underflow, aliasing, arbitrary-state
frames and the actual destination's numerical meaning. Direct execution with an
arbitrary admitted output prevents replacing the relation with one selected NaN
payload. The proof review found no hidden desired-result assumption. Kernel
execution, shared-memory safety, GPU conformance and softmax correctness are not
conclusions of this instruction trial.

## Acceptance-driver correction

Frozen driver v1 timed out at two applications of `eval_destination`: leaving the
instruction argument implicit triggered excessive definitional equality work.
Driver v2 supplies that same aliased instruction explicitly in the two calls.
Every proposition and the candidate source are unchanged. The first failed replay
is retained beside the subsequent replays; the corrected driver is also checked by the
normal integration suite. This is coordinator checker repair, not a worker repair
or first-pass acceptance claim.

The complete reference-fixture preflight required before dispatch was omitted.
This is a process deviation, not evidence of following that part of the workflow.
Post-generation mutation checks separately accept the original and reject three
compiling, axiom-audited mutants: ignored input, approximate spelling and weakened
target threshold. They improve confidence in the corrected driver but cannot be
reported as pre-dispatch calibration or retroactively remove the omission.
