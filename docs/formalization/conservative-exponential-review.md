# Conservative exponential numerical foundation: review

This slice implements numerical contracts for the next exponential instruction
handoff. It does not add an accepted PTX form, dispatch a worker, or claim a
softmax kernel. The pinned PTX 9.4 source and its unresolved ULP evaluation point
remain documented in [the preflight](unary-floating-preflight.md).

## Independent semantic review

A separate semantic reviewer examined the proposed maximum of center and output
ULP allowances against the pinned-source review. It found this appropriate as a
conservative relation over **those two named interpretations**, not a unique
reading of NVIDIA's wording. It specifically required an all-result output-range
proof and warned against extending the unit bound to arbitrary ULP counts.

The implementation proves exact equality with the union of the two policies.
It derives the output magnitude before using a local spacing bound, specializes
the uniform theorem to two ULPs, and checks a large-count counterexample. It
retains negative tiny outputs and both zero signs in the finite numerical
relation. Exact zero-input results, exceptional inputs and positive overflow
remain separate instruction obligations. No neighboring-encoding interpretation,
FTZ support or hardware realizability is claimed.

## Independent proof review

A separate proof reviewer read `ConservativeULP`, `ConservativeULPChecks` and
`ExpArgument`. It found no substantive issues with inclusion, existence, the
count-two all-result bound, or the composition of base conversion and
approximation error. In particular:

- Finiteness and nonpositive sign of the multiplication result follow from
  input conditions. There is no circular assumption about its output.
- The constant word is exactly `0x3fb8aa3b`, decoded as `12102203/8388608`.
- The exponential relation consumes the actual encoded multiplication output.
  Equality of its real witnesses is established through `finiteReal`.
- Constant error, multiplication rounding and inherited shift error remain
  distinct. The constant error is an explicit real expression, not an unchecked
  decimal estimate.
- Arithmetic-stage witnesses are constructed. A shifted-input proof and kernel
  execution are not implied by these witnesses.

The coordinator added direct encoded multiplication checks, a sufficient input
range theorem, and a concrete all-output error instance for an input of minus
one. These supplement the general theorems; no chosen exponential result is
substituted for the permitted-output relation.

## Reproducible checks and remaining handoff

The four modules are default integration targets. Every public definition and
theorem is included in `PtxIntegrationAudit.lean` and its exact namespace count
in `check.py`. Run the standard root and integration check scripts as described
in [the study guide](../foundations/stable-softmax.md). The allowed proof axioms
remain `propext`, `Classical.choice` and `Quot.sound`.

The next instruction contract must preserve these numerical choices, enforce its
exact special cases, and explicitly bound any unsupported domain. Before Luna
receives that task, its complete independent acceptance driver must pass against
a separate reference fixture and reject calibrated semantic mutants. This slice
has not performed or claimed that instruction preflight. The current numerical
proofs are inputs to it, not substitutes for it.
