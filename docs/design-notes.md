# Design notes

These notes hold tentative choices and questions separately from the Stratic
responsibility descriptions. They are not settled implementation contracts.

## Candidate Gemma precision policy

| Computation or storage | Candidate choice |
| --- | --- |
| Large weight matrices and matrix-multiplication operands | BF16 |
| Matrix-product accumulation | FP32, subject to the chosen instruction's actual contract |
| Normalization, softmax, and cross-entropy arithmetic | FP32 |
| Parameter-gradient accumulation and returned gradients | FP32 |
| KV cache | BF16 |
| Other intermediate activations and backward signals | Explicit choices per operation |

The table leaves casts, reduction order, intermediate truncation, subnormal and
special-value rules, and approximate functions unresolved. An FP32 accumulator
label does not establish one particular IEEE sequential reduction. These choices
need assessment against instruction contracts, resources, and useful error bounds.

## Questions requiring investigation

- Pin the PTX 9.4 source artifact and determine the concrete representation of
  targets, undefined behavior, scheduling assumptions, and execution premises.
- Select the TorchLean revision and inspect the derivative and correspondence
  theorems applicable to the required operations and execution paths.
- Select the Gemma checkpoint/configuration and PyTorch reference; identify the
  exact transformer-block parameter boundary, including parameter sharing.
- Specify the loss variant, targets, masking, normalization, and reduction.
  Cross entropy is the candidate discussed alongside the general VJP interface.
- Determine batch and sequence domains, hardware targets, storage strategies,
  kernel organization, and performance goals.
- Establish domains, norms, and accuracy criteria for useful forward and
  backward error bounds; no global numerical tolerance has been selected.
- Select model-assisted formalization tooling, provider/model, evaluation cases,
  review procedures, and cost budget. DeepSeek V4.1 Flash was suggested as a
  candidate, not selected or evaluated.
- Determine concrete release artifacts, study-guide organization, and coverage
  reporting conventions.

Implementation and proofs remain absent. These notes preserve unresolved design
choices without treating discussion history as a permanent responsibility.
