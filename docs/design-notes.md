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

- Extend the [pinned-source scalar foundation](foundations/guide.md) with a
  representation of targets, undefined behavior, scheduling assumptions, and
  execution premises for broader PTX coverage.
- Extend the [pinned TorchLean integration](../integration/torchlean/README.md)
  to the required operations and connect its exact graph proofs to numerical and
  PTX contracts. The selected upstream revision and first backward-success
  results are recorded in its package and source audit.
- Select the Gemma checkpoint/configuration and PyTorch reference; identify the
  exact transformer-block parameter boundary, including parameter sharing.
- Specify the loss variant, targets, masking, normalization, and reduction.
  Cross entropy is the candidate discussed alongside the general VJP interface.
- Determine batch and sequence domains, hardware targets, storage strategies,
  kernel organization, and performance goals.
- Establish domains, norms, and accuracy criteria for useful forward and
  backward error bounds; no global numerical tolerance has been selected.
- Broaden the recorded Codex headless GPT-6 Luna capability study across
  instruction families once their foundations are ready. Keep adaptive pilot
  evidence separate from a later frozen productivity evaluation; observe the
  campaign check-in before call 201.
- Determine concrete release artifacts, study-guide organization, and coverage
  reporting conventions.

The [scalar message-passing fragment](foundations/guide.md) has checked
implementation and proofs. The remaining design questions above are not settled by those proofs. These notes preserve unresolved design choices without treating
discussion history as a permanent responsibility.
