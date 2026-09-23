# From a word allocation to TorchLean tensors

The first concrete kernel–tensor bridge connects the existing vector-add program
to actual TorchLean tensors. It interprets 32-bit unsigned integers. It does not
introduce floating point or implement the real-valued backward example.

The checked implementation is
[`PtxTensorBridge.lean`](../../integration/torchlean/PtxTensorBridge.lean).
Its responsibility is described in [Stratic](../../stratic/descriptions/tensor-layout.md).

## Read the allocation as a layout

Suppose the allocation initially contains these words:

| Word index | Role | Initial value |
| --- | --- | --- |
| 0 | coordinate 0: left | 7 |
| 1 | coordinate 0: right | 11 |
| 2 | coordinate 0: output | 99 |
| 3 | coordinate 1: left | 4,294,967,295 |
| 4 | coordinate 1: right | 1 |
| 5 | coordinate 1: output | 73 |
| 6 | unrelated tail word | 42 |

For coordinate `i`, the layout selects word indices `3*i`, `3*i+1`, and
`3*i+2`. The left tensor is `[7, 4294967295]`; the right tensor is `[11, 1]`.
The initial output words can contain anything. After completion the output
tensor is `[18, 0]`, and the tail word remains 42. Each word occupies four bytes,
so the program uses byte addresses four times those word indices.

`view` is a small reusable component: give it an allocation, a function selecting
a word index for each coordinate, and a function interpreting each word. It
constructs an actual upstream `TorchLean.Tensor` of shape `[n]`. `unsignedView`
interprets words as natural numbers; `realView` interprets those same integers as
exact real numbers. `view_map` shows that changing the scalar interpretation
preserves the layout.

The standalone view is total: like the underlying execution, its list lookup has
a default if the index is absent. This is not permission to verify missing
memory. `layout_bounds` proves all selected initial cells exist from
`3*n ≤ memory.length`; `completed_bounds` proves the same for every finite
execution state. `view_bounded_apply` explicitly equates a bounded view lookup
with lookup of the actual cell, excluding default behavior.

The existing module is named `SharedVector`, because threads access one common
allocation. That allocation models **global memory**. This example does not use
PTX's separate shared-memory address space or a barrier.

## Follow one thread

Thread `i` executes five actual scalar instructions:

1. Load the left word into register 0.
2. Load the right word into register 1.
3. Add them with 32-bit wrapping arithmetic into register 2.
4. Store register 2 in the output word.
5. Exit.

The initial register files are supplied by the caller and may contain arbitrary
values. Loads overwrite the registers that addition uses. Distinct threads have
distinct output cells, and no output cell is an input cell, so their interleavings
do not change the input values.

A schedule is a finite list naming the thread chosen at each step.
`completed_unsigned` and `completed_unsigned_tensor` cover every such schedule
whose threads have all completed. These mathematical schedule identities require
the allocation bound. Their interpretation as actual nonfaulting scalar
instructions also requires `12*n < 2^64`, which excludes wrapping of the byte
addresses. The stronger `execution_exists` theorem supplies that instruction
correspondence and a completed schedule of exactly `5*n` steps. It does not assume
that an execution succeeds or that its output is correct.

## Separate modular arithmetic from real addition

For every coordinate, the primary theorem states

```text
output_i = (left_i + right_i) % 2^32
```

The addition on the right is addition of natural numbers. `%` takes the remainder
after division by `2^32`. Equivalently, the whole output tensor is TorchLean's
natural-number tensor addition followed by its pointwise `Tensor.map` operation
applying this remainder.

The second coordinate of the example overflows. The direct checked theorem
`wraparound_execution` evaluates the actual five scheduled steps for
`4294967295 + 1` and obtains zero. `wraparound_not_fitting` proves these inputs
fail the condition for the real-valued interpretation.

`NoOverflow n memory` requires every input sum to be less than `2^32`.
Under that input-only condition, `completed_real_add` proves a whole-tensor
equality with actual upstream real-tensor addition. `real_execution_exists`
also supplies a finite instruction execution for that equality. This is an exact
integer-to-real embedding. It says nothing about rounding, floating-point
accumulation, hardware execution, or agreement with PyTorch.

## Keep the memory obligations visible

`execution_exists` retains several logically separate conclusions:

- A finite instruction-faithful execution and completion of all threads.
- The modular tensor result.
- Preservation of every word outside the selected output cells, including input
  cells and unused tail storage.
- Access safety for every emitted memory effect.
- A fully valid relational memory graph, with each thread's three memory labels
  matching those of the same execution.

The relational result uses the existing six-event-per-thread family: three
initialization events and the thread's two reads and one write. Candidate read
values, read sources and coherence ordering remain parameters. Source
compatibility requires each read to take the value of a write at its location.
Only initialization writes the input locations, so this requirement forces the
original input values. `candidate_unsigned_tensor` then fixes the output tensor;
`candidate_execution_agree` identifies it with every completed schedule's output.
These theorems do not assume the desired output or require selecting the
constructed graph's particular source/coherence relations.

This is a restricted candidate family whose store labels implement the supplied
addition program, not a universal theorem about arbitrary PTX programs.
Execution-backed label correspondence already exists in
[`SharedVectorMemory.lean`](../../Ptx/SharedVectorMemory.lean). General dependent
concurrency, other layouts, mixed precision, kernel orchestration and device
conformance remain separate work.

## Check the result

From `integration/torchlean`, using the committed manifests and toolchain:

```sh
lake build PtxTorchLean PtxTensorBridge
lake env lean PtxTensorBridge.lean
```

The second command prints the logical dependencies of all 15 bridge theorems.
The new receipt `verification-tensor-bridge.json` records exact input hashes,
commands and dependency audit. Earlier integration receipts remain historical
snapshots. No dependency update, CUDA runtime, or LibTorch runtime is needed for
this proof target.
