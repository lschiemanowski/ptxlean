# Independent groups for the dense layer

This extends the [complete single-group layer](parallel-dense-layer.md). A
cooperating thread array (CTA) is a group of threads with shared scratch memory
and a barrier that lets them wait for one another. A grid launches several such
groups. They share global memory; completing one group's barrier does not wait
for or release another group.

The grid forward theorem is proved, but **the complete grid milestone is not**.
The theorem covers every completed admitted execution. A proof constructing
such an execution for the reduction is still missing, and the multi-group
backward has not been composed. The old single-group forward/backward existence
and numerical results remain intact.

## Follow one step

`Grid.State` contains one global array and a private state for each group.
`Grid.Step.issue` chooses a group and thread, gives the existing instruction
machine a view of that group's private state and the current global array, then
writes the result back. Another group's registers, scratch and barrier are
unchanged; its next instruction sees the updated global array.

This is actual instruction interleaving. It does not treat a complete row group
as one atomic operation. `Grid.Reference.run` is a software interpreter for
specific schedules. Its soundness proof connects these examples to candidate
execution, not automatically to memory admission.

## Follow a row

For a matrix with `m` rows and `n` columns, group `g` computes row `g` using
`width = 2^depth` lanes, where `n ≤ width ≤ 1024`. The entry state places
`g*width+t` in lane `t`'s work-item register. The instruction list itself decodes
the row and column and computes its load/store addresses. This entry-state
interface is not a CUDA launch or argument-passing implementation.

Each active lane multiplies `W[g,t]` by `x[t]`; padded columns contribute zero.
Lanes publish products, synchronize, and repeatedly combine adjacent pairs in
the same balanced order used by the single-group proof. The row leader adds the
bias, applies ReLU (or the explicit affine-only variant), and stores its output.
Groups can finish at different times.

For now, each private scratch allocation retains the original plane and row
offsets: `(depth+1)*m*width` words **per group**, including unused row positions.
This preserves the instruction list but is a substantial storage cost. The
model proves address bounds within those explicit arrays. It does not establish
that the allocation fits any GPU's shared-memory capacity. Compact per-group
addressing is a separate representation improvement.

## Why arbitrary read candidates cannot spoil the forward result

The instruction machine allows candidate load values. A separate graph checks
which actual write may supply each load. One initial global cell is shared by
all groups; scratch cell identities include their owning group.

The proof derives the following facts from the combined instruction trace:

1. Global stores target only distinct row outputs. Input, weight and bias loads
   therefore obtain their words from initialization.
2. Each scratch cell has one program writer. The fresh plane number identifies
   its reduction stage and the word offset identifies its lane.
3. Completing a row's execution entails its actual producer stores and barrier
   completions. Each barrier has actual earlier arrivals from that group.
4. The memory constraints force a later scratch load to observe its producer's
   value. Neither the producer's value nor a desired execution schedule is an
   assumption of this result.
5. An induction over the actual trace carries those values through the permitted
   floating-point instruction results. The final global stores therefore
   represent the prescribed reduction and activation.

`GridDense.completed_forward` proves stored outputs, unchanged original
operands, allocation lengths and aligned in-bounds accesses.
`PtxTorchLean.GridDenseForward.universal_forward` applies the existing initial
encodings and calculated range conditions to give error bounds against the
actual TorchLean real tensor graph. The arithmetic order and numerical policy
are unchanged; this is not a bitwise PyTorch or NVIDIA hardware claim.

## Pointwise stages and partial groups

Copy, multiplication and sensitivity gating use only global memory and no
barriers. `Grid.flatten_run` and `Grid.reflect_run` prove execution equivalence
with unique flat thread identities, allowing the existing pointwise memory
proofs to be reused. The flat numbering introduces no giant physical CTA.

`GridPointwise.launch_exists` and `launch_correct` separately establish admitted
existence and universal stored-output correctness. `padded_exists` and
`padded_correct` cover a logical vector whose length is not a multiple of group
width. Extra lanes read source word zero and write allocated padding outputs.
For example, three logical outputs with width two use two groups and four output
cells. The fourth cell is padding and may change; the first three are the
logical result. Zero groups take the explicit no-launch case.

## Check it and identify what remains

From the repository root, run:

```sh
bash scripts/check.sh
bash integration/torchlean/check.sh
```

The integration check builds the pinned project, reruns grid interpreter
examples and inspects the exact theorem dependencies. The examples cover
interleaved groups, a group finishing before another starts, different scratch
values at the same numeric address in different groups, padded columns and
outputs, empty dimensions, negative affine outputs, and more than 1,024 total
threads. No GPU execution or benchmarking is performed.

The exact remaining obligation is to construct a finite completed reduction
grid execution and read-source/coherence choices satisfying `GridDense.Admitted`
for arbitrary stored operands under the stated bounds. An interpreter run or
its candidate-execution soundness theorem does not prove that obligation.
After that, the five backward stages need actual grid launches, stored handoffs,
TorchLean VJP bounds, and their composed existence theorem. None of these missing
conclusions has been inserted into the forward theorem's assumptions.
