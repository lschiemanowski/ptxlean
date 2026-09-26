# Independent groups for the dense layer

This extends the [complete single-group layer](parallel-dense-layer.md). A
cooperating thread array (CTA) is a group of threads with shared scratch memory
and a barrier that lets them wait for one another. A grid launches several such
groups. They share global memory; completing one group's barrier does not wait
for or release another group.

The bounded grid forward and backward are proved: each has correctness for every
completed admitted execution and a separate construction of such executions.
The backward returns input, weight and bias gradients corresponding, within
explicit error bounds, to TorchLean's generated vector–Jacobian product.
Numerical agreement requires the same finite ranges and ReLU sign margin as
the single-group version. Execution existence itself needs no numerical guards.

## Follow one step

`Grid.State` contains one global array and a private state for each group.
`Grid.Step.issue` chooses a group and thread, gives the existing instruction
machine a view of that group's private state and the current global array, then
writes the result back. Another group's registers, scratch and barrier are
unchanged; its next instruction sees the updated global array.

This is actual instruction interleaving. It does not treat a complete row group
as one atomic operation. `Grid.Reference.run` is a software interpreter for
specific schedules. Its soundness proof connects these examples to candidate
execution. `Reference.run_concrete` additionally retains current-array read
evidence. `Grid.Memory.Chronology.concrete_admitted` builds admission from that
evidence, but completion of a particular schedule still needs its own proof.

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

## Why an execution exists

`GridDense.completed_admitted_exists` works for arbitrary input bit patterns and
register seeds under the storage and arithmetic bounds. It does not assume
products, sums, read sources, or the desired output.

The construction runs one group at a time against the actual current global
array. Within a group it sweeps the lanes through the product segment, executes
all barrier arrivals and release, repeats each reduction segment and barrier,
then executes output instructions and exits. `Dense.Local` separates physical
lane identity from logical matrix indexing. Address-control facts are derived
from each fetched prefix. They establish that these finite segments can execute
without invalid addresses. The existing generic grid step embeds every local
instruction; idle groups retain their private state.

`Grid.Replay` checks global and private scratch arrays across the entire emitted
trace. Each load gets either its initial word or the last earlier store to that
same storage location. `Grid.Memory.Chronology.concrete_certificate` assigns
those sources and orders writes chronologically, then proves the existing
memory constraints and actual barrier edges. The resulting graph also excludes
cycles through ordering and read-source edges. This is a sufficient witness;
universal correctness continues to cover all admitted completed interleavings.

`GridDense.Launch` exports the actual completed run and admission at an array
interface. `launch_exists` constructs one; `launch_correct` describes every
one. `PtxTorchLean.GridDenseForward.forward_exists` combines existence with the
unchanged TorchLean numerical encoding. No fairness claim follows.

## Follow the backward's stored values

For incoming sensitivity `d`, the five launches are:

1. Recompute `y = ReLU(Wx+b)`, one row per group.
2. Gate: `g_i = d_i` for positive stored activation, otherwise zero.
3. Multiply: `dW_ij = g_i*x_j`, independently for each matrix entry.
4. Copy the original weights and actual stored `g` into the transposed packet.
5. Reduce: `dx_j = sum_i W_ij*g_i`, with ReLU disabled. The stored `g` is `db`.

The copy includes explicit zero bias/output slots for the affine-only reduction.
Its final addition of positive zero remains in the numerical policy. These are
independently supplied instruction programs; TorchLean automatically constructs
only the specification's backward graph.

`GridDenseBackward.Execution` records each actual launch and its stored handoff.
Pointwise stages use 32-lane groups. `GridPointwise.LogicalLaunch` appends fewer
than 32 padding cells, runs the physical launch, and returns its original-length
prefix. For 33 gate outputs there are two groups, 64 physical outputs and 31
padding cells. All 33 gates and all source words remain in the returned prefix.
The physical padding writes are included in the run, not hidden by a frame claim.
Allocation and prefix selection are explicit host-model operations, not a CUDA
allocator or pointer ABI. Bounds conservatively reserve 32 representable words.

`GridDenseBackward.execution_exists` proves all stages can finish, including
zero rows, zero columns and both empty. `GridDenseBackward.gradients_stored` and
the storage lemmas derive actual gradient words and preserve original operands.
`PtxTorchLean.GridDenseBackward.universal_backward` proves numerical bounds
against the three tensors of the actual TorchLean generated backward for every
such completed admitted composition; `backward_exists` supplies a witness.
They reuse `PtxTorchLean.DenseBackward.Encoding` and `Ranges` unchanged.

The strict margin keeps each real affine value away from the ReLU corner and
prevents rounding from changing its sign. At zero, the machine still has a
well-defined zero-gate convention, but the real-gradient accuracy theorem does
not apply. A test of that convention is not a differentiability proof.

## Run the checks and understand the limits

From the repository root:

```sh
bash scripts/check.sh
bash integration/torchlean/check.sh
```

The integration check builds the pinned project, freshly runs interpreter
examples, rejects unfinished proofs and inspects exact theorem dependencies.
The grid backward checks execute all five instruction stages and validate
replay, completion, gradients and operand preservation. Cases include padding,
negative gradients, all empty-dimension combinations, the zero-gate convention,
and a 33-by-32 matrix whose forward reduction, transposed reduction, weight-gradient
and copy stages exceed 1,024 total lanes. Its 33-element gate uses a partial final group. Existing interleaving and private-barrier checks
remain in the suite. These examples supplement the general proofs.

Each individual reduction still fits one group of at most 1,024 lanes. Scratch
retains the full indexed extent per group, as described above; no shared-memory
capacity or performance claim follows. Reductions split across groups, compact
scratch addressing, general communicating CTAs, runtime/ABI correspondence,
GPU execution and benchmarking remain outside this completed bounded milestone.
