# Whole blocks and padding lanes

A vector can have 257 entries while the emitted kernel launches whole blocks
of 256 threads. That example launches 512 threads. The first 257 handle vector
coordinates; the others still exist and must execute their guard and return.
Proving only the active coordinates leaves those extra threads unaccounted for.

## What the instruction proof adds

`Rounded.count` describes the emitted block rounding. `Rounded.index` proves
that the actual block/lane multiply-add yields each thread's index without
unsigned wrap for fewer than 2^30 nodes. `Rounded.live` connects the instruction's
comparison with membership in the vector. Checks cover empty and one-entry
vectors, 255/256/257 entries, and the largest supported size. An empty vector
has no modeled threads; this does not authorize a CUDA launch with zero blocks.

`Observed.vector_padding` executes the actual six-instruction prologue for an
inactive lane. Its last instruction is the conditional return. There are no
loads or stores in this path, so no output storage is needed for padding.
`vector_padding_unique` proves the same absence of memory observations for any
completed candidate execution, regardless of other threads' load choices.

## Existence and arbitrary interleavings

`Parallel.extend_run` embeds the existing active execution into the rounded
thread set, with exactly the same instruction effects and access occurrences.
`complete_padding` then executes every extra lane. This is one finite witness
schedule, not a restriction imposed on correctness.

For universal correctness, `restrict_run` projects an arbitrary completed full
launch onto the active threads. `Rounded.history` uses the real guard proof to
show that this projection loses no memory record. Renaming participants changes
neither the occurrence numbers nor the accessed bytes. The compatibility proofs
therefore retain the original read sources. The same-thread no-future rule used
for in-place updates also transfers. No desired loaded value is supplied.

The global publication is identical before and after the projection. Existing
active-coordinate numerical and byte-frame theorems consequently apply to the
whole rounded launch. This preserves floating-point operation order and
permitted result encodings, rather than replacing the computation with a
mathematical answer.

## Covered kernels

- `Initialize.Arena.rounded_exists` and `rounded_correct` initialize the five
  output vectors, including boundary masking and the initial preconditioner.
- `AffineUpdate.Arena.rounded_exists` and `rounded_correct` publish the in-place
  direction update using the original direction values.
- `UpdateXRZ.Arena.rounded_exists` and `rounded_correct` publish the solution,
  residual and preconditioned residual updates.
- `RestartVectors.Arena.rounded_exists` and `rounded_correct` reset the three
  restart vectors from the actual stored true residual.
- `Assembly.Arena.rounded_exists` and `rounded_value` preserve the actual ordered
  contribution traversal and optional boundary mask. `entry_guarded` proves
  that exposing its common guard leaves the original program and jump targets
  unchanged.

Each also has `rounded_outside`, preserving all bytes outside its actual output
arrays. These results use the existing physical layout and necessary source
constraints. They establish model execution and publication, not complete PTX
admission, CUDA visibility, GPU fairness or hardware conformance. Rounded
fresh-residual execution and finite host-loop composition remain further steps.
