# First dense–ReLU forward GPU validation

The recorded run passed **37 cases and 341 output coordinates**, with three
launch attempts per case (empty outputs take the explicit no-launch path).
Every GPU output matched the Lean arithmetic reference and the independent
rational rounding evaluator bit for bit. Every output satisfied the exact
rational evaluation of its formal error allowance.

The run used an NVIDIA GeForce RTX 5090, driver 610.57.04, CUDA 13.2 `ptxas`
13.2.78 and PyTorch 2.11.0+cu130. Formal semantics are pinned to PTX 9.4; the
hardware artifact explicitly declares PTX 9.2, as explained in the
[compatibility review](ptx-compatibility.md). Input rows ranged from empty to
1024 columns; multi-row cases included 33 separate groups. The largest row
uses 1024 threads and 45,056 bytes of shared scratch.

Memory access, shared-memory race, synchronization and uninitialized-read
sanitizer replays all reported zero errors or hazards. Input regions and global
allocation guard words were unchanged. The entry adapter initializes every
shared plane and synchronizes before entering the formal body.

Ordinary PyTorch agreed within the separately declared diagnostic allowance,
but **67 of 341 output coordinates had different bits** from our kernel.
Those differences are retained in the report; they are not counted as bitwise
equivalence. They are not always tiny: the cancellation fixture returns 1 in
our fixed tree, 2 in PyTorch and 2 in exact arithmetic. Our error of 1 is below
its calculated allowance of about 3.5. A valid error bound need not guarantee
small relative error for an ill-conditioned sum. PyTorch's reduction implementation need not follow our balanced
operation order. The experiment establishes observed agreement within the
stated checks, not a formal correspondence theorem for that backend.

The largest observed fraction of a kernel coordinate's error allowance was
about 0.9594. This shows that the bound check was not merely a huge fixed
`allclose` tolerance. Inputs span many magnitudes, so the full report records
exact rational errors and allowances rather than only one aggregate decimal.

[The receipt](receipts/dense-forward.json) identifies the source files, input and
export hashes, binary artifacts, environment and checks.
`receipts/dense-forward.tar.gz` contains the complete run artifacts, including
inputs, generated PTX, cubins, formal instruction manifests, numerical outputs
and sanitizer logs. These are project-generated materials, not copies of the
NVIDIA manual. Extract into a fresh directory and use `--replay` to execute the
recorded binaries, or regenerate with the commands in the [guide](README.md).

The experiment does not verify the emitter, entry wrapper, driver or hardware.
It does not establish behavior on another GPU, prove PTX-version refinement,
measure performance, or validate backward/softmax execution. Those remain
separate milestones. No mismatch was hidden by changing an error allowance or
removing a failing supported case.
