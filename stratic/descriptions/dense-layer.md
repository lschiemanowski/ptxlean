# A parallel dense–ReLU layer

The layer takes an input vector x of length n, a trainable m-by-n weight matrix W,
and a bias vector b of length m. It returns y_i=max(sum_j W_ij*x_j+b_i,0).
Its automatically generated TorchLean backward takes an incoming sensitivity
vector d of length m. With g_i=d_i on a positive affine value and zero otherwise,
it returns dx_j=sum_i W_ij*g_i, dW_ij=g_i*x_j and db_i=g_i. A zero derivative at
an exactly zero affine value is a chosen convention; ordinary mathematical
differentiation requires every relevant affine value to be nonzero.

The independently supplied binary32 implementation computes output rows in
parallel. Cooperating threads multiply pairs and combine their partial results
through a balanced addition tree. A tree round combines independent pairs at
the same time; it does not send all summation work to one leader. Synchronization
between rounds makes the preceding stores visible before their consumers read.
Bias and activation belong to the same forward computation. The cache-free
backward recomputes affine values and gates, uses another parallel reduction for
W-transpose times g, and computes weight-gradient entries independently.

The first forward kernel places all output rows in one cooperating thread array.
For a padded row width p=2^d, thread number r*p+c owns column c of row r.
The matrix is stored row by row. Global storage contains x, then W, then b,
then a separate output slice. Thread-number registers are supplied at entry;
ordinary integer instructions compute the row, column and byte addresses.
Out-of-range padded columns use zero operands without reading input storage.
Each round halves the active columns within every row, while all threads reach
the barrier. Column zero of each row adds bias, applies ReLU and stores output.
Shared storage reserves a full padded plane for each round, including the
initial products. Bounds must cover that total allocation and prevent address
arithmetic from wrapping. An empty output requires no launch; an empty input
can use a one-leaf zero reduction. This bounded single-array layout does not yet
cover larger layers split across multiple cooperating arrays.

The implementation fixes matrix layout, thread ownership, reduction order,
scratch lifetimes, dimension and address bounds, and the sequence of completed
launches. Each reduction round uses fresh shared scratch locations, with one
program writer per location. This makes the lifetime rule simple: no later
round overwrites a value that another thread may still read. The storage bound
must include all rounds; reusing scratch would require a separate lifetime proof.
Non-power-of-two reduction lengths use positive-zero padding. Empty
reductions have value zero. Each memory access must be justified by the supplied
storage and computed address. Execution existence, correctness of completed
executions, synchronization and memory safety are separate proof obligations;
no desired numerical result substitutes for an instruction execution or a
memory-visibility argument.

A selected execution witness chooses the software binary32 result and reads from
the current storage arrays. Its proof must reach every thread's exit, derive the
stored row outputs, preserve the input region and bound every emitted access.
The witness retains concrete-read evidence through every instruction and
barrier. Replaying its emitted memory events checks every load value and
reproduces the final arrays. Each load is traced to the initial contents or the
last preceding store to that location, with global and shared storage kept
separate. The selected witness also supplies a graph on exactly those memory
events, with a proved read source for every load and an order for writes to the
same location. A chronological certificate proves that this graph satisfies the
existing memory constraints and the ordering derived from its actual completed
barriers. It also excludes circular chains through those order and read-source
edges. This establishes an admitted execution with the stated stored outputs.
Correctness for all admitted executions remains a separate obligation: their
reads need not follow the witness's selected chronology.

Numerical contracts relate finite encoded inputs to ideal real tensors. Bounds
follow the actual multiplication and tree-addition order, including bias and
backward arithmetic. A strict error margin at each activation proves that
rounding cannot change its branch. Result freedom in the underlying instruction
contracts is retained. The stored forward outputs and all input, weight and bias
gradients are related to the actual TorchLean forward and generated backward.

The bound for a selected stored row follows from finite input interpretations,
explicit encoding errors and checks on the calculated intermediate ranges.
It does not assume the accuracy of intermediate results. Each unpadded leaf
matches one stored weight and input word to the corresponding real tensor
entries, with explicit encoding errors. Padded leaves contain exact positive
zero operands. The proof removes those zero terms from the ideal real sum and
identifies each row with the actual TorchLean matrix-vector, bias and ReLU
graph. The resulting bound concerns the output words of the same admitted
execution; it is agreement within an error bound, not bitwise agreement with
an external PyTorch implementation. Tree-rounding and finite-range conditions
remain explicit and follow the implementation's fixed reduction order.

The first implementation uses binary32 with explicit separate rounding, fixed
contiguous layouts, and a bounded cooperating thread group for each reduction.
It aims at an efficient parallel structure without claiming measured speed.
GPU execution, benchmarking, CUDA runtime correspondence, mixed precision,
tensor-core instructions, batched matrix multiplication and hardware conformance
are outside this component. Proof checking and fidelity to documented PTX
semantics remain distinct.
