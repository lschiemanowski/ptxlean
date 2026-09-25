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

The implementation fixes matrix layout, thread ownership, reduction order,
scratch lifetimes, dimension and address bounds, and the sequence of completed
launches. Non-power-of-two reduction lengths use positive-zero padding. Empty
reductions have value zero. Each memory access must be justified by the supplied
storage and computed address. Execution existence, correctness of completed
executions, synchronization and memory safety are separate proof obligations;
no desired numerical result substitutes for an instruction execution or a
memory-visibility argument.

Numerical contracts relate finite encoded inputs to ideal real tensors. Bounds
follow the actual multiplication and tree-addition order, including bias and
backward arithmetic. A strict error margin at each activation proves that
rounding cannot change its branch. Result freedom in the underlying instruction
contracts is retained. The stored forward outputs and all input, weight and bias
gradients are related to the actual TorchLean forward and generated backward.

The first implementation uses binary32 with explicit separate rounding, fixed
contiguous layouts, and a bounded cooperating thread group for each reduction.
It aims at an efficient parallel structure without claiming measured speed.
GPU execution, benchmarking, CUDA runtime correspondence, mixed precision,
tensor-core instructions, batched matrix multiplication and hardware conformance
are outside this component. Proof checking and fidelity to documented PTX
semantics remain distinct.
