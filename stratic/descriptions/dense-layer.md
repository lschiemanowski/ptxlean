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

The backward uses a sequence of completed kernels with explicit intermediate
storage. It recomputes the forward activation, gates the incoming sensitivity,
forms independent weight-gradient products, and reduces transposed weight rows
against the gated sensitivities to form input gradients. Bias gradients are the
gated sensitivities themselves. Passing storage between completed kernels is a
model-level composition contract; it is not a CUDA runtime implementation.

The reduction kernel also offers an affine-only output option that leaves signed
results intact. The ReLU forward variant retains its existing computation. This
shared implementation avoids duplicating the reduction and synchronization
proofs for the transposed matrix-vector product. A copy kernel constructs the
transposed operand buffer from the actual stored
gated sensitivities and original weights. Each copied word comes from a fetched
load and store. Appending freshly allocated zero words and selecting the copied
buffer as the next kernel's allocation are explicit operations of the host model.
They perform no gradient arithmetic and do not constitute a CUDA allocation,
transfer, synchronization or pointer-ABI implementation.

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
can use a one-leaf zero reduction. This single-array variant has a bound on the
total thread count; the grid variant below distributes rows across arrays.

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
Universal correctness also covers admitted executions whose read choices need
not follow the witness's selected chronology.

The supplied forward instruction list contains no jumps or scalar exits. Its
arbitrary candidate traces therefore inherit strict instruction order within
each thread: each store site can occur at most once, and a store at an earlier
instruction position precedes that thread's later barrier arrival. This removes
repeated execution of a store site as a possible source of competing writes.
The actual emitted stores are classified exhaustively: one product-store site,
one store site per reduction round, and one global output-store site. For an
observed completed barrier, a consumer at a later instruction site must occur
after its completion. Instruction order alone does not identify a store's address;
address ownership supplies that separate argument. A finished execution must
also supply actual producers and completed phases, not merely possible sites.

Address ownership is proved independently of the values loaded from tensors.
Registers holding thread identity, row and column coordinates, and address
arithmetic cannot acquire a loaded tensor value or a floating-point result.
A separate calculation retains those registers, address registers and the
predicate controlling active columns, while omitting tensor data. Each fetched
instruction must preserve agreement with this calculation, including skipped
instructions and barrier release. The calculation is a proof aid, not a
replacement for the kernel's execution or memory semantics. Its result must be
connected to the addresses of actual emitted stores before layout injectivity
can establish a unique writer. Every shared store has byte address
4*(stage*threadCount+threadNumber). Different stages occupy
separate planes. Every global store addresses its row's output word and is
issued by column zero. Together with at-most-once execution of a store site,
these facts give at most one program write to each memory location over an
arbitrary candidate trace. Initial contents remain a separate write; uniqueness
does not by itself prove that a required producer or completed barrier exists.

For a completed forward execution, each thread's exit supplies evidence that it
passed every preceding store and barrier site. Product stores are unconditional;
a reduction store is enabled precisely for columns active in that round; output
stores are enabled for column zero. The address-control calculation must prove
these predicates before an instruction occurrence counts as a producer. Passing a store means
its address check succeeded, so these conditional results need no extra promise
that an access succeeds. They do not claim every schedule finishes. Every
required barrier completion and producer is recovered from the actual trace.
Together with single-writer ownership and instruction order, this supplies the
execution evidence needed for visibility. The observed loads and actual
arithmetic are then connected to the reduction tree.

Every actual load must be tied to its computed address and enabled predicate.
Input, weight and bias loads refer to unchanged initial global words. Shared
loads refer to active producers in the preceding scratch plane. The producer
and consumer belong to the same row, and the completed barrier separates their
accesses. Admission under the memory constraints must force the observed value;
the selected execution's read choices are not a substitute for that argument.
For every admitted completed execution, the resulting instruction arithmetic
must establish the stated bound for the words actually stored in output memory,
while preserving inputs and both storage extents. An empty output bypasses the
kernel entirely and returns an empty tensor without a launch or memory change.

The value proof proceeds through the actual interleaving of instructions.
At each step, a register invariant records only values that later instructions
still need. A shared read inherits its arithmetic meaning from an earlier actual
store, whose value has already been proved; global reads inherit the original
input encoding. Multiplication and addition use their permitted-result relations,
not equality to one chosen software result. Stores therefore contain evaluations
of the specified reduction tree, bias addition and ReLU. A separate final-memory
argument identifies the words actually left in the output slice. No assumptions
about desired load values, intermediate accuracy, or a preferred schedule enter
the completed-execution theorem. Completion is still a premise of this theorem;
the separate witness proves that a completed admitted execution exists.

Numerical contracts relate finite encoded inputs to ideal real tensors. Bounds
follow the actual multiplication and tree-addition order, including bias and
backward arithmetic. A strict error margin at each activation proves that
rounding cannot change its branch. Result freedom in the underlying instruction
contracts is retained. The stored forward outputs and all input, weight and bias
gradients are related to the actual TorchLean forward and generated backward.

The bound for every stored row follows from finite input interpretations,
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

The backward has five completed stages: recompute ReLU(Wx+b), gate the incoming
sensitivities, multiply the weight-gradient entries, copy the transposed operands,
and reduce the input gradients. The gated buffer is also the bias-gradient
buffer, so a separate copy for db is unnecessary. Each stage starts with the
actual final words of the preceding stage. Every completed launch is admitted
under the existing memory constraints; no assumed intermediate gradient or
preferred schedule substitutes for that evidence. A separate construction
proves that all stages can complete. Every emitted access is checked, and each
launch preserves its allocation lengths. New buffers are allocated explicitly
between launches, and the original x, W and b words remain unchanged.

The small elementwise kernels assign one output word to each thread. Each thread
receives entry pointers computed from the stated layout, independently of tensor
values. Their input region is read-only and their output words are distinct.
The formal entry state installs those pointers; correspondence to a runtime's
argument passing remains outside the model. They implement a word copy, a
rounded multiplication, or the ReLU sensitivity gate using existing instructions.
Their correctness covers all admitted completed interleavings; their witnesses
supply finite admitted executions. Zero threads mean no launch.

The single-group backward's size limits cover each actual thread group. Forward reduction
uses m*2^forwardDepth threads, and input-gradient reduction uses n*2^backwardDepth.
The copy stage uses m+n*m+2*n threads, one for every word in its destination
packet, including its zero bias and output slots. Every group is at most 1024
threads. Pointer calculations must fit the stated arithmetic bounds, and scratch
storage includes all reduction rounds. These explicit limits can exclude shapes
that fit the forward kernel alone. The grid variant below removes this bound on
total launch threads; scratch reuse remains a separate extension.

For finite encodings and the calculated range conditions, every stored dx, dW
and db has a proved error bound relative to the actual TorchLean generated
backward. The strict activation margin implies that each real affine value is
nonzero and its sign agrees with the recomputed rounded value. Without that
margin, the instruction and storage theorems still describe the actual gated
computation, including the zero convention, but the numerical gradient theorem
does not promise agreement with the real network's derivative near a ReLU corner.
The transposed reduction uses the same balanced addition order and a final
addition of positive zero; that addition is included in its range and error
accounting. Signed input gradients are preserved by disabling ReLU in that stage.


The multiple-group extension distributes independent output rows across
cooperating thread arrays, or CTAs: groups with their own shared scratch memory
and barriers. All groups access one global allocation. They may read common
inputs, but each output location has one owning group. Instructions from different
groups may interleave; a collection of isolated group proofs alone does not
establish correctness of the combined launch.

Each row reduction remains entirely within one group, preserving its multiplication
and balanced-addition order. Pointwise gate, weight-gradient and copy work is
partitioned into bounded groups, including a partially used final group with allocated padding lanes. Input gradients
use the same distribution of transposed rows. Group count is separate from the
per-group thread limit; each individual reduction and each private scratch
allocation still satisfies explicit resource and address bounds.

The combined forward and backward contracts must derive actual stored outputs,
unchanged operands, checked accesses, and numerical correspondence for every
admitted completed grid execution. A separate construction must establish that
such executions exist. Empty dimensions retain explicit no-launch behavior.
Memory admission, inter-group noninterference and private barrier behavior must
be proved from the fetched execution; no assumption may replace the desired
result or the absence of interference. Runtime/ABI and hardware correspondence,
splitting one reduction across groups, and benchmarking remain outside this
extension.


Address arithmetic bounds and per-group launch limits are separate obligations.
The total number of row/column work items may exceed a single group's thread
limit while its represented indices still fit the chosen integer widths. Shared
scratch remains private to each group; its allocation bounds must cover the
addresses the supplied reduction program actually computes.


The first row-distributed reduction reuses the existing shape-specialized
instruction list. Entry states supply the row/column work-item number, so each
group executes exactly one row. Shared addresses retain the existing plane and
row offsets inside each group's private allocation. Consequently each private
allocation initially reserves the full indexed scratch extent, including unused
row positions. This is an explicit storage cost of proof reuse, not a compact
scratch layout or a claim that these allocations fit a particular GPU. The
resource contract must cover that extent. Compact rebasing is a separate change.

The multiple-group forward and backward have complete bounded launch contracts.
Every completed admitted execution stores the specified outputs and gradients,
preserves original operands, and satisfies the same numerical error policy as
the single-group version. A separate finite construction supplies actual
instruction executions and the combined memory-admission certificate; it does
not assume desired reads or completed isolated group results.

The grid backward recomputes the activation, gates sensitivities, forms weight
gradients, copies transposed operands and reduces input gradients. Pointwise
stages use groups of 32 lanes. The host model temporarily appends spare output
cells for the last group, then returns the logical prefix containing every
source and requested result. Padding writes remain part of the proved physical
launch. Bounds reserve 32 additional representable words, although fewer than
32 padding cells are allocated. These host storage views do not perform
arithmetic and do not establish runtime allocation or transfer correctness.
Forward and transposed reductions each use at most 1,024 lanes per row; the
whole grid may contain more. Empty dimensions retain explicit no-launch cases.
Numerical gradient agreement still requires the finite ranges and strict
activation margin described above. General reductions spanning several groups,
compact scratch rebasing and hardware performance remain separate extensions.
