# Poisson correspondence

The solver returns a vector intended to solve the discrete Poisson equations.
Its accepted correctness condition is zero on boundary nodes and
`‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)` on interior nodes. Here the norm is the
Euclidean length, A is the TorchLean tensor operator interpreted in exact
arithmetic, and the coefficients are the exact real values of the uploaded
binary64 words. They are not ideal quadrature values recomputed over the reals.

An executable check recomputes this residual using rational arithmetic and
compares squared quantities, avoiding a rounded square root. It rejects
nonfinite input or solution words, negative tolerances, nonzero boundary values
and an excessive residual. Its soundness proof applies to any accepted vector.
Neither a reported GPU norm nor a convergence flag is an accuracy premise.
The whole-solver theorem reads x from the final execution's stored bytes and
reads the equations and tolerances from the original uploaded bytes.

Instruction execution records actual fetched instructions, register changes,
loads, stores, branches and returns. Binary64 memory operations use eight
little-endian bytes; connectivity indices and flags use four. Physical layout
conditions require alignment, complete allocated buffers, nonwrapping addresses
and the stated separation of buffers. Memory safety follows from these
conditions and the fetched instructions, not from an assumed numerical answer.

A candidate read may choose arbitrary bits before its sources are checked.
Each byte must match initialization or an actual recorded store. Same-thread
causality rules exclude a later overlapping write as the source of an earlier
read. For shared memory, actual producer instructions, arrivals and completion
of a whole-block barrier establish visibility to later consumers. Reused shared
locations additionally require the appropriate barrier round and ownership.
These are necessary source constraints for the synchronous, generic-address,
non-aliasing fragment. They are not the complete PTX memory-admission rules.

Publication means reconstructing memory from the stores in a completed trace.
It supplies the next modeled launch's input. This mathematical operation does
not prove CUDA visibility or host/device transport. Instruction arithmetic uses
the pinned binary64 model, preserves separate multiplication and addition
roundings, and retains the documented freedom in exceptional encodings.
FloatLib connects exact finite-word decoding to real values; compiler and GPU
conformance are separate claims.

Each cell uses one block of 32 threads and seven shared matrices. Polynomial
degrees one through four give matrix widths two through five; inactive lanes
still participate in all four barriers. The basis and quadrature dimensions
must agree for the stated TorchLean operator connection. The supported
coefficient layout places the basis at offset zero, the derivative after its
matrix plus a 32-byte guard, and the weights after the next such guard.

The complete cell proof starts with the actual launch prologue and reads the
connectivity table to gather the input vector. It then executes all eight
ordered matrix contractions, weight multiplications, shared stores, barriers,
final addition, global output store and return. Each contraction starts from
positive zero and traverses inner indices in increasing order. Register and
byte-source proofs derive the operands and results; no phase answer or desired
shared snapshot is supplied as a hypothesis.

For every completed admitted cell/grid execution, the published element values
have the proved TorchLean meaning under their explicit input-representation
conditions. The grid keeps shared storage private to each block and element
outputs disjoint. Conversely, valid initial storage supplies finite executions
for arbitrary input words, including padding lanes and actual barrier events.
A serial schedule witnesses existence without restricting the universal
correctness theorem to that schedule.

Assembly assigns one writer to each global node. Uploaded row offsets and
entry indices select its element contributions in the same order as the
TorchLean scatter calculation. Filtering irrelevant contributions preserves
rounded addition order; associativity of floating-point addition is not used.
Table-shape and index bounds establish memory safety. A stronger ordered-table
representation connects the entries to the intended mesh operator.

Actual input/output separation forces assembly reads to come from the initial
bytes of that launch. The proof covers boundary masking, all rounded blocks of
256 threads, padding returns, output publication and preservation of unrelated
bytes. Valid metadata also supplies a finite admitted execution. Composing
actual cell stores with this assembly, and then the fresh-residual launch,
produces the rounded residual of the represented TorchLean operator. Preserved
right-hand-side and metadata bytes are proved from write footprints, not
assumed to survive the preceding launches.

A dot product uses one block of 256 threads. Each thread accumulates its
strided input coordinates with separately rounded multiplication and addition.
The block combines those partial sums through eight shared-memory reduction
rounds, then lane zero publishes the result. Nine actual barriers cover the
initial publication and the eight rounds. This order is part of the numerical
specification; agreement with a sequential CPU sum need not be bitwise.

The proof includes the native predicate/branch instructions, strided input
loop, all shared writes and reads, reused-location visibility, final global
store and every return. Allocation bounds and a disjoint output word protect
input reads. Every completed source-admitted execution publishes the specified
rounded reduction and preserves other bytes. A complete finite execution exists
for arbitrary valid input words. No local reduction result is supplied in lieu
of executing its instructions.

The vector kernels execute full rounded launches: the smallest number of
256-thread blocks covering the nodes. The node count and number of cell entries
are each below 2³⁰, so the modeled unsigned indexing does not wrap. Padding lanes
execute the actual guard and return without touching vector storage.

Initialization copies the boundary-masked load to rhs and r, divides it by the
diagonal to obtain z and p, and sets x to positive zero. At boundary nodes the
divisor is one. The combined update computes x + alpha*p, r − alpha*ap and the
new residual divided by that diagonal, with separate roundings. Direction
update computes z + beta*p. Restart copies the freshly recomputed residual
into r and divides it to reset z and p. Fresh-residual computation subtracts
the actual assembled operator word from the actual rhs word.

Complete instruction proofs cover initial parameter/index setup, actual loads,
all stores and return. In-place x, r and p reads are justified by ownership
and same-thread source order. Other input reads follow from physical separation.
Each completed admitted interleaving publishes these rounded results and
preserves non-output bytes; each valid layout admits a finite execution.
The original residual instruction representation and the common control-flow
representation have a proved fetched-execution translation in both directions.

Scalar kernels run in one thread and use separate aligned numerical fields
and four-byte flags. Start computes the rounded rhs norm and tolerance, stores
the initial residual and sets active=1 and broken=0. Alpha divides rho by the
denominator only when active is nonzero and both operands are finite and
strictly positive; otherwise it writes positive zero. A failed active guard
sets broken. An already set broken flag does not itself disable that division.

Beta marks nonfinite rho_next as broken when active is nonzero; negative finite
rho_next alone does not fail that guard. It uses use_step to select division or
positive zero, copies rho_next to rho, and computes active from use_step, the
recursive residual/tolerance comparison and broken. Residual-norm computes
the rounded square root of the fresh squared residual. Restart-flag writes one.
These decisions determine execution control, not exact residual acceptance.

The mixed-width source proofs derive each scalar read from initial bytes:
actual reads precede same-field writes and different fields cannot overlap.
Fetched arithmetic, predicates and stores determine every output and preserve
neighboring bytes. All five entries have finite admitted executions. Signed
zero, nonfinite values, ordered comparisons and the NaN/positive-zero behavior
of abs and max remain explicit in the instruction contracts.

The host driver threads one persistent byte allocation through every launch.
Named buffers cover coefficients, connectivity, assembly tables, boundary
flags, input vectors, working vectors and scalar control. Projection into each
kernel interface proves the required addresses, bounds, widths and separation.
Actual write footprints show that uploaded equations, index tables and
tolerances never change. Those facts justify reusing the tables in later
iterations; no desired numerical result is part of the layout assumptions.

Six preparation launches initialize the solver. Each iteration requests nine
ordinary launches. A periodic check, also forced on the last iteration, adds
five launches that recompute the residual from x. The host inspects actual
published status bytes, first rejecting a nonfinite norm, then testing
convergence, then breakdown, and finally restarting when inactive. A restart
adds three launches, including on the last iteration if its conditions hold.
Zero allowed iterations still performs preparation and the initial norm check.

The concrete launch relation includes all 21 entry names and their fetched
PTX executions, returns, necessary source admission and actual publication.
For valid physical storage, supported coefficient positions, bounded
connectivity and valid assembly indices, the entire finite host program has a
terminating model execution. It requests at most `6 + 17 * maxiter` launches.
This discharges kernel-existence premises using concrete execution witnesses;
it does not assume that each requested launch can return.

Every completed modeled host execution preserves the uploaded problem. If its
actual final x passes the exact acceptance gate, the accepted-solver theorem
gives zero boundary values and the requested real residual bound for that same
problem, together with the launch bound. Convergence is not unconditional:
maxiter, breakdown or failure of the exact check are legitimate outcomes.
Existence of one terminating schedule is not progress for every GPU schedule.

Source fidelity and proof validity have separate evidence. Lean checks the
proofs against the stated instruction and memory model. Text-binding checks
compare the generated PTX entries and launch dimensions with their Lean
representations. Differential tests compare the real Python driver's launch
order and status decisions with an evaluator of the Lean host program, using
explicit mock launches to isolate control. They are tests of that connection,
not a theorem about Python, CUDA or GPU execution.

The archived-result checker decodes saved coefficient and solution words,
rejects malformed or nonuniform connectivity, and verifies that the uploaded
boundary agrees with the uniform-square boundary reconstructed by its parser.
Artifact hashes protect against changed saved inputs. The in-memory Lean gate
binds equations and solution directly to actual execution memory; connecting
a physical GPU run and serialized archive to that memory remains an external
transport and fidelity boundary. Neither the raw solve convergence flag nor a
standalone certificate is presented as a hardware instruction-trace proof.

The completed fragment does not establish full PTX memory admission, compiler
correctness, CUDA visibility, GPU conformance or scheduler fairness. It does
not promise unconditional PCG convergence, equality with CPU iteration history,
a continuous PDE error estimate or a conditioning-based solution-error bound.
Those are different claims from finite model execution, kernel correspondence
and sound acceptance of the returned solution.
