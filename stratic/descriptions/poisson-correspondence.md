# Poisson correspondence

A correspondence proof must explain what the GPU computes, rather than assume
that an operator call already has the right answer. The local cell calculation
uses five phases separated by barriers. Each lane computes one matrix entry,
with a sequential sequence of multiply and add operations. The proof relates
that ordered calculation to the actual TorchLean matrix-product definition.
It must not rearrange rounded sums using identities valid only over real numbers.

Assembly adds the contributions for a global node in element order. Filtering
other nodes' contributions out of that order must preserve its value even when
addition is not associative. Writes to different nodes may be scheduled in any
order because each node has one writer.

The GPU's dot product partitions inputs among 256 lanes, then combines partial
sums in a tree. That ordering belongs to its numerical specification. Agreement
with a sequential CPU dot product is not a universal bitwise property. The
solver must be related to its own rounded operations and fresh residual check;
a different iteration history is not itself a correctness failure.

Binary64 arithmetic uses the pinned Lean logical Float model. FloatLib supplies
the exact dyadic decoding used by the residual checker and proved arithmetic
bridges under explicit finiteness conditions.
Those logical bridges do not themselves establish the behavior of a compiler
or physical GPU.

The final instruction-level connection must cover fetched instructions, register
updates, byte addresses and bounds, shared-memory barriers, assembly ownership,
and the host launch sequence. Relating a phase calculation to TorchLean alone
does not discharge these obligations. Completed lemmas state their own scope;
missing layers remain explicit rather than becoming theorem hypotheses asserting
the correspondence they are meant to establish.

The accepted whole-solver guarantee is an a posteriori residual certificate: a
check of the actual returned solution, independent of how the solver obtained
it. Exact rational arithmetic interprets the saved binary64 basis, derivative,
weight, load and solution words. NaNs, infinities, malformed shapes and altered
uniform connectivity are rejected. The coefficient values are the represented
setup values, not ideal quadrature recomputed over real numbers.

Acceptance requires zero boundary values and
`‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)` on interior nodes, where A uses the
TorchLean tensor operator in exact arithmetic. The check compares squared
rational quantities, avoiding any rounded square root or empirical allowance.
The soundness theorem applies to every accepted vector and does not assume
PTX correctness, PCG convergence or agreement with the CPU iteration history.
All rounding in the returned solution is included by checking its exact stored
values. Successful GPU status alone is insufficient for acceptance.

This establishes a result certificate, not an instruction-refinement theorem.
It does not prove that every GPU execution will terminate or pass the check,
and it gives no continuous PDE error or conditioning-based solution-error bound.
Compiled checker execution, input/output transport, and a particular saved GPU
run retain their stated runtime and provenance boundaries.

Instruction correspondence is proved from fetched code and its initial storage.
Binary64 loads and stores use eight little-endian bytes, with explicit alignment,
allocation bounds and nonwrapping addresses. Arithmetic preserves the supported
rounding behavior and treats NaN payload freedom separately from a canonical
Lean value. A completed execution must derive each observed output from these
steps; a premise that a phase already computes the tensor formula is insufficient.
The program checked by a theorem must also be tied to the emitted PTX, including
its predicates, integer indexing, branches and synchronization instructions.

The complete `true_residual` entry has a per-thread instruction proof. It loads
the actual right-hand-side and operator-result bytes, subtracts their binary64
values, and stores the corresponding TorchLean tensor-subtraction coordinate.
The proof includes parameter and thread-index reads, the out-of-range return,
execution existence, allocation bounds, and preservation of bytes outside the
one output word. It does not assume that the operator-result input equals A x.
Contiguous-array addresses are derived from the arena base and field offsets.
A checked frontend compares the proved instruction list with emitted PTX.

Parallel residual verification permits each eight-byte load to choose a candidate
word before checking its memory sources. Each byte must come from the initial
storage or a matching byte of an actual executed store. The executed instruction
trace supplies every store's calculated address and operand value. If the output
array is disjoint from both inputs, no thread can supply a store to an input
byte. Every input load must therefore recover its initial word, independently
of thread order or a freedom to combine byte sources.

For this closed launch, with no concurrent external writer or address alias,
the resulting output tensor equals TorchLean binary64 tensor subtraction.
The 256-thread index calculation is nonwrapping in the bounded array layout;
each active lane owns one disjoint output word. Padding lanes return without
memory accesses. Publishing the actual stores in any order yields the same
decoded output and preserves every byte outside the outputs. A witness supplies
successful fetched executions and compatible initial-byte sources.

The parallel proof uses necessary source constraints, allowing more candidates
than the complete PTX memory rules. A universal result over those candidates
therefore needs no sequential-consistency assumption. The witness is an
execution of this broader candidate model, not a full PTX admission or hardware
progress theorem. Publication describes storage after the completed stores; the
CUDA host-visibility mechanism is not proved. Shared-memory barriers, the cell
phases, assembly, reductions, remaining PCG kernels and host launch composition
still need their instruction-level connections. No premise that these phases
already compute their specified answers substitutes for that work.
