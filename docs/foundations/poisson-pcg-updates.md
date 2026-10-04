# PCG vector updates

PCG is the preconditioned conjugate-gradient algorithm used by the FEM solver.
Its search direction p tells the next iteration where to move. After updating
the residual and its preconditioned version z, it computes

    p[i] = z[i] + beta * p[i]

Beta is one scalar shared by the whole vector. Each thread owns one coordinate.
The old p is an input and the new p occupies the same storage, so this is an
in-place update.

## Instruction and numerical meaning

The search-direction update has a complete per-thread fetched proof. Each
active thread executes the real launch-parameter and index setup, loads scalar
β and its old p and z words, computes the separately rounded product β · p,
adds z, stores the result and returns. Every other byte remains unchanged.
Padding threads return without memory accesses. Valid allocations give finite
execution witnesses for both paths. The 25-instruction Lean program is compared
with the emitted update_p entry, including the product register, scalar address,
in-place output address and unsigned guard. The parallel proof derives old inputs from the same actual interleaved history
and publishes the separately rounded update. The full PCG loop remains separate.

`AffineUpdateCorrect.correct` covers the instruction body and permits arbitrary
binary64 values. It states decoded equality, preserving permitted exceptional
encodings. `VectorEntry.completed_body` recovers the body from the actual fetched
prologue and return. `AffineUpdateEntry.entry_correct` joins them.

The theorem does not rewrite multiplication and addition as exact real-number
operations. For example, even if a real-number identity simplifies z + beta*p,
that identity cannot remove either rounding step in this implementation.

## Why the in-place read needs care

In-place updates need a source rule beyond byte compatibility. For synchronous
same-thread accesses using ordinary addresses and the generic memory proxy,
PTX causality forbids a read from taking bytes from a later overlapping store.
The restricted rule is explicit: it applies to actual same-thread occurrence
order at the same word address. If ownership excludes other writers, it forces
the old value to come from initialization. It does not order unrelated threads
or cover aliases, asynchronous accesses or the full PTX memory model. A
kernel-checked counterexample shows that byte compatibility alone accepts a
circular read justified by its own later write; the new rule rejects it.
Actual launch-derived ownership and instruction order discharge these conditions for the direction update.

Consider a single thread which loads p and later stores that same loaded value
back. If initial p is zero, byte compatibility alone can still propose that the
load reads the value one from the later store. The proposed store then repeats
one, apparently justifying the load. This is circular: no executed earlier
operation supplied the one. `GlobalThreadSourceChecks.compatibility_alone`
checks this counterexample; `circular_rejected` proves that the explicit future-
store exclusion rejects it.

`AffineUpdateSources.Arena.read_value` now proves those facts for the actual
entry. `ObservedParallelNative.before_of_pc` embeds its same event history in
the native machine and derives event order from actual instruction counters.
`GlobalThreadSources.before_own_writes_initial` then excludes every store source.

## Parallel replay, publication and existence

The parallel direction update derives all input reads from its actual
interleaved history. Launch registers select disjoint eight-byte p slots.
The coefficient and z array are read-only. The old p read occurs at instruction
13 and its owning thread's store at instruction 23; no other thread can write
that word. Actual same-thread instruction order and the explicit no-future
source constraint force the read to obtain initialization bytes. Neither old
input values nor desired output equations are assumptions.

Scalar replay preserves only reads that remain to execute. It permits the
in-place write after the last read instead of requiring input/output separation.
Every completed admitted active-thread interleaving publishes z + beta*p with
separate binary64 multiply and add roundings. Bytes outside the p array remain
unchanged, including the coefficient, other vectors and padding. The result
states decoded equality and allows exceptional encoding freedom.

A finite execution with compatible initial-byte sources and the no-future
constraint exists for every valid array layout and arbitrary input words.
Its numerical result follows from the same universal publication theorem.
The joint launch contains active coordinates; padding returns are proved
separately at the per-thread level. This does not establish full PTX admission,
CUDA visibility, progress for every schedule, hardware conformance or complete
PCG launch composition.

For example, two lanes may interleave their coefficient and vector loads in any
order. They each read their own old p, and either may store first. Once lane zero
has consumed its p, its store need not preserve that old value for lane zero:
there is no future read of it. Lane one's future read uses a disjoint slot.
`ObservedTemporalReplay.replay_temporal` expresses this distinction and recovers
actual scalar instruction execution without assuming full input/output separation.

`AffineUpdateParallel.Arena.parallel_value` proves the published vector formula.
`publication_outside` preserves every byte outside p, even for incomplete runs.
`AffineUpdateExists.Arena.parallel_exists` constructs a finite run and proves
its sources and numerical result together. No input finiteness condition is
needed for these instruction-level decoded-value statements.

## Source fidelity

The source check used the pinned PTX 9.4 HTML digest
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The interpretation uses NVIDIA's [program order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#program-order),
[causality order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-order)
and [causality axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-axiom).
For same-thread synchronous accesses, instruction order supplies program order;
using the generic proxy at the same identity address preserves that relation
into causality. The causality axiom then excludes a later overlapping store as
a source. This manual interpretation is distinct from Lean proof checking.

The new source predicate records only that necessary restriction. It is not a
complete memory-model admission checker or a GPU execution guarantee.

## Updating the solution and residual together

The combined PCG update computes x := x + alpha*p, then r := r - alpha*ap,
then z := r/diagonal. Here ap is the already computed operator applied to the
search direction. At boundary coordinates the divisor is the exact binary64
word for one. Alpha is loaded once and reused; each multiplication, addition,
subtraction and division rounds separately. The preconditioner uses the newly
computed residual register. No real-number rearrangement or fused operation
replaces the emitted arithmetic.

The full 54-instruction fetched entry is proved, including launch indexing,
active and padding paths, all input loads, three stores and return. Its physical
layout bounds and aligns one scalar, six disjoint binary64 arrays and the
four-byte boundary flags. Output arrays x and r reuse their own initial storage.
Earlier stores preserve every later input field. Actual instruction addresses
and array ownership exclude stores by other threads; the x and r reads precede
their own writes. Byte compatibility and the explicit same-thread no-future
source rule therefore derive the old input words from initialization. The
boundary load is separately justified by four-byte source compatibility.

Every completed admitted active-coordinate interleaving publishes the three
rounded initial-input formulas and preserves every byte outside x, r and z.
A separate construction executes the same entry, preserves only not-yet-consumed
input words, and produces a finite joint history with compatible initial-byte
sources and the no-future constraint. Arbitrary input words, including exceptional
values and zero diagonals, are permitted; numerical acceptance remains separate.
The emitted entry is bound instruction for instruction across the saved layouts.
These are necessary fragment admission constraints, not the complete PTX memory
model. Joint padding scheduling, CUDA visibility, hardware conformance,
scalar decision kernels and full host PCG
composition remain separate obligations.

The important order is visible in the instruction counters:

| Access | Load | Store |
| --- | ---: | ---: |
| alpha scalar | 9 | read-only |
| p | 13 | read-only |
| x | 17 | 23 |
| ap | 27 | read-only |
| r | 31 | 37 |
| diagonal | 41 | read-only |
| boundary flag, four bytes | 45 | read-only |
| z | not read | 52 |

For example, the store to x precedes the load of r. The proof needs physical
separation between those fields; merely saying that each lane owns one index
would not suffice. Conversely, x is read before it is overwritten, so requiring
that input x and output x occupy separate buffers would reject the real kernel.
`UpdateXRZSources.Arena.read_value` handles both cases from recorded accesses.
`UpdateXRZPending.Arena.pending_step` preserves just the inputs whose load
instructions remain ahead, which supports the independent execution witness.

`UpdateXRZCorrect.entry_correct` covers a single fetched thread. The universal
joint result is `UpdateXRZParallel.Arena.parallel_value`; it obtains local
execution by temporal replay and merges actual output stores. The independent
witness is `UpdateXRZParallelExists.Arena.parallel_exists`. The exact one-word
constant is kernel-checked by `PreconditionUpdate.decode_one`. The source-binding
checker compares all 54 rendered instructions, including the boundary selector
and division operand order, and audits the named theorem dependencies.

## Restarting from a freshly recomputed residual

Restart copies the freshly recomputed residual into r and divides it by the
diagonal to obtain z and p. At boundary coordinates it substitutes the exact
binary64 word for one as divisor. The two quotient stores use the same actual
result word, including any permitted exceptional-value encoding. The residual
copy is bit for bit. These are statements about the actual loads, arithmetic
instruction and stores, not supplied numerical answers.

The complete 34-instruction fetched entry includes launch indexing, the active
and padding paths, the four-byte boundary load and return. A physical layout
bounds and aligns five mutually separate binary64 arrays and separate boundary
flags. Actual instruction addresses derive array ownership. No output store
can overlap a source-residual, diagonal or boundary read, so byte-source
compatibility forces every input read to the initial memory. Every completed
admitted active-coordinate interleaving publishes r, z and p with the stated
values and preserves bytes outside those output arrays. Independently, the
same instruction list has a finite joint execution with compatible initial-byte
sources for arbitrary input words; no nonzero-diagonal or finiteness assumption
is needed for execution. Numerical acceptance is a separate question.

The emitted restart entry is compared instruction for instruction across saved
layouts. The necessary fragment source constraints do not establish the complete
PTX memory model, and finite schedule existence does not establish GPU fairness.
Joint padding scheduling, CUDA visibility and hardware conformance remain
separate. Scalar decision kernels and host-loop composition
still need their corresponding results before claiming complete solver
correspondence.

The residual-copy load is at instruction 9, its r store at 13, the diagonal
load at 17, the boundary flag load at 21, division at 24, quotient stores at
28 and 32, and return at 33. The load source is the separate `true_r` array.
This separation is why restart can use ordinary source replay: unlike the
in-place x/r and direction updates, none of its input arrays is overwritten.

`RestartVectorsCorrect.entry_correct` relates a completed fetched thread to
its input bytes. `RestartVectorsParallel.Arena.parallel_correct` derives the
joint publication from actual admitted observations. `RestartVectorsExists.Arena.parallel_exists`
constructs one actual finite schedule and its sources. `ArrayArena` shares the
physical array-layout facts across such kernels; `DividePair` preserves the
actual quotient word rather than forcing every result to a chosen encoding.

## Initializing the solver vectors

Initialization reads each coordinate's load and boundary flag. It substitutes
positive zero for the load at boundary coordinates, copies that same word to
rhs and r, divides by the diagonal (substituting one on the boundary), and
stores the same actual quotient word to z and p. A separate immediate-word
store initializes x to positive zero. The predicate chosen from the boundary
flag survives the intervening stores and diagonal load; no desired predicate
outcome or numerical input is supplied to the proof.

The complete 43-instruction fetched entry includes actual launch indexing,
active and padding paths, word and four-byte loads, all five stores and return.
Its bounded, aligned physical layout separates seven binary64 arrays and the
boundary flags. In particular the early rhs/r stores cannot alter the later
diagonal load. Actual access classification and physical ownership show that
no output store can supply any input read. Word and four-byte source
compatibility therefore force the initial input bytes. Every completed admitted
active-coordinate interleaving publishes all five stated outputs and preserves
every byte outside rhs, r, z, p and x. Independently, a finite joint execution
with compatible sources exists for arbitrary input words. Zero diagonals and
exceptional values do not prevent execution; numerical acceptance is separate.

The exact emitted instruction list is bound across saved layouts, including
both zero-word instructions and the boundary divisor. These results use necessary
fragment admission constraints, not the complete PTX memory model. Joint padding
scheduling, GPU fairness, CUDA visibility and hardware conformance remain
separate. Scalar decision kernels and host-loop composition remain obligations
for full solver correspondence.

The boundary load is at instruction 9, the load-vector read at 13, the rhs/r
stores at 19 and 23, diagonal read at 27, division at 29, z/p stores at 33 and
37, zero-x store at 41 and return at 42. `InitializePrefix.prefix_trace` keeps
the actual boundary predicate through the copied vectors and diagonal read.
`InitializeCorrect.entry_correct` proves the single fetched entry;
`InitializeParallel.Arena.parallel_correct` derives joint publication from
actual sources, and `InitializeExists.Arena.parallel_exists` constructs a finite
execution. `StoreZero` models the emitted immediate store explicitly.

## Scalar residual norm and restart flag

The scalar residual-norm entry loads the stored sum of residual squares,
computes its binary64 square root with rounding to nearest, and stores that
actual result. Its complete 13-instruction fetched execution determines the
numerical output and preserves bytes outside the output word. The separate
8-instruction restart-flag entry stores the four-byte unsigned value one and
preserves every other byte. Both entries have finite execution witnesses for
arbitrary input bytes in valid allocations. These are single-thread sequential
byte-memory results; they do not yet derive this execution model from weak-memory
candidate admission or connect it to CUDA transport between launches.

The additional scalar instruction contracts distinguish numerical value from
bits. The pinned abs.f64 rule preserves NaN input bits; ordinary inputs have
only their sign bit cleared. Unmodified max.f64 ignores a sole NaN, permits NaN
encodings when both inputs are NaN, and prefers positive zero to negative zero.
Ordered floating comparisons return false on either NaN input. Predicate
conjunction, negation, unsigned selection and conditional arithmetic read the
actual predicate registers. Four-byte status stores check actual addresses and
allocation bounds. These contracts and the existing base instructions form a
separate wrapper, leaving the earlier concurrent instruction semantics intact.
Kernel-checked corner cases support the manual pinned-source review but do not
establish hardware fidelity.

Full-entry text binding checks both scalar programs across saved layouts.
Scalar weak-memory justification and host-loop composition remain separate
obligations; the start and coefficient proofs below cover their sequential
instruction behavior.
The norm computation itself is not a residual certificate: the accepted solver
claim still requires a fresh residual bound for the same discrete equations.

`ScalarNorm.entry_correct` derives the stored norm from the source memory word;
it does not assume that this input already equals a mathematical residual norm.
The dot-product and operator proofs must supply that connection during
composition. `ScalarRestartFlag.entry_correct` covers the actual four-byte
status write. Each module also provides `entry_exists`. The renderer and binding
check use the same entry definitions, including the three-instruction launch
prologue and return. See [the scalar source review](poisson-scalar-source-review.md)
for the exceptional-value choices and their limits.

## Start and coefficient selection

The solver's start, alpha and beta entries have complete fetched-instruction
proofs in the single-thread sequential byte-memory model. Start computes the
rounded square root of the stored RHS squared norm, copies that result into
the initial residual field, computes max(rtol times norm, atol) with separate
binary64 rounding, and writes active=1 and broken=0. Alpha reads the stored
denominator, rho and flags. It enables rho/denominator only when the active
flag is nonzero and both floating inputs are finite and strictly positive;
otherwise it stores positive zero. A failed active guard sets broken. An old
broken flag is preserved but does not itself disable this alpha division.

Beta marks a nonfinite rho_next as broken when active is nonzero, while a
negative finite rho_next alone does not fail that guard. The use_step flag
controls rho_next/rho; the disabled case stores positive zero. Beta also copies
the actual rho_next word into rho. Its final active flag requires use_step,
an ordered comparison of the stored recursive residual square with the rounded
tolerance square, and a zero broken flag. This recursive residual test is not
the fresh residual certificate and does not by itself establish convergence.

These results derive arithmetic and predicate inputs from the actual loads,
retain permitted rounded-result encodings, describe every output byte and
preserve all other bytes. Their finite execution witnesses require only a
valid physical scalar layout, with no numerical result or guard outcome assumed.
The scalar layout has separate aligned eight-byte numerical fields and
four-byte status fields, all within a nonwrapping allocation. Complete text
binding covers 39 start instructions, 49 alpha instructions and 63 beta
instructions, including launch setup and return. Scalar weak-memory admission,
whole-launch composition and the finite host PCG loop remain separate
obligations; CUDA transport and GPU conformance are not established here.

The main results are `Scalar.Start.entry_publication`,
`Scalar.Alpha.entry_publication`, and `Scalar.Beta.entry_publication`. Each has
an `entry_exists` theorem. `Allowed` describes the enabled rounded quotient or
the exact disabled zero; the proof derives which branch applies from loaded
flags and operands. `Scalar.Arena` contains physical layout facts, not solver
answers. `hardware/check_poisson_control.py` checks the full saved entries
against the same Lean program definitions. Mutation tests reject changes to
rounding, operand order, predicates, widths, layout and launch shape. Seven
kernel-checked guard examples include old broken flags, inactive infinities,
NaN and signed-zero denominators, and negative finite rho_next.

## Remaining work

Scalar weak-memory admission and the host PCG loop still need their
instruction-level composition. The accepted solver target remains a fresh
residual bound for the same discrete equations, rather than CPU-iterate bitwise
identity or a convergence claim for every input.
