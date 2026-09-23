# From litmus programs to scalar kernels

The foundation has explicit topology and allocation contracts, scoped whole-word
and bytewise memory models, a scalar interpreter, reusable proof rules, and
instruction-level integer kernel proofs, including vector addition over one
shared allocation. These are checked pieces of a PTX formalization. They do not
yet form a complete concurrent semantics for arbitrary programs with
data-dependent stores, computed addresses, and branches.

Read this guide first for orientation. The detailed guides cover
[environments and scopes](environment.md), [scalar execution](scalar-machine.md),
[reusable proof rules](scalar-rules.md), [shared-allocation kernels](shared-vector.md),
and [byte observations](byte-memory.md). The source reviews cover
[environments and scalar execution](blocks12-source-review.md) and
[byte observations and shared kernels](next-source-review.md), distinguishing
checked results from interpretations of the locally pinned PTX 9.4 source.

## What fits together

| Component | Checked result | Boundary |
| --- | --- | --- |
| Environment | Successful accesses satisfy ownership, full byte bounds and alignment; target examples accept/reject supported forms. | Allocation, lifetime and initialization are supplied contracts; this is not a CUDA allocator or complete target validator. |
| Scoped whole-word memory | Publication with mutual scope inclusion; within-CTA success, cross-CTA stale witness; partial raced-write coherence; exact legacy specialization. | Constant-store global arena, generic proxy, whole-word sources. This layer restricts out-of-scope races to non-torn candidates; the byte model below removes that restriction for fixed aligned accesses. |
| Bytewise memory | Per-byte sources, an admitted torn-read witness, scope-based rejection, and exact whole-word specialization; mutual scope coverage derives uniform sources. | Aligned u32 accesses, constant-store programs, generic proxy; no mixed-size overlap or aliases. Torn observation order has two explicit interpretations. |
| Scalar machine | Interpreter and finite derivations agree; traces retain actual register-derived effects; every emitted access is safe; memory extent is preserved. | Local sequential execution or explicitly unvalidated candidate reads, fixed u32 arena and u64 pointers. |
| Text boundary | Supported typed instructions survive encode/decode; unsupported mnemonics and malformed supported operands are rejected. | Typed operands and resolved labels are inputs. No raw PTX parser, assembler, module validation, or register allocator. |
| Arena bridge | Scalar validity is equivalent to access validity in its explicit global allocation view. | Access permission does not establish exclusive ownership or concurrent memory ordering. |
| Sequential kernels | Modular addition and a genuine branching array-sum loop have result, preservation and completed-execution proofs. | Owned sequential arena discipline; lane-wise product is not a launched GPU vector-add theorem. |
| Scalar proof rules | Execution-segment composition, preservation outside actual stores, invariant-based partial correctness, and termination from local progress and a decreasing measure. | Contracts for the scalar interpreter; candidate reads still need memory-model admission. |
| Shared-allocation vector addition | Instruction-level interleavings preserve inputs and other lanes' outputs; completed runs compute modular sums; a finite completed execution has a valid graph matching its actual memory trace. | Fixed disjoint input/output layout and sufficient allocation/pointer bounds; no general concurrent PTX completeness, launch ABI, or scheduler fairness theorem. |

## Follow an actual loop

Open [`Ptx/ScalarKernels.lean`](../../Ptx/ScalarKernels.lean). `sumLoop` has eight
instructions. The initial state supplies:

- `r0`: the number of words to consume;
- `r1`: the initial accumulator;
- `rd0`: the byte address of the first word;
- the complete initial word list and every other register and predicate.

The loop tests whether the count is zero. If it is, it branches to `exit`.
Otherwise it loads the current word, adds it to the accumulator, advances the
64-bit address by four bytes, decrements the 32-bit count, and branches back.
The reference `sliceSum` folds modular u32 addition over the selected slice.
There is no floating-point arithmetic or hidden mathematical-integer accumulator.

`sum_loop_correct` proves the result for arbitrary inputs, lengths, starting
indices, and initial accumulators. Its hypotheses are:

1. Execution starts at instruction zero with the specified count and pointer.
2. `start + count ≤ memory.length`: the entire slice exists.
3. `count < 2^32`: the initial counter represents the intended count.
4. `4 * (start + count) < 2^64`: advancing the cursor never wraps, including
   the final one-past position.

The last condition is a deliberately sufficient bound, not a claim that every
excluded execution would fail. A sharper bound could admit some endpoints that
are never dereferenced; it is unnecessary for this first reusable proof.

For zero count, three dispatches perform the comparison, taken branch and exit.
For positive count, `loop_advance` accounts for seven dispatches and reduces to
the shorter slice with the updated accumulator. Induction gives a budget of
`7 * count + 3`. The proof reduces real instruction execution; it does not assume
the loop body computes the reference sum.

`sum_loop_exists` packages a **halted** inductive execution with the result and
unchanged memory. `sum_loop_extra_fuel` proves any larger budget returns exactly
the same run, including its trace. `sum_loop_memory_safe` gives alignment and
complete four-byte bounds for every emitted memory effect. A safe emitted prefix
can still precede a fault, so that generic safety fact is intentionally separate
from the loop's no-fault completion theorem.

## Addition, storage and composition

`addLane` loads the words at offsets 0 and 4, adds them, stores to offset 8 and
exits. `add_lane_result` quantifies over arbitrary inputs, overwritten output,
untouched trailing memory, and initial registers. It proves the output is the
modular sum and every other memory word is preserved. `add_lane_exists` supplies
the completed derivation.

`elementwise_add` takes a family of these independent local views. Each lane
produces its corresponding result. The theorem is a product of local executions;
it does not prove a shared physical-memory embedding, a launch scheduler, or
noninterference of arbitrarily overlapping GPU threads.

The separate [`SharedVector`](../../Ptx/SharedVector.lean) model now places all
lanes in one allocation and schedules individual instructions. Lane `i` reads
words `3*i` and `3*i+1` and writes word `3*i+2`. The invariant proves that stores
preserve all inputs and every other lane's output. `completed_execution_exists`
constructs a completed execution of `5*n` dispatches with correct sums and
preservation of non-output words, under `3*n ≤ memory.length` and `12*n < 2^64`.
This disjoint layout supports arbitrary instruction interleavings; it does not
model arbitrary overlapping kernels or guarantee that every schedule completes.
The [shared-vector study](shared-vector.md) explains the scalar-step connection,
access safety, and explicit exit steps.

[`ScalarEnvironment`](../../Ptx/ScalarEnvironment.lean) makes one part of that
embedding explicit. `arenaEnvironment` maps a scalar arena to a global allocation
with initialized contents, a four-byte base-alignment guarantee and access on
the issuer's device. `arena_access_iff` proves its access check agrees with scalar
address validity. `run_environment_safe` lifts every emitted scalar access to
that contract. `separate_arenas` proves distinct allocation identifiers remain
distinct in the resolved-address representation; a real pointer/launch mapping
must preserve those identities.

## A scalar-to-memory correspondence result

[`ScalarMemoryWitness`](../../Ptx/ScalarMemoryWitness.lean) extracts the addition
lane's memory labels from its actual dynamic trace. Register-only and skipped
instructions contribute no memory label; event positions preserve dispatch
order. `events_eq` derives the table, including the store value computed by the
register addition. `label_preserves_address` justifies the byte-to-word mapping
for aligned effects.

The argument has both directions needed for a useful example. `candidate_correct`
quantifies over arbitrary candidate input reads and source/coherence choices.
Source compatibility forces each load to read its input's unique initialization
write, so the completed result is the desired sum. This premise is an actual
memory source constraint; it does not assume the output is correct.
`witness_valid` constructs compatible source and coherence choices for every
input. `candidate_eq_concrete` equates the grounded candidate with the concrete
interpreter run, and `witness_events_from_run` connects the labels to that run.
`constructive_execution` packages the halted derivation, final memory and graph
witness.

This is a checked bridge for the specified lane, not a generic proof that
`Graph.Valid` suffices for every dependent PTX program. The loop currently has
the sequential correctness/existence result described above; a corresponding
general trace-to-memory refinement is still a separate obligation.

For the shared-allocation example,
[`SharedVectorMemory.verified_shared_execution`](../../Ptx/SharedVectorMemory.lean)
packages a completed instruction execution, correct outputs, a valid relational
graph, and equality between that graph's program labels and the actual per-lane
execution traces. `candidate_output` separately establishes the sum for every
source-compatible graph in the fixed candidate family. Input/output separation
grounds those reads in initialization; neither theorem supplies general
no-thin-air semantics for dependent concurrent programs.

## Consequential choices

The old message-passing semantics and theorems are retained unchanged. The new
scoped relations have an exact all-in-scope specialization theorem; they do not
silently redefine an established predicate to make a new example pass.

The scalar machine uses a concrete word list and fixed-width pointers because
this supports executable proofs without an allocator, byte heaps or generic
address-window machinery. Its instruction set is deliberately small. A typed
mnemonic decoder establishes a useful explicit syntax boundary without the
large unrelated task of parsing complete PTX modules. Stores in supported PTX
text require register data; internal immediate stores are not disguised as
legal assembly. Unsupported opcodes cannot disappear behind a false guard.

Dynamic occurrences record executed instructions, register reads/writes and
memory effects. Those records expose dependencies for inspection; they are not
a proof that a particular syntactic dependency analysis captures PTX's semantic
no-thin-air clause.

## Exact remaining semantic obligations

The following obligations remain after the shared-allocation and bytewise
extensions; their checked examples do not establish a general PTX execution model:

- **Dependent concurrent execution.** PTX permits some cyclic reads-from and
  dependency patterns, including grounded zero-valued cycles, and allows semantic
  reasoning to eliminate apparent dependencies. A blanket acyclicity test would
  exclude permitted behavior. The remaining task is to give a justified account
  of no-thin-air for dependent local candidates, connect the complete memory
  constraints to them, and prove the intended adequacy/refinement results.
- **Observation order for torn reads.** Byte-level sources and qualified
  single-copy atomicity are implemented for aligned `u32` accesses. The torn
  witness and its scope-based rejection are proved under both `anyByte` and
  `wholeSource` observation policies. The unresolved question is which
  interpretation matches the manual's observation-order wording for mixed-source
  reads. These relaxed examples do not settle that source-fidelity question.
- **Broader memory coverage.** Mixed-size partial overlap, aliases, additional
  proxies, and asynchronous accesses remain outside the fragment. Whole-word
  specialization is proved when source identities are uniform; mutual scope
  coverage derives that uniformity in the original restricted fragment. It is
  not an unconditional nontearing guarantee for arbitrary out-of-scope races.
- **Runtime and hardware correspondence.** Allocation and pointer contracts do
  not supply a complete runtime launch/module ABI or hardware-conformance proof.
  A constructed finite schedule establishes execution existence, not scheduling
  fairness or general GPU progress.

Stratic records implemented restricted results separately from the remaining
coverage and interpretation obligations. The sequential and shared-allocation
kernel results, scoped witnesses, and bytewise specialization hold at their
stated levels. Lean checking validates those results against the definitions;
source review must separately justify the definitions' relationship to PTX.

## Reproduce and review

Run `./scripts/check.sh --clean` with the pinned Lean toolchain. It rebuilds the
library, verifies source provenance, rejects proof placeholders/unchecked proof
evaluation, and audits the listed theorem dependencies. `Ptx/Audit.lean` lists
the public results included in the audit; only standard Lean axioms are allowed.

For review, start with the contracts in `ScalarKernels`, then inspect the
interpreter instructions used by the loop, the allocation bridge, and the source
review's limitations. Continue with `verified_shared_execution` and the byte
study's torn-read example and whole-word specialization. `ScalarExamples`
contains kernel-checked successful and
failing execution cases, including empty input, modular wraparound, insufficient
fuel, misalignment, invalid addresses, guarded accesses, and unsupported syntax.
No hardware execution, external paid model generation, floating point,
asynchronous instructions, TorchLean integration or Gemma implementation is
part of this development.

## Continue with shared allocation

The [shared-vector study](shared-vector.md) develops reusable scalar proof rules
and replaces independent local views with a shared allocation for the vector-add
example. It proves arbitrary-interleaving invariants and exact per-thread trace
correspondence, with an explicit completed execution and relational graph.

## Continue with byte-level sources

The [byte-observation study](byte-memory.md) addresses the non-torn restriction
for fixed aligned `u32` accesses and proves a whole-word specialization. Full
mixed-size and aliasing semantics remain absent. The interpretation of
observation order for torn reads is exposed as two named policies, with the
reported specialization and examples checked under both.
