# Lean representation of the publication fragment

The [publication study](message-passing.md) is implemented in Lean 4.33.0 using
only its bundled libraries. Start with the [study guide](guide.md) for a reading
path and the [source ledger](source-ledger.md) for semantic justification.

## Local execution and global compatibility

`Ptx/Language.lean` defines `Instr`, `Instr.step`, `Step`, `execute`, and `Runs`.
An instruction is a relaxed/acquire load into a register or a relaxed/release
store of an immediate `BitVec 32`. Addresses are constant word indices. Registers
are functions from natural-number identifiers to words. Execution consumes a
candidate value at each instruction position; stores ignore it. A load updates
exactly its destination register. `execute_runs` and `runs_eq_execute` connect
the function to the inductive local execution relation. Every finite instruction
list has a completed local run for each candidate read assignment.

`Ptx/Program.lean` materializes initialization followed by every thread's emitted
events. Each program event records its thread and instruction position. The
finite event index provides identity; list concatenation does **not** impose a
cross-thread execution order. `events_origin`, `load_origin`, `store_origin`, and
`initial_origin` expose the actual instructions and initialization behind the
labels. A candidate cannot supply a different trace or invent a store value.

Read assignments may be globally inconsistent. `Program.graph` adds candidate
read sources and coherence to the generated labels; `Graph.Valid` checks their
memory compatibility. `Program.Admitted` additionally requires arena bounds.
Read-source choices at non-read events are irrelevant. Coherence is a Boolean
relation whose typing, strict order, per-word totality, and initialization order
are separately checked. No global total order is imposed on distinct words.

## Deliberate restrictions

| Choice | Reason and precise boundary |
| --- | --- |
| Immediate stores; constant addresses; straight-line code | Prevent value, address, and control dependency cycles while retaining the weak-memory phenomenon. No branches, polling, arithmetic, register-valued stores, or early termination. |
| `BitVec 32` values | Model the exact u32 bit payload, without silently using unbounded mathematical integers for values. There is no arithmetic or floating-point semantics. |
| Natural-number word indices; `byteAddress i = 4*i` | Give a simple injective address/storage mapping with no pointer overflow. `AccessSafe` proves alignment and arena extent. Raw PTX pointers, allocation, lifetime, virtual aliases, and address translation are not implemented. |
| All accesses global, strong, GPU-scoped, generic-proxy, on one GPU | These are fixed environmental restrictions, not variable labels checked at runtime. Under them, non-initial events at the same word are mutually morally strong. Eligible PTX 9.4 targets for these opcodes are assumed; no target validator exists. |
| One initialization event per word, with no issuing thread | Group the manual's per-byte initial writes. Initialization precedes all other writes at its word in coherence, never receives program order. The normalization's source argument is in the ledger. |
| One word source for each read | Encode non-torn matching u32 accesses. `byteSource` lifts this to a uniform source at all four byte offsets. There is no formal equivalence theorem to a general PTX byte model. |
| Unbounded finite relational paths | Express actual transitive closure without a search-depth cutoff. Witness certificates bound derived paths by an independently checked transitive relation. |

These choices are consequential restrictions of this formalization. They are not
requirements for future full PTX coverage. Unsupported instructions have no
constructor; this is not a parser that accepts them as no-ops. There is no general
undefined-behavior classification. Arena bounds exclude out-of-bounds accesses
from `Admitted`, while raw `Graph.Valid` only describes memory constraints.

## Relations and checked constraints

`Ptx/Memory.lean` gives separate definitions to `po`, `rf`, `observation`,
`releasePattern`, `acquirePattern`, `sync`, `base`, `proxyBase`, `cause`,
`coherence`, `communication`, and `locationEdge`. Patterns cover both a direct
qualified access and the applicable two-access forms; synchronization requires
different endpoint threads and morally strong endpoints.

`base` is the nonempty transitive closure of program order and synchronization.
`proxyBase` keeps its same-address endpoints under identity addressing and the
generic proxy. `cause` is exactly `proxyBase` or observation followed by
`proxyBase`. It is not transitively closed again.

`Graph.Valid` checks read-source compatibility, well-formed coherence, acyclic
base order, the coherence axiom, both causality exclusions, and acyclicity of
overlapping program order plus morally strong communication. Fence-SC and RMW
rules have no syntax instances. Single-copy behavior is represented by one word
source. Literal stores, independent control, and constant addresses exclude the
dependency cycles relevant to no-thin-air here. `no_invented_values` proves value
grounding; it is not a general no-thin-air theorem. The ledger makes these
interpretations explicit rather than hiding them in a validity premise.

`Certificate` is a sufficient proof device, not a changed execution semantics.
Its `upper` relation contains each actual base edge and is transitive and
irreflexive. Its natural-number rank increases on every per-location edge.
`valid_of_certificate` proves that these finite obligations establish the
path-based constraints in `Valid`. Certificates also check source, coherence,
and both causality obligations. They do not take publication as an input.

## Results and their quantifiers

`Ptx/MessagePassing.lean` constructs the two-thread program and derives its six
events by local execution. `publication_observed` quantifies over every candidate
read assignment, source map, and coherence relation satisfying `Valid`: if the
final consumer flag register is 1, its final payload register is 7.

`successful_execution_exists` supplies an admitted acquire execution with result
(1,7). `relaxed_counterexample_exists` supplies an admitted relaxed execution
with result (1,0). `acquire_stale_impossible` excludes (1,0) for *every* source and
coherence choice in the acquire variant. `memory_safe` proves alignment and
arena bounds even for candidates rejected by the memory constraints;
`objects_disjoint` proves the word footprints do not overlap.

`Program.all_threads_run` and `local_completion` establish finite local execution
for exactly the oracles used to create the graph. Combined with the existential
admission results, this gives complete consistent candidates, not merely
hand-drawn memory graphs. There is no theorem that a hardware scheduler realizes
these candidates, no fairness model, and no eventual observation of flag 1.

## Proof checking and semantic fidelity

The implementation has completed proofs with no placeholders or custom axioms.
The witness checks use ordinary `decide`, whose generated proof is checked by
the kernel; they do not use native evaluation. `Ptx/Audit.lean` and the check
script report and constrain theorem dependencies.

Those facts establish correctness relative to these definitions. Fidelity to
NVIDIA's prose additionally relies on the source ledger, restriction arguments,
and independent semantic review. This work provides neither full PTX coverage
nor hardware conformance nor a formal refinement from a separate complete PTX
model. Future generalization must revisit byte mixing, initialization, scopes,
proxies, dependencies, target restrictions, and partial/infinite executions.

## Exact finite checking and additional examples

`Ptx/Reachability.lean` proves a finite nonempty-reachability algorithm equivalent
to `Path`. `Ptx/Checker.lean` then proves `Graph.check` equivalent to the unchanged
`Graph.Valid` predicate for every finite graph. This supports concrete witnesses
without a hand-written upper relation or rank certificate. It does not enumerate
program executions or discharge arena bounds.

`Ptx/MessagePassingOutcomes.lean` classifies the entire acquire and relaxed
outcome sets, including exclusion of arbitrary other word values.
`Ptx/Litmus.lean` supplies store-buffering, same-location, paired-release, and
paired-acquire examples. The [finite-checking guide](finite-checking.md) explains
the algorithm, proof boundaries, and the distinct source rules exercised.
