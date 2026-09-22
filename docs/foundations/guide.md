# Studying the first PTX semantics fragment

Read the [publication experiment](message-passing.md), then follow this guide
with the Lean files open. You need only understand a pair of stores, a pair of
loads, and the difference between a locally executed instruction and a globally
permitted memory result. The [representation account](representation.md) records
why these particular data types were chosen. The [source ledger](source-ledger.md)
connects each memory rule to the pinned PTX 9.4 text.

## 1. Execute one thread

In [`Ptx/Language.lean`](../../Ptx/Language.lean), inspect `Instr.step`.
A load takes a candidate word and updates its destination register; a store
emits its literal word. Neither operation decides which other thread's writes
are visible. `Step` names precisely that transition, and `Runs` composes it
through a finite list. `execute_runs` proves that the interpreter constructs such
a derivation; `runs_eq_execute` proves uniqueness for the same read assignment.

This oracle is a candidate read assignment, not an assumption that any requested
values are physically possible. Its purpose is to separate local instruction
behavior from global memory consistency.

## 2. Build events from actual instructions

In [`Ptx/Program.lean`](../../Ptx/Program.lean), inspect `events` and `graph`.
The arena initialization creates initial events, then each completed local run
creates program events. `events_origin` is exhaustive: every label has an
initialization or a particular thread/instruction behind it. `store_origin`
ensures a read assignment cannot invent a store operand.

`Program.Admitted` combines instruction address bounds with `Graph.Valid`.
A local run may exist even when its memory candidate is rejected. This is why
`all_threads_run` alone would not prove execution existence for the experiment.

## 3. Distinguish the memory relations

In [`Ptx/Memory.lean`](../../Ptx/Memory.lean), read in this order:

1. `po` orders occurrences in one thread. `rf` names the chosen source of a read.
2. `observation` adds the relevant morally-strong conditions to a read-source
   edge. It is still not synchronization by itself.
3. `releasePattern`, `acquirePattern`, and `sync` establish synchronization.
4. `base` closes program order and synchronization transitively. `proxyBase`
   filters same-address endpoints for this fixed proxy/address setting.
5. `cause` follows the precise PTX construction. Do not replace it with `base`.
6. `communication` adds coherence and from-read edges; `locationEdge` selects
   the union constrained by SC-per-location.
7. Read every field of `Valid`. Neither publication nor a final register value
   occurs in its definition.

`Certificate` is a proof tool: an upper relation bounds actual base paths, and a
rank proves per-location acyclicity. `valid_of_certificate` is the soundness
bridge. The upper relation does not replace the semantics and is not used as a
hypothesis in the universal publication theorem.

## 4. Follow the publication proof

In [`Ptx/MessagePassing.lean`](../../Ptx/MessagePassing.lean), `events_eq` derives
six labels from execution: `ip`, `iff`, `a`, `b`, `c`, `d` correspond to I_p, I_f,
A, B, C, D in the study. `publication` follows a short causal argument:

- Source compatibility plus flag value 1 forces C's source to be B.
- B is release, C acquire; their observation establishes synchronization.
- PO A→B, synchronization B→C, and PO C→D create a base path A→D.
- A and D address the same word, so this is the required causality edge.
- `no_stale` and initialization-before-A coherence exclude D reading I_p.
- The only remaining payload write is A, whose literal value is 7.

`result` reads the two *final consumer registers*. `publication_observed` exposes
the useful theorem about that result, with arbitrary candidate values and memory
choices. `acquire_stale_impossible` rules out the bad result independently of
which choices a caller tries.

## 5. Inspect existence separately

`successSource` reads B at C and A at D. `success_valid` checks every finite
certificate obligation. `successful_execution_exists` packages this with arena
bounds and the actual final result (1,7).

`staleSource` reads B at C but initialization at D. Changing only C's qualifier
to relaxed removes the publication synchronization. `stale_valid` checks the
whole candidate, and `relaxed_counterexample_exists` packages the result (1,0).
Its per-location rank orders D before A and B before C. There is no global rank
respecting every cross-location PO/communication edge; requiring one would
wrongly reject this witness.

The finite checks use kernel-checked `decide`. The integer synthesis-size option
only gives Lean room to find nested decision procedures; it adds no assumption
and does not switch to unchecked native evaluation.

## 6. Read exactly what safety and completion mean

`memory_safe` proves all six candidate effects aligned and inside the two-word
arena, regardless of read values or memory validity. `objects_disjoint` proves
the four-byte footprints do not overlap. The generic `Program.admitted_access_safe`
provides the corresponding result for every bounded program in the fragment.
These are mathematical arena properties; allocation, raw pointers, target
validation, and CUDA launch safety remain outside the implementation.

`local_completion` and `all_threads_run` prove completion of finite local
instruction lists for their chosen read values. Global witnesses establish
compatible completed candidates. Neither statement promises GPU scheduling,
eventual completion on hardware, or eventual observation of flag 1.

## Reproduce and inspect

Install the toolchain named by `lean-toolchain` using Elan, then from the project
root run:

```sh
./scripts/check.sh
```

The check builds the pinned Lean library, inspects theorem axioms, and verifies
the pinned source. See the script for exact checks. You can also inspect the
theorem statements and dependency output with:

```sh
lake env lean Ptx/Audit.lean
```

Proof checking establishes these statements relative to the definitions. The
ledger and independent source review support semantic fidelity; they do not
turn this bounded fragment into full PTX coverage or a hardware-conformance
result. No floating point, asynchronous instructions, TorchLean integration,
or Gemma implementation is included.

## Continue with finite checking

The [finite-checking guide](finite-checking.md) explains the exact candidate
checker, the now-complete publication outcome table, and four further litmus
programs. It separates algorithm correctness, outcome completeness, and semantic
fidelity, and shows why multi-instruction synchronization patterns need carefully
chosen examples.

## Continue with environments and scalar kernels

[From litmus programs to scalar kernels](blocks12.md) introduces explicit scopes,
storage contracts, the scalar interpreter and proved integer kernels. It explains
which new pieces have checked bridges, and why dependent concurrent execution
and bytewise raced observations remain separate semantic obligations.
