# Publishing a payload between two threads

This study works out a small instance of the relational PTX foundation. It is a
source-reviewed mathematical argument and a proposed proof target, not a Lean
proof, assembled kernel, hardware experiment, or implementation of PTX semantics.
The [representation proposal](representation.md) explains the resulting design
constraints without committing to concrete Lean declarations.

## The experiment on paper

One producer publishes a payload and a readiness flag. A consumer reads each
once. The desired property is conditional: **if the consumer reads flag 1, its
payload read returns 7**. It is not a claim that the consumer necessarily sees
flag 1.

Use two distinct valid threads on the same GPU, two disjoint four-byte-aligned
global words, one virtual address for each word, and only generic-proxy accesses.
Both words begin at zero. No other thread or host action modifies them. Use PTX
9.4 and an eligible target of `sm_70` or later for this instruction fragment.
All four accesses cover their whole word. These are assumptions of the example,
not proposed restrictions on the full formalization.

The following are per-thread instruction fragments. Register declarations,
thread selection, launch code, and output collection are intentionally absent;
these blocks are not a runnable PTX module.

```text
Producer                                      Consumer
A: st.relaxed.gpu.global.u32 [payload], 7;      C: ld.acquire.gpu.global.u32 %flag, [ready];
B: st.release.gpu.global.u32 [ready], 1;        D: ld.relaxed.gpu.global.u32 %value, [payload];
```

The consumer executes D even if C returns zero. This makes all four outcomes
easy to inspect without introducing a branch or a polling loop. A conditional
consumer could use the result differently; that would be another local trace.

The source anchors for instruction syntax, eligibility, alignment, scopes,
initialization, and memory rules are recorded in the
[frozen source manifest](../../references/nvidia/ptx-isa-9.4/manifest.json).
The relevant instruction sections are [ld][ld] and [st][st]. The use of relaxed
accesses for the payload keeps this example free of weak-access data races;
the failed version below isolates a missing synchronization edge.

## Candidate execution

We propose to describe this example with six event identities. The initial
events are mathematical initialization events, not extra PTX instructions.

| Event | Meaning | Value |
| --- | --- | --- |
| I_p | Initialize payload | 0 |
| I_f | Initialize ready | 0 |
| A | Producer writes payload | 7 |
| B | Producer writes ready | 1 |
| C | Consumer reads ready | chosen from a permitted source write |
| D | Consumer reads payload | chosen from a permitted source write |

The two local program-order edges are A to B and C to D. Keep read results and
their source writes together: for example, assigning C the value 1 means choosing
B as its source in this closed example. The per-location coherence edges are
I_p to A and I_f to B. Distinct addresses do not acquire a common write order
merely because they appear in this table.

For this particular fragment, a read-source map at word granularity is adequate:
the payload write/read and the flag write/read are matching, strong GPU-scope
operations, and each pair overlaps completely. A general PTX representation
must retain byte ranges and the conditions justifying such a whole-word view.

## Why publication works

Assume C returns 1. Because I_f contains 0 and B is the only other write to
ready, C reads B. The selected scopes include both threads, and the accesses
use the same proxy and address. Thus B and C meet the relevant morally-strong
conditions. The release B and acquire C form the synchronization pair. See
[morally strong operations][strong], [release/acquire patterns][patterns],
[observation order][observation], and [synchronization][sync].

Our proof decomposition is:

1. Establish the fragment's legality and its memory-access premises.
2. Recover the read source B from C's result 1.
3. Derive synchronization B to C.
4. Combine A to B, B to C, and C to D into a base-causality path A to D.
5. Establish the proxy/address conditions for A and D, yielding the required
   causality edge between these payload accesses.
6. Exclude I_p as D's source because I_p precedes A in coherence order.
7. Exhaust the remaining writes to payload: D must read A and therefore return 7.

Steps 4 and 5 are deliberately separate. PTX 9.4 distinguishes base causality,
proxy-preserved base causality, and causality; simply naming the transitive
closure of program order and synchronization “causality” would skip a semantic
obligation. The source rules are [causality order][cause-order] and the
[causality axiom][cause-axiom]. The manual's message-passing example in the latter
section uses fences; this study uses direct release/acquire accesses and stronger
payload accesses, so it is a derived example rather than a transcription.

The following table is our derived target for completed executions under the
stated assumptions. The entries are not results of a model checker.

| C returns | D returns | With acquire at C | With relaxed at C |
| --- | --- | --- | --- |
| 0 | 0 | permitted | permitted |
| 0 | 7 | permitted | permitted |
| 1 | 0 | forbidden | permitted |
| 1 | 7 | permitted | permitted |

Simple serialization witnesses explain three rows: C,D,A,B yields (0,0);
A,C,B,D yields (0,7); A,B,C,D yields (1,7). These are existence witnesses only.
The universal publication property comes from the relational argument above,
not from trying all sequential interleavings.

## Removing the consumer's acquire

Change only C to `ld.relaxed.gpu.global.u32 %flag, [ready];`. Retain the producer's
release, the GPU scopes, and all other assumptions. A relaxed read can observe
the flag without providing this acquire pattern. Source-read communication alone
must not be treated as the missing synchronization operation.

Consider the following candidate witness for (1,0):

```text
program order:   A -> B, C -> D
reads from:      B -> C, I_p -> D
coherence:       I_p -> A, I_f -> B
synchronizes:    no producer-to-consumer edge
```

The communication graph contains D to A (reading an older payload value), A to B
in local program order, B to C (reading the flag), and C to D in local program
order. That is a cycle in the union of these relations. It is **not** sufficient
to forbid it by declaring that entire union acyclic: such a rule would impose
an extra global ordering requirement. The [per-location rule][sc-location]
does not compare this entire cross-location cycle.

The source obligations for admitting this witness are reviewed below. This is a
paper check for this finite fragment, not a general decision procedure.

| Obligation | Check for the (1,0) relaxed witness |
| --- | --- |
| Local instruction behavior | Both constants are stored; each load gets its nominated source value; A precedes B and C precedes D locally. |
| Read-source compatibility | Sources address the same complete word as each read; neither value is invented. |
| Coherence | Each initialization is before its unique program write; no conflicting causality edge reverses either pair. |
| Fence-SC | No fence.sc events are present. |
| Atomicity | Each whole-word read uses one source; there is no RMW. |
| No thin air | Store values are constants independent of the loads, and no value is justified by a self-supporting dependency cycle. |
| Per-location consistency | On payload the communication chain is I_p to D to A; on ready it is I_f to B to C. Neither has a contradictory local overlapping-access order. |
| Causality | There is no A-to-D publication edge. Observing B at C does not create a same-address base path from C to D: these read different words. |

Review these checks against [coherence][coherence], [Fence-SC][fence-sc],
[atomicity][atomicity], [no thin air][nta], [per-location consistency][sc-location],
and [causality][cause-axiom]. They motivate an explicit allowed witness as a
future proof obligation; the absence of the positive proof alone would not show
that the bad result is allowed.

## Safety, existence, and progress

Memory safety here requires valid, aligned, initialized storage of sufficient
extent, compatible state spaces, and legal instructions. It does not imply the
publication property: the relaxed counterexample satisfies those premises.

Execution existence asks for a candidate satisfying all applicable constraints.
The serialization witnesses and the relaxed witness above are inputs to that
future construction. A proof that every completed execution has a property must
not substitute for showing that at least one execution exists.

Progress asks whether execution can reach completion. The fragments contain no
loops or explicit waits, but their finiteness alone is not a proof that hardware
will schedule them or complete their accesses. A termination theorem needs an
operational account and stated environment/scheduling assumptions. In particular,
this example proves no eventual observation of flag 1. Replacing C with a spin
loop would introduce a separate progress question.

## What this teaches the representation design

The model needs distinct event identity, local order, read-source choices,
memory footprints, operation strength, scope, and proxy information. It also
needs derived relations whose definitions are not interchangeable. A sequential
interpreter could demonstrate the successful witnesses while missing precisely
the failed behavior this study is meant to expose.

This example does not exercise asynchronous completion, collectives, alias
proxies, overlapping mixed-size accesses, floating point, or multi-kernel
execution. The proposal must leave room for those responsibilities; this small
example cannot validate their design. Its concrete target is the publication
implication and an explicit counterexample after weakening the consumer.

[ld]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld
[st]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st
[strong]: ../../references/nvidia/ptx-isa-9.4/index.html#morally-strong-operations
[patterns]: ../../references/nvidia/ptx-isa-9.4/index.html#release-acquire-patterns
[observation]: ../../references/nvidia/ptx-isa-9.4/index.html#observation-order
[sync]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-synchronization
[cause-order]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-order
[cause-axiom]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-axiom
[coherence]: ../../references/nvidia/ptx-isa-9.4/index.html#coherence-axiom
[fence-sc]: ../../references/nvidia/ptx-isa-9.4/index.html#fence-sc-axiom
[atomicity]: ../../references/nvidia/ptx-isa-9.4/index.html#atomicity-axiom
[nta]: ../../references/nvidia/ptx-isa-9.4/index.html#no-thin-air-axiom
[sc-location]: ../../references/nvidia/ptx-isa-9.4/index.html#sc-per-loc-axiom
