# Proposed Lean representation for the publication example

This is a design proposal for review. Names below are schematic; no Lean types,
semantics, or proofs have been implemented. The proposal is driven by the
[publication study](message-passing.md) and the
[pinned PTX source](../../references/nvidia/ptx-isa-9.4/README.md).

## Two connected descriptions of execution

Use local operational derivations to explain each thread's executed instructions,
register changes, and emitted effects. Use a candidate execution to assign
memory-read sources and express global constraints on the resulting events.

Neither side may be independently fabricated. A candidate includes enough
evidence to check that the chosen read values produce the local traces claimed
for the program. Conversely, the local trace must account for the events in the
candidate. This circular constraint is a consistency problem, not an instruction
to let a sequential interpreter choose globally visible memory contents.

For the publication fragment, control flow is straight-line and both stores
have constant operands. This keeps read-dependent execution simple without
removing the need to represent it in the eventual general interface.

## Proposed objects

| Concept | Proposed role | Obligation exposed by this example |
| --- | --- | --- |
| Target/environment | ISA version, target features, thread topology, and memory mapping | Selected instructions are legal; GPU scopes include both threads. |
| Program | Parsed/validated instructions with typed operands and qualifiers | The two programs differ at C's memory-order qualifier only. |
| Thread state | Registers, predicates, control position, and call state | C and D place the chosen values in the correct registers. |
| Event identity | A dynamic occurrence, distinct from source instruction identity | Repeated instructions can eventually produce different events; I_p and I_f are initialization events. |
| Event label | Issuer, kind, scope, proxy, addresses, byte footprint, values, and originating instruction | A and D overlap exactly; B and C overlap exactly; other cross-location pairs do not. |
| Local derivation | Evidence connecting instructions, states, and emitted events | Establish A before B and C before D without imposing a cross-thread order. |
| Candidate memory choices | Read sources and write-order witnesses with well-formedness conditions | Represent B-to-C and I_p-to-D even when no sequential interleaving realizes them. |
| Execution validity | Conjunction of local consistency, applicability, and the actual memory constraints | Permit the relaxed counterexample and exclude the acquire counterpart. |
| Observable result | A projection from an admitted execution | Return the pair of final consumer registers without treating arbitrary internal order as observable. |

Choose bit representations for scalar values and byte-addressed footprints at
the boundary to memory. A whole-word read-source map is a derived convenience
for this fragment, not a universal assumption about PTX loads. Its justification
must identify the atomicity and overlap conditions that make a single source
adequate. Do not require a global total order on all writes.

The general representation should carry virtual addressing separately from
underlying storage identity; this example assumes a simple injective mapping.
The exact treatment of aliasing, multimem addresses, and memory beyond the scope
of the documented consistency model needs separate design work.

## Relations must retain their distinct meanings

The proposed interface gives separate names to program order, read-source
communication, observation order, synchronizes-with, base causality,
proxy-preserved base causality, causality, coherence, and communication order.
Each derived relation is defined from its premises, not accepted as an arbitrary
relation supplied by a kernel proof author.

In particular, distinguish base causality from the later causality relation
specified in [section 8.9.5][causality]. A convenience lemma may reduce the latter
to a simpler condition under this fragment's address/proxy assumptions, but the
general definition must retain its full construction. Likewise, reads-from
must not automatically imply synchronizes-with: that error would erase the
relaxed counterexample.

Use small, separately named predicates for the memory axioms so that a proof can
cite the constraint it needs. A predicate called ValidExecution is useful only
when all its constituent conditions are defined and tied to source passages.
An opaque assumption of validity would move the central work into a premise.

## Proposed theorem shapes

These are mathematical obligations, not checked declarations:

```text
Publication:
  for every admitted completed execution of the acquire fragment,
  consumer.flag = 1 implies consumer.value = 7.

SuccessfulExecutionExists:
  an admitted completed execution of the acquire fragment has result (1,7).

RelaxedCounterexampleExists:
  an admitted completed execution of the weakened fragment has result (1,0).

MemorySafety:
  under the stated allocation and legality premises, the fragment's accesses
  stay within their valid storage and satisfy the applicable access conditions.
```

The proof of Publication should be assembled from local trace facts,
source-write identification, synchronization, the payload's causality edge,
and exclusion of the old write. RelaxedCounterexampleExists must supply a
complete finite witness and establish each applicable axiom; failing to prove
Publication for the weakened fragment is not a counterexample proof.

A separate progress theorem would connect an operational execution account to
the admitted candidates. State whether it asserts some completed execution or
completion of every maximal execution under explicit assumptions. Do not claim
the latter from finite trace enumeration or from the absence of a loop alone.

## Guardrails for generalization

- Event issuance and completion need separate identities or relations when
  asynchronous instructions are introduced. Do not force every effect into
  the issuing thread's ordinary program order.
- Collective instructions require participation conditions beyond independent
  scalar thread steps. This fragment supplies no validation of that design.
- Scope and proxy compatibility are derived from labels and topology. They must
  not be replaced by a single universal “synchronized” flag.
- Unsupported instructions, invalid programs, and documented undefined behavior
  must remain distinguishable from valid programs with no constructed witness.
- No-thin-air obligations become more demanding with data-dependent control and
  values. This example avoids such cycles; it does not justify a general
  no-thin-air algorithm or an unrestricted acyclicity substitute.
- Kernel results connect to orchestration through explicit memory/state and
  completion contracts; this study does not provide a CUDA runtime model.

## Decisions still needing review

Decide how to encode local derivations and their coupling to read choices,
which invariants belong in types versus explicit predicates, and whether byte
read sources should be primitive or derived. Also decide the representation of
initialization and unsupported/undefined cases without manufacturing vacuous
success. A treatment of infinite or partial executions is needed before making
general progress claims.

The publication example gives a concrete review test: any proposed design must
admit (1,0) for the relaxed variant, reject it for the acquire variant, and
construct at least one successful acquire execution. Those obligations are
necessary checks of the design, not sufficient evidence of full PTX fidelity.

[causality]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-order
