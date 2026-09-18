# Scalar message passing

The fragment gives operational and relational meaning to finite straight-line
programs of immediate u32 stores and register loads over aligned, disjoint global
words. All program accesses use the generic proxy at GPU scope on a single
device. Release and acquire qualifiers, including their multi-instruction
patterns, determine synchronization; reading a write alone does not establish it.

Instruction execution produces the events used by memory validity. Program
order, observation, synchronization, base causality, proxy-preserved base
causality, causality, coherence, and communication retain separate definitions.
Initial word events group byte initialization and precede program writes at the
same location. Read sources and coherence choices must satisfy the restricted
memory constraints; a conclusion about publication is not itself a validity
condition.

The acquire publication program guarantees that observing its flag implies
observing the published payload. A complete successful execution witnesses
non-vacuity. Weakening the consumer's acquire to relaxed admits a complete stale
payload witness. The same instruction-level allocation premises establish safe
aligned accesses for both variants.

Checked proofs expose their logical dependencies. Source correspondence records
explain the restrictions under which whole-word read sources and constant-store
value grounding represent the applicable PTX requirements. There are no fences,
RMW operations, load-dependent stores or addresses, branches, asynchronous
operations, or claims about hardware scheduling in this fragment.

The guide connects source clauses to definitions and proof steps, distinguishes
formal guarantees from semantic interpretation, and gives reproducible checks.
Finite local execution and admitted completed candidates are distinct from a
general progress theorem for GPU executions.

A finite candidate checker accepts exactly the executions satisfying the
restricted memory-validity predicate, including its unbounded path constraints.
The message-passing outcome classification is complete for both acquire and
relaxed consumers. Source-reviewed litmus examples exercise store buffering,
same-location ordering, and multi-instruction synchronization patterns through
admitted executions and universal exclusion results.
