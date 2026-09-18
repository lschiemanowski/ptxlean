# Finite execution checking

The checker decides the restricted memory-validity predicate for every finite
candidate graph. Acceptance and rejection agree with the existing relational
definition, including source compatibility, coherence, base-order acyclicity,
causality constraints, and per-location acyclicity. It does not replace program
materialization or allocation bounds, or search all executions of a program.

Nonempty reachability preserves exactly the paths of the supplied edge relation.
Empty graphs, self-loops, and longer cycles require no extra assumptions or
path-length cutoff. Vertex elimination provides a terminating finite algorithm;
its correctness does not depend on an unproved performance bound.

Concrete candidates can establish validity through kernel-checked evaluation of
the checker and its soundness theorem. Completeness ensures rejection cannot
come from an extra algorithmic restriction. Regression examples distinguish
nonempty paths from reflexive reachability and exercise malformed sources,
coherence, and cyclic ordering.

The explanation separates algorithmic equivalence, outcome completeness, and
fidelity to the documented PTX semantics. Existing fragment restrictions and
source-interpretation obligations remain explicit.
