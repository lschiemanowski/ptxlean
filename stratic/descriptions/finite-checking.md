# Finite execution checking

The checker takes one finite proposed memory graph: nodes record reads and
writes, and directed edges describe relations between them. It returns whether
the graph satisfies the restricted memory-validity rules. These check each read's
source, the ordering of writes, causality, and the absence of forbidden cycles
(paths returning to their starting node). The result agrees exactly with the
existing mathematical definition. It does not establish that an instruction
program generated those events, prove allocation bounds, or search every
execution of a program.

Reachability asks whether following edges can get from one node to another.
Here a path must contain at least one edge: a node reaches itself only if there
is a cycle, not by an empty path. The algorithm adds paths through one possible
intermediate node at a time, a recurrence called vertex elimination. It handles
empty graphs, edges from a node to itself, and longer cycles without extra
assumptions or a path-length cutoff. It terminates because there are finitely
many intermediate nodes; correctness does not assume an unproved speed bound.

For a concrete candidate, Lean's trusted proof checker can verify evaluation of
the algorithm. Soundness means every accepted graph satisfies the rules;
completeness means every graph satisfying the rules is accepted. Rejection
therefore cannot arise from an extra algorithmic restriction. Regression examples
check the treatment of nonempty paths, invalid source choices, inconsistent
write ordering, and cycles.

Agreement between the algorithm and memory rules is distinct from classifying
all outcomes of a particular program. Both are distinct from showing that the
rules faithfully represent PTX. The explanation keeps these claims, the fragment's
restrictions, and unresolved source interpretations separate.
