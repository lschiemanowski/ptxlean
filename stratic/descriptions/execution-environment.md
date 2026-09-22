# Execution environment

The environment assigns threads to compute devices, clusters, and CTAs and
interprets scope membership and mutual inclusion. Scope and storage ownership
are distinct: synchronization scope cannot make inaccessible storage accessible.

Addresses identify a state space and storage location. Allocated extents,
alignment, access permissions, initialization, and private or shared ownership
constrain scalar memory accesses. The supported instruction forms carry explicit
ISA-version and target requirements. Unsupported features and illegal uses are
reported distinctly from valid executions with nondeterministic results.

Local execution provides memory events for scoped relational constraints.
Source-reviewed examples establish permitted synchronization within scope and
its absence outside scope. Checked specialization results explain the relation
to the existing global, GPU-scoped message-passing fragment. Interpretive limits,
particularly byte overlap, proxies, and dependent execution, remain explicit.

The scoped relational extension retains whole-word sources. For accesses that are
not mutually in scope, this selects non-torn candidates; it does not enumerate
all bytewise outcomes permitted by PTX. Constructed out-of-scope witnesses and
within-scope publication results retain this distinction.

The scalar arena has a checked embedding into an allocated global-memory view.
Successful emitted accesses satisfy that view's ownership, initialization,
alignment, and full byte-extent contract. This bridge does not by itself supply
concurrent ordering, launch behavior, or a weak-memory refinement.

A byte-level scoped memory model records the source of each observed byte and
the applicable atomicity constraints. Checked relationships identify when a
whole-word representation is justified and distinguish permitted torn reads
from forbidden observations.
