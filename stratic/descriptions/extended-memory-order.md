# Extending memory order

The original whole-word model derives order from each thread's instruction
sequence and release/acquire synchronization. A collective operation can impose
additional order. This reusable layer accepts a relation specifying those extra
edges and builds paths through both original and additional edges. An edge is
an ordering claim between two events, not an assertion about the value of a read.

The validity conditions remain source compatibility, coherence of writes,
acyclic base order, respect for causality, exclusion of future or obsolete read
sources, and acyclic same-location communication. Causality uses the same
restricted construction as the original model: a base path with matching endpoint
addresses, or an observation followed by such a path. Its arbitrary transitive
closure is not substituted for this rule.

Every valid extended graph is valid in the original model. With no extra edges,
the two validity predicates agree. If one set of extra edges includes another,
validity for the larger set implies validity for the smaller set. These results
show that an extension adds constraints without silently dropping old ones.

A latest-write rule identifies a read's source when the chosen write precedes
the read in the extended causality relation and all other compatible writes
precede that write in coherence. It obtains the numerical value only after
identifying the source. Neither the required output value nor visibility of that
value is an input assumption.

A three-event example distinguishes the new constraint: an initial zero, a
write of one, and a read by another thread. Without cross-thread order, both
read sources satisfy the original graph rules. Adding a write-to-read order
edge admits the new value and rejects the initial value. This is an algebraic
check of the extension, not an execution of a barrier instruction.

A completed-phase order certificate can supply the extra relation: a memory
access before a participant's arrival precedes one after a participant's
resumption in that same phase. The combined rules prove a latest write supplies
a later read. If the original base edges also increase the certificate's event
positions, the enlarged base relation is acyclic. Event positions alone do not
establish the other memory constraints.

The extra relation is a reusable mathematical parameter, not an execution
certificate. An application must derive its edges from actual synchronization
and instruction events, establish that the source rules justify them, and
construct a nonempty execution witness. This layer does not implement barriers,
shared-state-space instructions, new byte-size behavior, or a complete semantics
for data-dependent concurrent programs by itself.
