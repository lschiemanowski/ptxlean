# From a completed barrier to memory ordering

A barrier's control execution and its memory consequences answer different
questions. The control layer says who has arrived and when waiting threads may
continue. The memory layer says which writes a later read may observe. The
ordering projection in `Ptx/CollectiveOrder.lean` connects the shapes of those two
accounts without assuming a read's value.

Consider a producer that stores a word before a barrier and a consumer that reads
it after the same use of that barrier. The structural path is:

```
producer store → producer arrival → completion → consumer resumption → consumer load
```

An illustrative set of positions is 0, 1, 2, 3, 4. A real machine step may emit an
arrival and completion together; multiplying step indices and allocating small
intermediate positions can still separate their logical roles. The certificate
requires strict order, not a physical clock or a GPU scheduling promise. With
many arrivals, completion must follow every participating arrival. With many
resumptions, each must follow completion.

`Certificate` records ownership, phase participation and these positions. `Phase`
is an abstract type of completed barrier uses, not merely the integer resource
name. An eventual connection to `Barrier.Key` must preserve its CTA, resource,
generation and instruction-site identity. The same resource may be used again,
but a completed earlier generation cannot stand in for a later one.

`Before` checks that the access belongs to the participant and precedes their
arrival. `After` checks ownership and that resumption precedes the access.
`cross` says that both conditions hold for one completed phase, potentially with
different participants. Its definition contains no address or memory value.

`cross_path` expands that edge into the four explicit `Edge` constructors.
`edge_increases` proves each step increases the assigned natural-number position;
`path_increases` extends this fact to every nonempty finite path. A cycle would
make one position strictly less than itself, so `split_acyclic` excludes it. The
same argument gives `projected_acyclic` after removing the intermediate nodes and
combining cross-barrier edges with ordinary edges. The latter proof requires
ordinary edges to increase the *same* positions. Separate acyclicity of two
relations alone would not establish acyclicity of their union.

A certificate does not establish its own instruction origin. To apply these
lemmas to an actual PTX example, the caller still needs to show:

1. Every represented memory event came from the executed instruction, and all
   relevant accesses were included.
2. Arrival, completion and resumption came from the same completed dynamic use,
   with the required full CTA participation, common aligned site and no early
   exits.
3. The assigned positions preserve the actual control ordering, including
   ordinary edges combined with the projection.
4. Shared accesses have genuine shared-state-space labels, valid CTA-owned
   addresses and appropriate instruction qualifiers. For the initial intended
   form, these are matching aligned four-byte, generic-proxy, relaxed CTA-scope
   accesses in one CTA.
5. The memory graph satisfies the independently justified PTX constraints.
   Ordering a store before a load helps rule out obsolete sources; it is not
   itself a proof that no competing write can supply the load.

These obligations are deliberately outside the generic certificate. In
particular, choosing positions based on an assumed desired read value would not
supply the missing execution connection. This module also supplies no new
instruction semantics, execution witness, memory-safety theorem, asynchronous
completion rule or hardware scheduling guarantee.

The source grounding is the completed-barrier synchronization rule in PTX 9.4
§8.9.4, combined with program order (§8.9.1), the base-causality construction
(§8.9.5), and `bar.sync`'s waiting/completion behavior (§9.7.15.1). See the
[pinned-source review](barrier-source-review.md) for the exact scope and source
anchors. Pre/post paths may cross addresses. The later memory account applies
same-address and proxy restrictions where the source specifies them; imposing a
same-address test on each intermediate step would discard useful paths.
