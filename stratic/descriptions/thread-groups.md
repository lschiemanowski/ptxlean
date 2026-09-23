# Thread groups and scopes

A cooperative thread array (CTA) is a group of threads that can cooperate through
shared memory and synchronization. CTAs launched together form a grid. A cluster
groups CTAs within a grid for additional cooperation. These groups belong to a
compute device, here a GPU.

The model identifies each thread by its device, grid, cluster, CTA, and position
within the CTA. This arrangement is called the thread topology. Two threads must
have different complete identities, even if their position numbers within their
own CTAs are equal. CTA identifiers are names within this hierarchy, not raw
hardware register values.

A synchronization operation specifies which participants it can coordinate with.
This set of participants is its scope:

| Scope | Included participants in this model |
| --- | --- |
| CTA | Threads in the same CTA |
| Cluster | Threads in the same cluster |
| GPU | Threads on the same GPU, including other grids |
| System | All represented GPU threads belonging to the host program |

The host is the CPU program that launches GPU work. Its own thread execution is
not represented here. Sharing a scope does not require threads to execute their
instructions at the same time.

For the cross-thread scope condition, both operations must include the other
thread. This is mutual scope inclusion. For example, a writer using GPU scope
includes a reader in another CTA on that GPU. But if the reader uses CTA scope,
it excludes that writer. This pair does not satisfy the condition merely because
the writer chose the wider scope. Other instruction and ordering conditions are
also needed for synchronization.
