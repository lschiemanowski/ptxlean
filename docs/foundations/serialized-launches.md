# From a completed kernel to the next launch

`Ptx.Scalar.Sequential` connects fetched mixed-instruction execution with the
persistent logical storage of `Ptx.SequentialStorage`. It does not assume an
output postcondition and invent a matching execution.

A `Request` identifies one device participant and one live global allocation,
plus a target, a program, memory arguments and a `Seed`. Each `Argument` holds
an allocation identity and a 64-bit byte offset. Every identity must match the
selected allocation. `start` sets PC to zero and fills address registers
`0 .. arity-1` from argument offsets. Value registers, predicates and other
address registers are arbitrary supplied seed banks. `start_argument` and
`start_other` state that binding exactly. No registers are implicitly zeroed or
copied from a previous launch.

`SuccessfulLaunch request before after final trace` packages a live entry cell,
its device-owner check, all argument identities, an actual
`Mixed.Run ... final .halted trace`, and successful writeback of exactly
`final.memory`. It is an existential proposition; `.cell` chooses its uniquely
identified entry cell only as a proof convenience. `.run_from` and
`.writeback_lookup` let a caller use its already-known cell directly.

The run need not access every argument. Consequently argument binding checks
identity, while `environment_safe` derives alignment and bounds for every
memory access actually emitted. `final_environment_safe` retains those checks
after writeback; `environment_unchanged` proves allocation metadata unchanged.
`exact_writeback` retains owner and extent; `other_cell` preserves other
allocations; `word_frame` preserves untouched words inside the selected arena.
There is no global non-aliasing premise. Aliased offsets obey the actual run.

`launch_exists` constructs a successful launch from a proved actual halted run.
It derives the required same-length writeback condition from
`Mixed.Run.memory_length`. It does not promise that arbitrary programs terminate.
`no_launch_absent`, `no_launch_wrong_owner` and `no_launch_wrong_identity` exclude
invalid launches. `no_launch_after_release` applies after any finite valid
storage history, including reservations of replacement allocations. It is not
merely an immediate-after-release check.

`Chain` joins a finite list of launches through their exact intermediate storage.
`Chain.append` joins existing chains; `Chain.two_iff` exposes both actual
launches and their intermediate state. `Chain.invariant` propagates a proved
storage property, while keeping construction of the launches a separate
obligation. `Chain.storage_history` reuses the storage lifetime discipline;
`Chain.old_absent` ensures a previously issued absent identity remains absent.
The chain records no fairness or universal termination property.

A real runtime must wait, publish writes, preserve live storage and exclude
interference to implement this synchronous abstraction. No PTX `exit` theorem
or memory scope is used to infer those conditions. A second kernel's local
initial-memory events describe its entry snapshot, not additional physical
writes in a unified cross-kernel graph. This is one thread and one global arena
per launch, not PTX parameter ABI, streams, asynchronous or overlapping kernels,
or hardware/runtime conformance.

## Checked evidence

Lean source SHA-256: `af66e7fc85bd6f4c4d5fa7fa4cd3eb41beed49dc5e09967a6f0c4d5c6261a10d`.

With the repository's pinned Lean 4.34.0 and dependency manifests:

```
cd integration/torchlean
lake --no-cache build PtxBinary32.Sequential
lake --no-cache env lean PtxBinary32/Sequential.lean
```

The build completed with 2523 jobs. All 32 public named theorems and the
`start`, `SuccessfulLaunch`, and chosen-cell definitions were freshly audited
with `#print axioms` (35 exact reports). Only `propext`, `Classical.choice` and
`Quot.sound` occur. The existing forbidden-token scanner found no `sorry`,
`admit`, new `axiom`, or `native_decide`. The complete reports are in
[serialized-launches-audit.txt](serialized-launches-audit.txt).
These checks establish proof validity for this contract, not runtime fidelity.
