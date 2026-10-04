# Why a scalar load sees its input

A single thread can read and later overwrite the same field. Alpha selection,
for example, reads `broken`, computes a new status and stores `broken` again.
The numerical proof must not silently choose the old value for the load.

Consider initial `broken = 0` and this impossible candidate:

```
read broken → 1
write broken ← 1
```

The bytes match if the read points to the later write. Byte matching alone
therefore cannot reject it. PTX's same-thread causality rule excludes that
future write as a source. `Scalar.SourceChecks.future_flag_compatible` and
`future_flag_not_admitted` prove precisely this distinction. The width check
also prevents a four-byte write from supplying a fifth byte.

## From instructions to bytes

`Scalar.Observed` keeps the existing freely chosen candidate loads. It records
both numerical words and status flags in one history. A recorded address comes
from the instruction's actual registers. Stores use the actual source bits.
`Scalar.Sources.publish` applies each recorded write with its actual width.
`Observed.runs_memory` proves that this publication equals the final local
memory; it is not an extra premise about the output.

The code calculates every scalar address with three instructions before its
load or store. `ScalarObservedAddress` proves these calculations.
`ScalarObservedTransfers` identifies the resulting named arena field.
`Chunk` groups these instruction sequences for proof composition; its expansion
is proved equal to the original body, and does not replace the instruction
semantics with a second interpreter.

The checked footprints establish that each read occurs before every write to
the same field. Separate fields have disjoint allocated byte ranges, including
four-byte flags beside eight-byte numerical words. Thus every store that could
supply a read byte would be a later same-field write. The no-future rule rules
out that source, leaving initialization. Earlier stores to different fields
cannot change the bytes. `chunks_replay` reconstructs the sequential execution
from these derived reads; `chunks_entry_replay` includes fetched launch setup
and return.

## What the complete results say

`Start.admitted_publication`, `Alpha.admitted_publication`,
`Beta.admitted_publication`, `Norm.admitted_publication`, and
`RestartFlag.admitted_publication` apply the earlier numerical/status results
to these actual histories. `admitted_exists` in each namespace constructs a
finite candidate execution and compatible sources for arbitrary initial words
in a valid scalar arena. It does not assume a guard result or desired output.

The source contract is a necessary fragment of the pinned PTX 9.4 causality
rules (§§8.9.1, 8.9.5, 8.10.6), for synchronous generic accesses without aliases.
It is deliberately restricted to same-address, same-width future sources;
physical field separation proves that those are the only possible writers in
these kernels. This does not formalize general overlapping mixed-size accesses,
all PTX admission axioms, CUDA transport, GPU progress or hardware conformance.
The full host solver and remaining complete-launch obligations are separate.
