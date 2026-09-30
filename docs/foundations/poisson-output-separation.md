# Output stores while other threads are still reading

A fast thread can finish its two final products and write its result while a
slower thread is still loading coefficients. We cannot justify that situation
by assuming another barrier. Instead, the proof must show that the output store
cannot affect any of the slower thread's input bytes.

This is a prerequisite for the complete concurrent output-tail theorem. It does
not yet integrate the tail's integer index, store and return with every other
thread's arithmetic transitions.

## Two separate questions

The proof answers two questions:

1. **Which bytes can the instructions touch?** The arithmetic reads global tables
   B, D and W. The output tail writes a separate element-result array. The actual
   integer calculations, allocation layout and no-wrap bounds must establish
   that separation.
2. **Does removing output stores preserve the memory account?** The arithmetic
   proof can then examine the retained read/store/barrier events. Its byte-source
   choices must still refer to the same actual stores after event positions are
   renumbered.

The first is about addresses. The second is about the meaning of an execution
history. Neither is an assumption about the numerical answer.

## Actual instruction addresses

For width `m`, each coefficient table contains `m*m*8` bytes. The generated layout
puts 32 guard bytes between B and D, and between D and W. The exclusive end of the
coefficient region, relative to the global base, is therefore

```
2 * (m*m*8 + 32) + m*m*8
```

[CellCoefficientProgram](../../integration/torchlean/PoissonPTX/CellCoefficientProgram.lean)
checks every global load in every active lane for Q1–Q4. It follows the symbolic
address calculations while discarding loaded values.
[read_bounds](../../integration/torchlean/PoissonPTX/CellCoefficientReads.lean)
connects that finite certificate to actual fetched concurrent loads. All eight
bytes of each global read lie inside the coefficient region. The base plus this
region's length must fit within the 64-bit address space.

The output address is computed from `cell*m*m + lane`, widened and multiplied by
eight, then added to the global base and output-array offset.
[after_coefficients](../../integration/torchlean/PoissonPTX/CellOutputSeparation.lean)
uses the existing proofs of these actual instructions to place the output word
at or beyond the coefficient region's end. It requires the index to fit in 32
bits and the final byte-address calculation not to wrap. Without those bounds,
modular arithmetic can alias a different location.

The same module proves that the fetched index/store/return tail preserves every
coefficient byte, whatever bit pattern it writes. Distinct bounded indices give
disjoint eight-byte output words. Establishing unique writer ownership from a
complete concurrent run is still a separate obligation.

The saved-layout checker rejects output extents that overlap B, D or W and records
the coefficient end, output start/end and word count in each binding receipt.
This checks concrete layout inputs; it does not verify the Python allocator.

## Keep the original byte sources

[ConcurrentProjection](../../integration/torchlean/PoissonPTX/ConcurrentProjection.lean)
represents the retained history by a strictly increasing map from retained event
positions to original positions. The events themselves must match at those
positions. Position identity matters: two stores with equal values are still
different executed occurrences.

For every retained read byte, the source transformation keeps initialization or
renames its actual store position. If that store had been omitted, compatibility
would say it covers the read byte, contradicting the separation proof. Thus the
store exists at a retained position and its byte value is unchanged.

A retained writer, arrival, barrier completion and reader also keep their order.
The original rule excluding initial bytes after publication therefore still
holds in the retained history. The inverse position map uses Lean's standard
classical choice; this is a logical theorem, not an executable trace-rewriting
utility or an additional arithmetic axiom.

This argument permits removed stores anywhere in the history, including between
a producer and its consumer. It does not depend on a chosen thread schedule or
assume that the stores occur only after all reads.

## What the combined theorem does and does not establish

`projected_arithmetic` combines these facts with the existing TorchLean local-cell
correspondence. Its explicit inputs include an actual retained arithmetic run,
its ordered embedding into the larger history, and the omitted stores' address
bounds. The larger history must satisfy the necessary byte-source constraints.

The [combined concurrent execution](poisson-concurrent-output.md) now derives
the arithmetic run, event embedding, omitted-store classification and result
register relation. The remaining connection is to derive actual output-store
address bounds from launch registers and recover the final stored tensor from
that same run. Complete PTX memory admission, prologue/gather, launch composition
and general execution existence retain their existing boundaries.

## Checks

[ProjectionChecks](../../integration/torchlean/PoissonPTX/ProjectionChecks.lean)
constructs histories with output stores before and between retained events. It
checks compatibility, barrier publication and the renaming of a shared producer
from position one to position zero. A mutation overlapping a read by one byte
is rejected. These are source-transformation checks, not whole-kernel execution
witnesses. The existing source-constrained Q1 execution remains in the suite.

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_*.py'
```
