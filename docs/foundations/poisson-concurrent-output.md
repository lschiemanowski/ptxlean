# Concurrent output tails

The middle phases and final arithmetic can now run in one concurrent machine
with the actual output indexing, store and return. A lane may store its answer
and return while another lane is still computing. The proof does not insert a
barrier to make this easier.

The numerical theorem now derives actual output-store addresses from launch
registers and nonwrapping integer bounds. In that same execution, each completed
active lane's stored bytes equal its TorchLean local-cell result. Publishing the
actual store records in any order now yields the complete TorchLean output
tensor once all active lanes have passed their stores.

## One actual machine

[ConcurrentTail](../../integration/torchlean/PoissonPTX/ConcurrentTail.lean)
contains a per-thread program counter, registers, byte memories, predicate and
return flag, together with the shared barrier state. Before the arithmetic
cutoff, it fetches the existing concurrent arithmetic/barrier instructions.
After the cutoff, it fetches the existing integer/store/return instructions.
A returned thread cannot take another step.

The concrete [Poisson program](../../integration/torchlean/PoissonPTX/CellTailProgram.lean)
uses six tail instructions: a 32-bit index calculation, three byte-address
operations, the binary64 global store, and return. The inactive-lane branch
targets that real return, skipping all output operations. Earlier branches
still target their barriers. Kernel-checked certificates cover Q1 through Q4.

This is a composition of existing instruction rules, not a new interpretation of
floating-point arithmetic or a full NVIDIA execution model. Front loads still
choose candidate words; whole-history byte-source constraints justify those
choices. Tail stores update the selected lane's memory and record their actual
address and word in the history. The concrete tail contains no loads. The
generic tail interface alone does not establish coherent cross-thread memory
or full PTX memory admission.

## Deriving the arithmetic execution

The proof constructs a second execution for reasoning. It is not an input to
the actual machine.

* A lane still doing arithmetic has exactly the same state in both executions.
* A lane in its tail has a projected program counter at the arithmetic cutoff.
  Its scratch registers and output bytes may change, but register 11 retains
  the arithmetic result.
* Front steps produce the same recorded events. Tail steps disappear from the
  projected execution, and every omitted event is a global store.
* A barrier release can occur only when all participants are at the same live
  barrier. Consequently it cannot advance an already-returned lane or move
  the projected cutoff forward.

[TailRunProjection](../../integration/torchlean/PoissonPTX/TailRunProjection.lean)
proves this by induction on the actual execution. It constructs an ordered
mapping from each retained event occurrence to its position in the whole
history. Equal-looking events remain distinct occurrences.

The [source-restriction proof](poisson-output-separation.md) then transports the
original byte-source choices into the derived arithmetic execution. It does not
choose unrelated memory values for the two executions.

## Exactly what the numerical theorem says

[CellTailBounds.result_from_launch](../../integration/torchlean/PoissonPTX/CellTailBounds.lean)
takes:

* Q1–Q4 launch registers and gathered initial bytes;
* one actual combined execution;
* launch-only 32-bit index and 64-bit address bounds, with the output offset
  beyond the coefficient tables;
* compatible byte sources and the necessary barrier-publication constraint;
* an active output lane that has reached or passed the arithmetic cutoff.

It concludes that this actual lane's decoded register 11 equals its entry of
the ordered TorchLean local-cell calculation. Other lanes need not have
completed. Neither the answer, a separate arithmetic execution, its event
mapping, nor a last-barrier boundary state is supplied as an assumption.

The companion theorem `stored_from_launch` reaches the actual bytes written
by that lane after its store. It takes the same execution and launch conditions,
with the lane past the store instruction. It does not need a separate tail run
or a fabricated memory snapshot.

## How the address and stored-byte proofs work

[CellTailShape](../../integration/torchlean/PoissonPTX/CellTailShape.lean)
checks that the arithmetic front preserves registers 0, 14 and 15: the base,
lane ID and cell ID. The tail preserves these registers too. Consequently, the
address computed at any later store equals the address determined at launch.

[CellTailAddress](../../integration/torchlean/PoissonPTX/CellTailAddress.lean)
tracks scratch-register facts at each of the four index/address instructions.
At the store, register 2 contains the computed output address. The store's own
byte update establishes the read-after-write result; returning preserves it.
Inactive lanes jump to return, and the stored-value property is required only
for active lanes.

The natural index is `cell * width² + lane`. The launch bounds require it to
fit in 32 bits, and require `base + 8 * index + outputOffset` to fit in 64 bits.
The current interface conservatively checks these arithmetic bounds for all
32 lanes, including padding. It does not require padding output words to be
allocated. The actual store rule checks alignment and allocation.

[CellTailStores](../../integration/torchlean/PoissonPTX/CellTailStores.lean)
locates every actual global store in the combined execution and derives its
address. Together with the output offset, this proves that those stores cannot
overwrite coefficients. [CellTailOwners](../../integration/torchlean/PoissonPTX/CellTailOwners.lean)
also derives disjoint output words for different lanes with a common cell ID.

## From actual stores to one output array

[CellOutputOccurrence](../../integration/torchlean/PoissonPTX/CellOutputOccurrence.lean)
proves that an active lane cannot pass the store instruction without emitting a
global store record. This closes a possible circular argument: the caller does
not hand the proof a list of stores containing the desired answers.
[CellOutputValues](../../integration/torchlean/PoissonPTX/CellOutputValues.lean)
then proves that the recorded word equals the writer's final arithmetic register.

[GlobalPublication](../../integration/torchlean/PoissonPTX/GlobalPublication.lean)
applies recorded global writes to a single byte memory. Other events leave this
memory unchanged. For a chosen output word, each global store either writes the
same word at the same address or touches disjoint bytes. A real matching store
must occur. These facts make the final word independent of the merge order and
of the old output bytes. Outside bytes are preserved.

[CellOutputPublication](../../integration/torchlean/PoissonPTX/CellOutputPublication.lean)
derives these conditions from the combined execution and launch geometry.
[CellOutputTensor.published_tensor](../../integration/torchlean/PoissonPTX/CellOutputTensor.lean)
reads a normal contiguous, row-major array from the merged bytes and proves it
equals the TorchLean local cell result. In addition to the earlier numerical
conditions, it requires a common cell ID and completion past the store for every
active lane. It derives all required stores and their values.

For example, Q1 has four output words at offsets 160, 168, 176 and 184 when the
base and cell ID are zero. Publishing lane three before lane zero is harmless:
their eight-byte words are disjoint. A write starting at offset 161 would not be
harmless merely because 161 differs from 160; it overlaps seven output bytes.

Only the merge order is varied. The byte-source constraints still use the
original execution history, including its barriers. The merge is a mathematical
observation of actual records; it is not a CUDA driver rule establishing when the
host can read the result. Host-visible completion, arbitrary-input termination,
prologue/gather, complete PTX memory admission and hardware conformance remain
separate obligations.

## A completed execution

[CellTailChecks](../../integration/torchlean/PoissonPTX/CellTailChecks.lean)
constructs a Q1 zero-data run with 32 participants. Lane zero stores and returns
before lane one performs its remaining coefficient reads. Exactly four global
stores occur; all 28 padding lanes return without storing. Attempting to step a
returned thread fails.

[CellTailWitnessSources](../../integration/torchlean/PoissonPTX/CellTailWitnessSources.lean)
checks the actual event words, alignment and output addresses, constructs one
whole-history source assignment, and instantiates the numerical theorem.
[CellTailAddressChecks](../../integration/torchlean/PoissonPTX/CellTailAddressChecks.lean)
instantiates the stronger stored-byte theorem using launch conditions alone.
It also executes a tail with nonzero base, cell, lane and stored word, and
rejects mutated bounds with index overflow or byte-address overflow.
[CellPublicationChecks](../../integration/torchlean/PoissonPTX/CellPublicationChecks.lean)
instantiates the whole-tensor theorem, including reversed publication order and
arbitrary old output memory. It also checks a nonzero actual store, coefficient
byte preservation, rejection of missing stores and rejection of overlapping
store words. These are kernel-checked finite witnesses, not GPU measurements or
general termination proofs.

Run the registered proofs, source guards and exact axiom audit with:

```sh
integration/torchlean/check.sh
```


## Establishing the entry state

The [register prologue](poisson-entry.md) now has its own fetched execution and
existence proofs. It derives the addresses, lane/cell IDs and row/column values
from launch context while preserving all memory. It ends before the gather.
Connecting the indexed gather and first barrier to this arithmetic/output proof
still requires their execution and memory-source arguments.
