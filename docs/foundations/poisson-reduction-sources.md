# Which shared word does a reduction read?

The [local pair-update proof](poisson-reduction-update.md) explains what six
instructions do with two loaded words. This layer explains why a load must
obtain the intended previous write, even though reduction stages overwrite
the same shared-memory locations.

Each lane owns one eight-byte word. Lane `t` writes at `base + 8*t`.
Two different lanes cannot overlap even one byte. This physical fact matters:
source selection is checked per byte, without assuming an indivisible word read.

## The two reads have different ownership arguments

An active lane first reads **its own word**. Its earlier stores precede the
selected publication in that lane's instruction order. Its current and later
stores follow the read. The store sites of consecutive stages leave no other
store between the selected publication and this read.

It then reads **a neighbor's word**, one stride away. At stride 128, lanes
0–127 read neighbors 128–255. Those neighbors no longer write: the active range
only shrinks in later stages. The neighbor's earlier stores precede its selected
publication in its own instruction order. Its actual barrier arrival and the
common completion place that publication before the reader's load.

Together these facts establish the condition required by the
[repeated-write theorem](poisson-repeated-shared.md): every overlapping store
is the selected write, before that write, or after the read. The necessary
memory rules then force each byte to come from the selected store. The loaded
word is a conclusion, not a supplied arithmetic answer.

[ReductionSources.lean](../../integration/torchlean/PoissonPTX/ReductionSources.lean)
proves the ownership and instruction-order arguments.
[ReductionStageSources.lean](../../integration/torchlean/PoissonPTX/ReductionStageSources.lean)
uses the actual active-range sequence `256,128,64,32,16,8,4,2,1` to derive the
own-word gap and the neighbor's last-write property. Publication sites are
parameters, required to increase. This avoids confusing instruction indices in
a restricted control representation with indices in emitted PTX text.

The generic source lemmas require **store coverage**: every shared store
has the owning lane's address, occurs at a designated publication site, and
comes from a lane active at that stage. The selected publication must also be
shown to occur as an actual event. Read positions and the actual barrier edge
remain explicit obligations for that entry. The [shared-tree control proof](poisson-reduction-control.md) now derives
these premises for the 256-lane shared-tree fragment, including every read
address and preceding publication. Native predicate/branch translation and
the full entry remain separate obligations.

## A checked two-stage execution

The four-lane example uses the same six-instruction update body and the existing
concurrent barrier machine. It begins with four actual shared stores:

| Lane | Initial word | After stride 2 | After stride 1 |
| --- | ---: | ---: | ---: |
| 0 | 1 | 4 | 10 |
| 1 | 2 | 6 | 6 |
| 2 | 3 | 3 | 3 |
| 3 | 4 | 4 | 4 |

Every thread participates in all three barriers: after initial publication and
after each update stage. Inactive lanes skip the arithmetic, not the barrier.
The final read of word zero must select the write of four, even though the
history also contains its initial one and its later overwrite with ten.
The final neighbor read must select six, not its overwritten initial two.

The Lean witness checks all emitted events of this restricted execution and
proves that all four lanes reach the fragment's end. A separate proof supplies
byte-compatible sources for every read and an explicit coherence witness
satisfying the necessary repeated-write rules. Thus the execution and admission
claims coexist; the output theorem is not vacuous. A second checked candidate
reads the overwritten neighbor value two and has byte-compatible sources. The
new ordering rules reject that candidate; mere instruction execution and byte
compatibility would accept it.

The source theorem also treats the final two proposed load words as arbitrary:
for an actual run with this history shape and admitted sources, they must be
four and six, and the final store must be ten. The earlier part of the history
is fixed in this regression and independently checked by its concrete execution.
This is not yet an arbitrary-input or arbitrary-history whole-tree theorem.

Read the implementation in this order:

1. [ReductionTreeWitness.lean](../../integration/torchlean/PoissonPTX/ReductionTreeWitness.lean): program, schedule, actual history and completion.
2. [ReductionTreeSources.lean](../../integration/torchlean/PoissonPTX/ReductionTreeSources.lean): ownership, real barrier edge and universal final-read selection for that history shape.
3. [ReductionTreeAdmission.lean](../../integration/torchlean/PoissonPTX/ReductionTreeAdmission.lean): concrete source witness, composed result and obsolete-neighbor rejection.

## Boundaries

The example uses the existing combined lane-test/branch instruction. It does
not establish the correspondence of the emitted `setp` and predicated branch
instructions, the strided input loop, the final global store, or the entire
256-thread entry. It also begins with given lane sums rather than proving the
input dot products. The eight-stage lemmas supply reusable source reasoning;
the four-lane execution supplies a concrete regression of the mechanism.

The source constraints remain necessary conditions for the restricted shared
memory model, not complete PTX admission. No GPU execution, hardware progress,
CUDA transport or complete PCG residual guarantee is claimed here.
