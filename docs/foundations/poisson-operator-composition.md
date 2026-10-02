# From cell outputs to the assembled operator

The element kernel computes a small matrix for each mesh cell. Assembly then
adds the contributions belonging to each mesh node. A proof of this connection
must retain the order of additions: binary64 addition is rounded, so regrouping
a sum can change its value.

For example, a connectivity scan may encounter the pairs
`(node 0, slot 0), (node 1, slot 1), (node 0, slot 2)`.
Appending each slot to its node's list produces `[0,2]` for node zero and `[1]`
for node one. The proof in
[AssemblyTableConstruction](../../integration/torchlean/PoissonPTX/AssemblyTableConstruction.lean)
shows that this append procedure equals filtering the original encounter list.
It neither sorts indices nor rearranges contributions within a node.

The host stores these lists consecutively, as `[0,2,1]`, and records offsets
`[0,2,3]`. A node reads its own offset and the next one, then follows that slice
of the entry array. The
[compressed-row reconstruction proof](../../integration/torchlean/PoissonPTX/AssemblyCompressedRows.lean)
recovers the original list, including empty rows and repeated indices.
[Input representation](../../integration/torchlean/PoissonPTX/AssemblyRowRepresentation.lean)
connects this result to the actual four-byte words in memory. The finite
[table checker](../../integration/torchlean/PoissonPTX/AssemblyTableCheck.lean)
has a soundness theorem: successful checking supplies this input contract.
Checking only that indices are in bounds would be insufficient, because an
incorrect permutation can pass that weaker test.

Each cell execution records its input layout, fetched execution, source choices
and completion evidence in
[CellExecution](../../integration/torchlean/PoissonPTX/CellExecution.lean).
There is no expected-result field. The existing whole-entry theorem derives
its TorchLean tensor. The
[padding proof](../../integration/torchlean/PoissonPTX/CellTailPadding.lean)
shows that inactive lanes skip all data accesses and the output store. This
matters across cells: a hypothetical store by a padding lane could land in the
next cell's output region. Actual global stores are instead confined to the
active coordinates of their own cell.

A [cell family](../../integration/torchlean/PoissonPTX/CellFamily.lean) shares one
initial global memory and a contiguous output array. Each member retains its
own actual execution and source evidence. Publishing the members' store
histories in any cell order preserves every cell's proved tensor. The uploaded
assembly tables and boundary flags lie below the cell-output array;
[their preservation](../../integration/torchlean/PoissonPTX/CellFamilyInputs.lean)
follows from the actual store addresses, rather than an assumption that a
kernel leaves its inputs unchanged.

The [composition theorem](../../integration/torchlean/PoissonPTX/CellAssembly.lean)
starts assembly with those published bytes. It uses the checked input tables,
derives assembly's read values from its joint source constraints, and proves
that the published node vector is the TorchLean tensor operator, with optional
boundary masking. The
[mesh adapter](../../integration/torchlean/PoissonPTX/OperatorMesh.lean) takes node
indices from the operator's actual connectivity arrays. It requires their
shape and bounds and the supported equality of quadrature and cell dimensions.

The [nonzero composed example](../../integration/torchlean/PoissonPTX/CellAssemblyChecks.lean)
uses a two-by-two synthetic cell, identity coefficient matrices, unit weights
and unit gathered inputs. Actual cell execution publishes four twos; the checked
row table sends those four entries to one node, whose assembled value is eight.
This exercises nonzero arithmetic, actual byte-source checking and publication.
The coefficients are a synthetic test, not a claim about physical quadrature.

The [array-reference bridge](../../integration/torchlean/PoissonPTX/OperatorArrayCorrespondence.lean)
then connects this tensor operator to the public `Poisson.apply` function that
the executable reference calls. It follows the actual nested loops and rounded
array updates, rather than substituting a new scatter algorithm. The
[direct PTX/reference theorem](../../integration/torchlean/PoissonPTX/CellAssemblyReference.lean)
therefore equates that reference result with the actual unmasked publication.
It requires the reference's normal vector length and finiteness checks.
A cancellation regression distinguishes two encounter orders, and invalid
length and infinity regressions retain the existing error behavior.

The [grid extension](../../integration/torchlean/PoissonPTX/CellGrid.lean)
now schedules actual instructions from different cells in one tagged history.
For example, block zero may store an output, block one may store its output,
and block zero may take another step. Filtering the history by block preserves
its actual instruction order and all barrier records. It is unnecessary to
pretend that one complete block ran before another.

Shared memory needs an extra identity. The numeric shared address 256 in block
zero names different storage from address 256 in block one. A proposed source
that connects these two is rejected even when the stored and loaded words happen
to be equal. Global address 256, in contrast, has one identity across the grid.
The [regressions](../../integration/torchlean/PoissonPTX/CellGridChecks.lean)
check this distinction, interleaved publication, and two actual setup instructions
that update their own blocks independently.

The [admission proof](../../integration/torchlean/PoissonPTX/CellGridAdmission.lean)
first establishes global store addresses without using read-source admission.
All stores lie in the cell-output region. Connectivity reads are below that
region, so admitted connectivity bytes must come from uploaded memory. Their
values then bound the later vector reads, which are also below the output
region. This ordering avoids assuming correct gathered values in order to prove
that they are correct. Shared reads retain their own block and the existing
performed-write requirement across its barriers.

The [grid/assembly theorem](../../integration/torchlean/PoissonPTX/CellGridAssembly.lean)
uses the chronological store publication directly. Other blocks' output slots
are disjoint, and uploaded assembly tables remain unchanged. Its
[reference corollary](../../integration/torchlean/PoissonPTX/CellGridReference.lean)
connects the unmasked result to the public array reference. These theorems assume
a supplied actual grid with the stated input layouts, source constraints and
completed active output lanes; they do not construct an admitted cell grid for
arbitrary inputs or prove termination of every padding lane.

The next-launch byte state remains explicit mathematical publication, not a
proof of CUDA transport or host visibility. General admitted cell execution
existence, the remaining PCG/reduction instructions and the final host/solver
connection remain separate obligations. The table checker is a Lean definition;
its existence alone does not establish that the Python byte serializer or
runtime invokes it correctly.

A [schedule-construction theorem](../../integration/torchlean/PoissonPTX/CellGridSchedule.lean)
removes the need to supply a separate grid schedule when local cell executions
are already available. It runs block zero's instructions, then block one's,
and so on. At every stage, completed blocks retain their final states and
unscheduled blocks retain their initial states. Every projected history equals
the original local history, including barrier arrivals and completions.

[Source lifting](../../integration/torchlean/PoissonPTX/CellGridLiftSources.lean)
adds the source block to each local writer index. This preserves the original
byte equalities and barrier conditions. The resulting
[grid-existence theorem](../../integration/torchlean/PoissonPTX/CellGridExists.lean)
takes supplied admitted local cell executions with common entry arguments;
it assumes neither a grid execution nor expected intermediate results.
The [nonzero regression](../../integration/torchlean/PoissonPTX/CellGridExistsChecks.lean)
constructs this grid and the following assembly launch, whose final value is
eight. It reuses checked cell evidence rather than recomputing the large witness.
Serial scheduling witnesses existence only; the universal correctness theorem
still permits arbitrary admitted instruction interleavings. Constructing local
cell runs for arbitrary inputs remains open.
