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

These are compositional execution and mathematical publication results. The
cell family does not yet derive arbitrary grid scheduling from one device-wide
run. The next-launch byte state is explicitly the publication of the preceding
histories; this is not a proof of CUDA transport or host visibility. General
admitted cell execution existence, the remaining PCG/reduction instructions
and the final host/solver connection remain separate obligations. The table
checker is a Lean definition; its existence alone does not establish that the
Python byte serializer or runtime invokes it correctly.
