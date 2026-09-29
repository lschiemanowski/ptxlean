# From cell matrix products to PTX instructions

A cell of the Poisson mesh uses small square matrices. For Q1 through Q4 their
width is two through five. A matrix-product coordinate is a dot product: multiply
one row by one column, then add the products in order. The GPU code gives each
live lane a row and column and writes out the inner loop as a fixed instruction
sequence. This guide covers that local sequence, not the entire cell launch.

## What is proved

[ContractionFetched.fetched_correct](../../integration/torchlean/PoissonPTX/ContractionFetched.lean)
starts from actual fetched instructions and concrete global/shared byte storage.
For every completed block execution it proves that the accumulator—the register
holding the running sum—equals the pinned TorchLean `Spec.matMulSpec` applied to the two byte-backed tensor views.
The environment, including both memories, allocation bounds, base pointers and
row/column registers, is preserved. The theorem covers either accumulator used
by the generator, `%acc` and `%acc2`.

The argument has these initial conditions:

- The program counter starts at the block's actual offset in surrounding code.
- Every selected eight-byte operand has an aligned address inside its allocation.
- Global and shared storage supply the snapshot from which the block reads: the
  byte values present when this local block begins.

The program counter records the next instruction position. Each step fetches
and executes the instruction at that position. A completed run finishes immediately
after the last instruction. The fetched-run lemma derives the full instruction sequence from these counters; it cannot skip
a load or replace the block by a statement that a dot product was computed.
`fetched_exists` independently constructs such a run for every valid snapshot.
This establishes local execution existence, not physical GPU scheduling progress.

The operand tensors are a one-row and a one-column view of the bytes selected
by the emitted row/column/inner-index expressions. They are not hypotheses
asserting the final answer. The address calculation and loads establish their
values. Multiplication and addition round separately using the existing binary64
primitive relation. NaN payloads may vary while decoding to the same logical
Float; bitwise agreement of NaNs is not required. The sum starts at positive zero
and follows increasing inner-index order. No associativity of rounded addition
or substitution of fused multiply-add is used.

## Where the blocks occur

`B` and `D` are the global basis and derivative tables. `S0` through `S6` denote
seven shared matrices. Their contents in this theorem are arbitrary snapshots;
connecting them to prior phases is still a separate obligation.

| Block | Matrix product selected by its addresses | Accumulator |
| --- | --- | --- |
| `bu` | `B S0` | `%acc` |
| `du` | `D S0` | `%acc` |
| `dx` | `S1 Dᵀ` | `%acc` |
| `dy` | `S2 Bᵀ` | `%acc` |
| `bl` | `Bᵀ S3` | `%acc` |
| `dl` | `Dᵀ S4` | `%acc` |
| `x` | `S5 D` | `%acc` |
| `y` | `S6 B` | `%acc2` |

The superscript `ᵀ` swaps a matrix's rows and columns. For example, `dx` loads
`S1[i,k]` and `D[j,k]`, rather than `D[k,j]`. The same eight blocks occur in the
probe, search-direction and solution operator kernels.

[ContractionLoads](../../integration/torchlean/PoissonPTX/ContractionLoads.lean)
models each two-instruction row-major index calculation, widened byte offset,
base addition, and actual load. Global operands use the arena base and a table
offset; shared operands use the shared base and an immediate plane offset.
[ContractionLayout](../../integration/torchlean/PoissonPTX/ContractionLayout.lean)
proves that in-range row/column operands and complete allocated matrices supply
the bounds, alignment and nonwrapping conditions for widths at most five.
`mul.lo.u32` and `add.u32` themselves remain modular operations: their definitions
do not assume that indices are in range.

[Contraction](../../integration/torchlean/PoissonPTX/Contraction.lean) composes
these loads with separate multiply/add steps and proves the exact left-to-right
fold. The result holds for every permitted arithmetic result encoding, while
the executable interpreter supplies canonical witnesses.

## What remains outside this result

Ordinary PTX global/shared loads are weak accesses. The concrete snapshot used
here is a local instruction contract, not a general parallel memory model.
The full cell proof must establish which bytes the gather and earlier phase
stores provide, and why `bar.sync 0` makes those bytes available to later phases.
There is no premise that a previous phase already computes its matrix formula.

The entry's lane-control branches, initial gather, weight multiplications, final
addition and output store remain outside these block proofs. The shared stores
and their publication algebra are covered below, separately from barrier visibility. Neither the launch itself nor the assembled operator `A x` is proved by
this step. The [ordered cell calculation](../../integration/torchlean/PoissonQuadCorrespondence.lean)
and [whole-solver residual certificate](poisson-correspondence.md) retain their
separate scopes.

## Source and reproducibility

The interpretation was reviewed against the locally pinned PTX ISA 9.4 document
with SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`:
integer `mul` and `add`, floating-point `mul` and `add`, and memory `ld`.
Low-word integer arithmetic discards high bits. Explicit `.rn.f64` selects
nearest-even rounding, supports subnormals and preserves the separate arithmetic
operations. `ld.shared` selects the current thread block's shared state space;
these weak accesses need synchronization supplied elsewhere. The supported
binary64 arithmetic forms require at least `sm_13`; the saved backend targets
`sm_120`. No vendor text is distributed in this guide.

Run the proof and dependency checks from the repository root:

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_poisson_contractions.py'
```

To compare saved emitted PTX with the same program consumed by the theorem:

```sh
python3 hardware/check_poisson_contractions.py \
  --run .hardware-runs/poisson-certified \
  --output /tmp/poisson-contractions-check.json
```

Use a new output path. The run directory is a locally saved validation run, not
required for the Lean proofs. The checker verifies artifact hashes, the pinned
dependencies and toolchain, then builds and audits the contraction endpoints.
It compares every instruction of all eight blocks in each of the three element
entries. The receipt records this selected-block scope; it does not certify
surrounding instructions, the compiler, or GPU conformance. Tests reject changed
rounding, operands, indices, shared offsets and accumulator initialization.
Kernel-checked examples exercise both accumulators, a nonzero matrix row,
invalid accesses, modular index arithmetic and cancellation-sensitive ordering.

## From an accumulator to a shared plane

A plane is one square matrix held in the thread block's shared memory. The
kernel reserves seven planes. For a matrix of width `m`, lane `i*m+j` owns entry
`(i,j)`. Its store address is `sharedBase + (plane*m*m + lane)*8`.

`PoissonPTX/SharedStore.lean` proves the three actual store instructions: widen
the lane number and multiply by eight, add the shared base, then store the source
register at the plane offset. Its bounds theorem uses `m ≤ 5`, an active lane,
and a seven-plane allocation with aligned, nonwrapping addresses. Only address
scratch registers change. The source cannot be one of those scratch registers;
a checked example demonstrates why that restriction matters. Raw stores preserve
all bits, including NaN payloads.

The contraction/store theorem composes the matrix calculation with that store.
It derives the stored scalar from the byte-backed TorchLean matrix product and
provides a completed execution witness. This directly applies to the adjacent
`bu`, `du`, `bl`, and `dl` blocks. The `dx` and `dy` blocks additionally multiply
by a weight before storing; `CellMiddleCorrespondence` now includes that
operation in its whole-middle-slice proof.
The final `x` and `y` contractions feed an addition and a global output store.

`PoissonPTX/SharedPlane.lean` combines the words recovered from completed stores.
Different lanes and different planes occupy disjoint bytes, so every complete
publication order gives the same entire memory, including unchanged bytes outside
the plane. Its contraction theorem derives every published coordinate from an
actual contraction/store execution. The later-load lemma explains how a
row-major matrix operand reads its producer's word from this constructed snapshot.
It does not assert that an arbitrary concurrent load observes the snapshot.

The reusable fetched barrier model now proves arrival provenance, waiting, reuse
and the single-writer byte-source visibility rule. Its full-cell instantiation
still must establish the executed stores before arrival, the complete access
coverage, and the subsequent reads for every phase. The three middle phases
now have this instantiation and numerical composition. The final body has a
separate fetched proof and phase-by-phase composition; gather and a single
concurrent trace through final reads remain outside that result. See the
[barrier visibility guide](poisson-barrier-visibility.md).
The plain `st.shared.f64` instruction is weak by default; publication algebra
alone must not silently supply synchronization. The source review used the pinned
PTX 9.4 sections on `st` and `bar` (same manual hash as above): `bar.sync 0` uses
the aligned, whole-thread-block form, and its completion orders prior accesses
against later accesses of its participants. Those facts underlie the explicit necessary source constraint;
complete PTX admission and full-cell control/data composition remain open.

The binding checker now compares all seven shared-store blocks as well as the
eight contraction blocks in each of the three element entries. It checks the
exact proved instruction lists on all 30 saved layouts and requires the four
unweighted contraction/store pairs to be adjacent. It now also checks the five
guards and four barrier boundaries syntactically. This does not prove their
complete launch. The middle-body binding additionally checks every instruction
against the program used by the completed middle-slice numerical theorem.

## Completing the final arithmetic and store

The final `x` and `y` contractions are now composed with their addition,
element/lane indexing, global store and return. The proof establishes the actual
stored value, preserves unrelated bytes and supplies a completed execution for
valid snapshots. A second theorem constructs those bytes from actual middle-run
stores and obtains the whole TorchLean local cell result. See the
[final-output guide](poisson-final-output.md) for its entry conditions and the
remaining distinction between this phase-by-phase composition and one concurrent
whole-cell trace. The frontend checks the entire final body, not just `x` and `y`.
