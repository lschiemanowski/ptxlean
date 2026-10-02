# One step of the Poisson dot reduction

Each dot kernel assigns inputs to 256 threads. After each thread accumulates
its own products, the kernel places those 256 sums in shared memory. It then
combines pairs at strides 128, 64, 32, 16, 8, 4, 2 and 1. At stride 128, for
example, thread 127 reads words 127 and 255 and replaces word 127 with their
rounded sum. Every thread meets the barrier before the next stage.

This proof covers the six instructions of one active update. The proof for the
complete concurrent reduction is still being built.

```ptx
mul.wide.u32 %off, %lane, 8;
add.u64 %addr, %shared, %off;
ld.shared.f64 %a, [%addr];
ld.shared.f64 %b, [%addr+1024];
add.rn.f64 %acc, %a, %b;
st.shared.f64 [%addr], %acc;
```

The displayed offset is 128 eight-byte words. The Lean instruction list is
parameterized by the offset, so the same proof covers the other stages.

## What the proof says

[ReductionUpdate.lean](../../integration/torchlean/PoissonPTX/ReductionUpdate.lean)
uses the existing byte-addressed instruction semantics. Its `effect` theorem
starts from execution of these instructions and derives both load values and
the exact final state. The stored word decodes to the binary64 sum, rounded to
nearest with ties to even. Permitted NaN result bit patterns remain free; the
proof does not restrict every execution to the canonical executable witness.

`correct` proves the stored decoded value and preserves global memory and
registers outside the five scratch destinations. `preserves_other_bytes`
proves that all shared bytes outside the destination word are unchanged.
`fetched_correct` obtains this result for a block inside an arbitrary surrounding
straight-line program, using actual instruction fetches and endpoint counters.

`fetched_exists` constructs a successful execution when the two accesses are
valid. `valid_of_active` derives those requirements from the actual allocation:
a lane below a stride of at most 128, at least 2048 shared bytes, an eight-byte
aligned base, and an allocation that stays inside the 64-bit address space.
The allocation conditions are memory requirements, not presumed output values.

The [regressions](../../integration/torchlean/PoissonPTX/ReductionUpdateChecks.lean)
check the last active lane of the widest stage, preservation of its neighbor,
rejection of an unaligned address and an address just beyond the allocation,
and a rounded addition. In particular, binary64 cannot represent `2^53 + 1`;
this addition produces `2^53` under round-to-nearest, ties-to-even. No step of
the proof substitutes a real-number sum or reassociates additions.

## Connection to generated PTX

[The binding checker](../../hardware/check_poisson_reduction_updates.py) compiles
the update module, audits the relevant theorem dependencies, and renders that
same instruction list using the existing register mapping. It checks every
local update in all six dot kernels in a saved run. It also checks the adjacent
lane guard and barrier, the order and adjacency of the eight stages, and the
block/shared allocation declarations. Mutation tests exercise rejection of
changes to these parts.

After building the pinned integration dependencies, run:

```sh
python3 hardware/check_poisson_reduction_updates.py \
  --run .hardware-runs/poisson-certified \
  --output /tmp/poisson-reduction-updates.json
python3 -m unittest discover -s hardware -p test_poisson_reduction_updates.py
```

Use a fresh output path. This reads a saved run and does not launch a GPU kernel.
The checker uses a single Lean thread and a 5 GiB Lean allocation limit. The
checks performed during development also ran inside a 6 GiB hard process-group
memory cap, with no swap and no concurrent Lean builds.

## What remains

The local theorem takes a shared-memory byte view. It does **not** prove that
concurrent loads observe that view. The [repeated-write source theorem](poisson-repeated-shared.md)
is available for that next connection, but the actual reduction must still
establish its history and ownership conditions. The input accumulation loop,
all reduction stages, final scalar store and whole-launch existence must also
be connected in order. The binding check does not claim to bind those omitted
parts of the entry or to establish host launch correctness.

These obligations precede the connection of PCG's stopping logic to its exact-real
residual guarantee. This local proof supplies neither full solver correctness
nor complete PTX memory admission or GPU progress.
