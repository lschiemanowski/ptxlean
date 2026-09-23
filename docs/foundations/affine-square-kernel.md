# Follow a value through two kernels

This example computes the scalar network `(x*weight+bias)^2`. Its purpose is to
connect a real TorchLean graph, rounded instruction executions and persistent
memory across two launches. Each layer proves a different part of that claim.
The authoritative short contract is Stratic's `affine-square-kernel` description.

## Memory and arguments

Reserve an initialized region with five 32-bit words, followed by any extra words:

| Byte offset | Before launch 1 | After launch 1 | After launch 2 |
|---|---|---|---|
| 0 | encoded x | unchanged | unchanged |
| 4 | encoded weight | unchanged | unchanged |
| 8 | encoded bias | unchanged | unchanged |
| 12 | arbitrary old bits | rounded x*weight+bias | unchanged |
| 16 | positive-zero bits | unchanged | rounded intermediate squared, then plus zero |

The first kernel receives offsets `[0,4,8,12]`. The second receives
`[12,12,16,16]`: its two multiplicands name the same intermediate word, and its
bias names its output location. This aliasing is safe because all three loads
precede the store. Extra words are preserved exactly.

Both launches execute the existing seven-instruction affine program: three
`.u32` loads that preserve the input bits, a nearest-even binary32 multiply, a
nearest-even binary32 add, a `.u32` store of the result bits, and explicit exit.
The second add has positive zero as its bias. It remains an actual instruction
with its own rounding contract. These are not fused multiply-add operations.
Each launch starts at PC zero with its own supplied register banks; they need
not contain zero or match the preceding launch's registers.

For x=1.5, weight=2 and bias=0.25, the first launch stores 3.25 (`0x40500000`).
The second stores 10.5625 (`0x41290000`). `two_launch_example` proves this through
actual instruction executions and writebacks, for arbitrary incoming registers.
It does not use an evaluator that substitutes the desired answer.

## What the universal theorem says

`launches_correct` starts from a live allocation with the displayed initial
memory, an eligible ISA/target pair, and two successful serialized launches. It
extracts both actual seven-event traces and exact final states. Their four
arithmetic results must satisfy the original instruction result relations.
`pipeline_correct` exposes the resulting memory contract for a finite chain.
`pipeline_frame` preserves every other allocation.

Those are conditional correctness statements about completed runs.
`pipeline_exists` separately constructs such a chain for every initial bit
pattern, without requiring finite inputs or supplying a desired output.
`pipeline_of_results` is its intermediate construction lemma; the public theorem
discharges that lemma's arithmetic-result premises. Exceptional inputs can
therefore have executions without satisfying the real-valued accuracy theorem.

The serialized layer checks logical allocation identity and device ownership.
Writeback uses exactly the first run's final memory, and the second launch
assembles its state from that saved memory. Releasing the allocation permanently
invalidates its identity, including after later reservations or writes.
`second_launch_after_release_rejected` specializes this guarantee to the consumer.
The [storage](storage-lifetimes.md) and [launch](serialized-launches.md) guides
explain the reusable interfaces.

## Why the error follows the actual output

Let xh, wh and bh be the finite real interpretations of the three encoded input
words. Their differences from ideal x, weight and bias have supplied bounds.
Let A=x*weight+bias and let E be the already-proved affine error budget. Let
R=round(round(xh*wh)+bh), where each round uses nearest-even binary32 semantics.
The first two input-range guards prove that the actual intermediate word is
finite and represents R. This is a conclusion, not a premise about a convenient
intermediate output.

The second pair of guards bounds `|R*R|` and `|R*R|+eps32(R*R)` by the largest
finite binary32 magnitude. They depend only on the initial input values. They
establish finiteness for both second-stage results. The final error budget is

```
eps32(round(R*R)) + eps32(R*R) + 2*|A|*E + E*E
```

The first two terms conservatively account for the second multiply and explicit
zero addition. The remaining terms propagate both copies of the first error;
the quadratic term is retained. `stored_forward_error` applies this theorem to
the result bits actually stored at offset 16 and compares them with the output
of the pinned upstream TorchLean graph. Nonfinite encodings have no invented
real interpretation. The bound is sound but not advertised as a tight estimate
for a large network or as bitwise agreement with PyTorch.

## The automatic backward is a separate result

For an output weight d, TorchLean constructs the exact real backward computation
of this same graph. Its values are `2*d*A*weight`, `2*d*A*x` and `2*d*A`, in input,
weight, bias order. The [VJP guide](affine-square-vjp.md) shows the actual checked
call, success theorem and derivative proof. This example provides a forward
kernel implementation. It does not generate or verify a PTX backward kernel.

## Execution assumptions and reproduction

The model uses initialized whole-word global storage, one thread and one selected
allocation per launch, PTX ISA 9.4 and numeric target sm_70 or later. Work is
serialized with no interfering operations. A real runtime must establish
completion and visibility between launches, translate arguments correctly and
preserve storage lifetimes. PTX thread exit alone does not establish these host
obligations. Each kernel's memory witness uses its entry snapshot; the example
does not claim that these are new physical initialization writes or construct a
combined cross-kernel PTX memory graph. No asynchronous streams, host-pointer
ABI or hardware conformance are proved.

Run `./scripts/check.sh` at the root and `./integration/torchlean/check.sh` for
the pinned joint package. These checks build the actual modules and inspect the
transitive logical dependencies of their public declarations. The independent
review reports distinguish the checked formal contracts from the runtime and
PTX source interpretation boundaries.
