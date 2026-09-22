# PTXLean

A Lean formalization of PTX and reusable foundations for neural-network kernel
verification. The project targets PTX ISA 9.4; **full ISA coverage is not yet
implemented**.

The first completed fragment proves publication between two threads, constructs
a successful execution and a relaxed stale-read counterexample, and establishes
aligned arena access safety. It covers only straight-line immediate u32 stores
and register loads, with fixed global/GPU/generic-proxy restrictions.

An exact finite candidate checker, complete message-passing outcome table, and
additional memory-order litmus proofs support the same restricted fragment.

The next foundation adds explicit topology, allocation/access contracts,
non-torn scoped-memory candidates, and a scalar machine with register operands,
predication, branches and bounded loops. A modular-add lane and array-summing
loop have completed execution, correctness and safety proofs. See
[from litmus programs to scalar kernels](docs/foundations/blocks12.md) for the
checked connections and the remaining dependent-concurrency and bytewise-race
semantics obligations.

Start with the [foundations study guide](docs/foundations/guide.md), then
[finite checking and litmus examples](docs/foundations/finite-checking.md). The
[source ledger](docs/foundations/source-ledger.md) distinguishes checked proofs
from the interpretation of NVIDIA's documented semantics. This release state
makes no hardware-conformance or general GPU-progress claim.

With the toolchain in `lean-toolchain` installed through Elan:

```sh
./scripts/check.sh
```

Lean 4.33.0 is pinned; there are no external Lean package dependencies.
[Stratic descriptions](stratic/descriptions/root.md) record the larger intended
responsibilities and their implementation status. TorchLean integration,
numerical verification, and Gemma examples remain unimplemented.

The [shared-allocation vector-add study](docs/foundations/shared-vector.md)
adds reusable proof rules, arbitrary instruction interleavings over one memory
allocation, and a checked connection from completed shared traces to a valid
relational graph.
