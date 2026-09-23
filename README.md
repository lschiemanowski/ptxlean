# PTXLean

A Lean formalization of PTX ISA 9.4 and reusable foundations for neural-network
kernel verification. **Full ISA coverage and the complete network/kernel
interface remain unfinished.**

Start with the [Stratic project description](stratic/descriptions/root.md).
It explains the responsibilities, contracts and current restrictions. The
[study guides](docs/foundations/guide.md) add worked examples and proof walkthroughs.

Current checked foundations include:

- Whole-word and byte-level memory observations, scoped ordering, message passing
  and finite candidate checking. The interpretation of mixed-source observations
  remains explicitly unresolved.
- Scalar integer execution, predication, branches, reusable proof rules and
  kernels operating on a shared allocation. A shared allocation here does not
  mean PTX's distinct `.shared` storage space.
- [Computed-data publication](docs/foundations/computed-publication.md): actual
  loads, addition and register stores connected to release/acquire communication,
  with universal result, restricted execution witnesses and safety proofs.
- A [recorded Luna workflow](docs/formalization/worker-runs.md), source-section
  inventory, fresh patch replay and independent semantic checks. Its first
  accepted instruction forms include `min.u32`, `max.u32`, `clz.b32` and
  `popc.b32`; these are small
  exploratory results, not evidence of full-ISA productivity.
- [Shared-memory barrier publication](docs/foundations/shared-barrier.md): actual
  `.shared` instructions, waiting and completion, universal results for completed
  schedules, a finite execution witness and a two-warp instance.
- An [actual pinned TorchLean graph](integration/torchlean/README.md) with a
  proved forward formula, automatic backward success and mathematical VJP
  correctness. Numerical accuracy and separately supplied PTX forward/backward
  correspondence remain separate obligations. A [tensor-layout bridge](docs/foundations/tensor-layout-bridge.md)
  connects actual unsigned vector-add execution to TorchLean tensors, with an
  exact-real corollary when input sums do not overflow.

Run the core checks with the toolchain installed through Elan:

```sh
./scripts/check.sh --clean
```

The core and TorchLean integration pin Lean 4.34.0. The core has no external Lean
packages; the integration depends on the actual core package and pinned upstream
TorchLean packages. See its README for reproduction and the distinction between
joint library use and a proved kernel/network correspondence.

The [source ledger](docs/foundations/source-ledger.md) distinguishes checked
proofs from interpretation of NVIDIA's documented semantics. Neither the current
fragments nor the TorchLean example establish hardware conformance, general GPU
progress, complete numerical verification, or a Gemma implementation.
