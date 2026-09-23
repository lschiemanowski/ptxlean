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
  accepted instruction forms are `min.u32` and `max.u32`; this is a small
  exploratory result, not evidence of full-ISA productivity.
- An [actual pinned TorchLean graph](integration/torchlean/README.md) with a
  proved forward formula, automatic backward success and mathematical VJP
  correctness. Numerical accuracy and separately supplied PTX forward/backward
  correspondence remain separate obligations.

Run the core checks with the toolchain installed through Elan:

```sh
./scripts/check.sh --clean
```

The core pins Lean 4.33.0 without external Lean packages. The separate TorchLean
integration pins Lean 4.34.0 and its upstream dependencies; see its README for
reproduction and the current compatibility boundary.

The [source ledger](docs/foundations/source-ledger.md) distinguishes checked
proofs from interpretation of NVIDIA's documented semantics. Neither the current
fragments nor the TorchLean example establish hardware conformance, general GPU
progress, complete numerical verification, or a Gemma implementation.
