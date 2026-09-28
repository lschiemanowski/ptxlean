# Poisson binary64 PTX compatibility review

The project's semantic target is PTX 9.4. The Poisson hardware artifact explicitly
selects PTX 9.2 because that is what the installed CUDA 13.2 assembler supports.
This review concerns only the directly authored Poisson kernels, and is not a
formal refinement proof between PTX versions or a hardware conformance claim.

The primary sources are NVIDIA's [PTX 9.2 manual](https://docs.nvidia.com/cuda/archive/13.2.0/parallel-thread-execution/index.html)
and the pinned [PTX 9.4 manual](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).
The [review receipt](receipts/poisson-ptx-compatibility.json) records document and
normalized section hashes. The manuals themselves are not distributed here.

The emitted floating-point operations are `add.rn.f64`, `sub.rn.f64`,
`mul.rn.f64`, `div.rn.f64`, `sqrt.rn.f64`, `abs.f64`, `max.f64` and comparisons.
The arithmetic `.rn` modifier selects rounding to nearest, ties to even. These
are binary64 operations; there are no approximate instructions, float32
conversions, fused multiply-adds or flush-to-zero modifiers. Explicit rounding
on multiply/add and the assembler's `--fmad=false` preserve the chosen separation.
The arithmetic sections used by this subset agree between the pinned manuals.

Integer operations compute bounded 32-bit indices and widened 64-bit addresses.
Host validation limits both global-node and element-entry counts below `2^30`.
`mad.lo.u32`, integer multiply/divide/remainder, predicate operations, moves,
conditional branches and returns implement indexing and control. Entry kernels
require their exact launch dimensions with `.reqntid`; these are matched by the
runtime's launch manifest. No device functions or inter-kernel device launches
are used. The integer-add section adds an architecture for unused packed and
saturating forms; the ordinary additions used here are unchanged.

Global and shared scalar loads/stores are naturally aligned to their four- or
eight-byte widths. With no memory-order qualifier they are **weak accesses**:
the loads and stores do not themselves establish synchronization. Shared-memory
phases use `bar.sync 0`; every thread in the group reaches each barrier, including
threads with no active matrix entry. Each vector or assembly output has one
writer, and kernels run in order on the same CUDA stream. Host observations use
synchronous device-to-host copies. These execution conditions are part of the
backend, not assumptions discharged by existing PTXLean memory proofs.

The load/store sections differ between 9.2 and 9.4, but the reviewed changes
concern unused memory-mapped I/O ordering forms, a read-only proxy, cache-policy
spelling and their version/target notes and examples. The ordinary scalar
`.global`/`.shared` forms used here retain their relevant contracts. The
barrier section agrees after section-number and whitespace normalization.

This review does not extend the project's formal binary32 execution model to
binary64, or change existing instruction-coverage claims. Compilation and
sanitizer results add empirical evidence for the specific saved artifacts.
