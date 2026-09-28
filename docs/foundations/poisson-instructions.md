# From Poisson PTX instructions to a TorchLean result

There is a proved instruction-level connection for **one thread of
`true_residual`**, the kernel that subtracts the computed operator value from
the right-hand side. There is not yet a proof of the complete Poisson solver's
PTX implementation. In particular, this theorem does not establish that the
input called `ap` really contains `A x`.

For an active index `i`, the statement is:

```
output[i] = binary64_subtract(initial_rhs[i], initial_ap[i])
          = TorchLean.Tensor.subSpec(initial_rhs, initial_ap)[i]
```

This is a statement about every completed execution of the modeled instructions,
not an assumption supplied by an execution record. The numerical equality uses
Lean's logical `Float` values: it distinguishes signed zeros and preserves the
freedom of NaN encodings by comparing after decoding. It is not equality with
exact real subtraction, nor a claim that all NaN payload bits agree.

## Read the proof in small pieces

1. [Bytes](../../integration/torchlean/PoissonPTX/Bytes.lean) reads and writes
   eight little-endian bytes: the lowest-addressed byte contains the least
   significant bits. `read64_write64` proves the exact round trip;
   `read64_write64_disjoint` proves that an unrelated word is preserved.
   Validity includes the allocation's lower bound, alignment to eight bytes,
   its upper bound, and the 64-bit address limit.
2. [Machine](../../integration/torchlean/PoissonPTX/Machine.lean) gives individual
   instructions their register and memory effects. Loads read the actual
   calculated byte address. Invalid accesses have no successful step.
   Arithmetic chooses any output word whose decoded value is the specified
   binary64 result. The executable interpreter chooses a canonical encoding;
   the universal theorem covers the entire relation.
3. [MemoryBlocks](../../integration/torchlean/PoissonPTX/MemoryBlocks.lean)
   proves the emitted address sequence: widen the 32-bit index, multiply by
   eight, add the arena base, then add the field offset. It proves loads and
   stores from those instructions, rather than assuming a stream of tensor
   elements is supplied to the arithmetic.
4. [Residual](../../integration/torchlean/PoissonPTX/Residual.lean) joins two
   loads, one subtraction, and one store. It derives the result from the
   initial bytes and proves that only the output's eight bytes can change.
5. [Kernel](../../integration/torchlean/PoissonPTX/Kernel.lean) fetches each
   instruction by its program counter. A completed execution must reach a
   return instruction. The kernel prologue reads the arena parameter and the
   lane and group indices, computes `group*256+lane`, and returns early for
   padding lanes.
6. [ResidualKernel](../../integration/torchlean/PoissonPTX/ResidualKernel.lean)
   proves `fetched_correct`, `fetched_frame`, `fetched_exists`, and
   `fetched_inactive` for that complete 20-instruction entry. An active lane
   has a finite execution when its accesses are valid; an inactive lane
   needs no data allocation and changes no memory.
7. [Layout](../../integration/torchlean/PoissonPTX/Layout.lean)'s
   `array_coordinate` connects the computed addresses to ordinary contiguous
   arrays and **the actual TorchLean `Tensor.subSpec` definition**. Its
   hypotheses concern the initial arena, field bounds, alignment, index and
   execution. None asserts the desired output. `field_valid` derives the
   three access-validity premises from allocation conditions.

The model permits arbitrary initial registers and byte values. The initial
program counter is zero and the thread has not returned. A launch context
provides the arena base and lane/group IDs. The allocation represents initialized,
readable and writable storage. The layout theorem requires that the allocation
fits below the 64-bit address limit. The index calculation is modular as in PTX;
`index_exact` separately recovers ordinary integer indexing under a no-wrap
bound. The checked frontend restricts vector lengths to the backend's existing
32-bit domain and checks its 256-thread launch dimensions.

[Arithmetic](../../integration/torchlean/PoissonPTX/Arithmetic.lean) additionally
connects finite-input subtraction to FloatLib's proved binary64 software
operation. This bridge includes cancellation and overflow; it does not assume
that the result is finite. Kernel checking establishes validity relative to
these definitions. Reviewing those definitions against PTX is a separate task.

## Connecting the proof to the PTX file

[Text](../../integration/torchlean/PoissonPTX/Text.lean) renders the very same
parameterized instruction list used by the proof.
[check_poisson_ptx.py](../../hardware/check_poisson_ptx.py) compares those strings
with the actual saved `true_residual` entry, including register declarations,
parameter spelling, index calculation, predicate and return. It also checks
module version/target, field sizes and offsets, launch dimensions and saved
artifact hashes. It accepts only the emitter's narrow dialect and rejects
comments, duplicate entries, and changed instructions.

This is a checked frontend binding, **not a proved PTX parser or compiler**.
Running its Lean renderer trusts compiled execution. Its receipt records the
proof/frontend hashes and which saved modules it checked. The closed examples
in [Checks](../../integration/torchlean/PoissonPTX/Checks.lean) instead use Lean
kernel reduction: subtraction, padding, and rejection of misaligned or
out-of-allocation accesses, as well as failure to report success before a return.

```sh
# Full proof and dependency audit; no GPU required:
integration/torchlean/check.sh

# Compare a saved numerical run with the Lean instruction program:
python3 hardware/check_poisson_ptx.py \
  --run .hardware-runs/poisson-local \
  --output .hardware-runs/poisson-instruction-binding.json

# Check frontend mutation/rejection tests:
python3 -m unittest discover -s hardware -p test_poisson_ptx.py
```

Use a new output path. A saved run can come from `hardware/validate_poisson.py`;
there is no need to rerun unchanged kernels to check their emitted instructions.

## Semantic review and exact remaining obligations

The review uses the locally pinned PTX ISA 9.4 source, document SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Relevant source sections are integer `mad`, `mul` and `add`, `setp`, `mov`,
`ld`, `st`, floating-point `sub`, `ret`, special registers, and `.reqntid`.
The review is against those particular forms, not full mnemonic coverage:

- `mad.lo.u32` keeps the low 32 bits; `mul.wide.u32` retains the full widened
  product. Address additions are modulo 64 bits. The separate layout proof
  excludes wrapping for its arrays.
- `sub.rn.f64` rounds to nearest with ties to even and supports binary64
  subnormal values. Explicit rounding prevents treating this as a contracted
  multiply-add. The numerical relation allows NaN payload freedom.
- Scalar `ld.global.f64` and `st.global.f64` transfer eight bytes and require
  natural alignment. The modeled parameter load receives its value from the
  launch context; it is not a proof of the CUDA parameter ABI.
- Predication evaluates the guard, and a taken `ret` exits this thread.
  The `.reqntid` declaration is checked against the launch metadata.

The existing [9.2/9.4 source comparison](../../hardware/receipts/poisson-ptx-compatibility.json)
records the compatibility review for the backend's selected forms. This is
source evidence, not a theorem relating the complete two ISA versions. Vendor
prose is not redistributed here.

**The critical restriction is memory concurrency.** This new model has concrete
sequential byte storage. PTX's ordinary loads/stores are weak memory operations;
a sequential memory map is not their general concurrent semantics. Existing
parallel admission proofs in this project use four-byte observations. They do
not automatically justify this new eight-byte model. Therefore the proof above
is a per-thread instruction result, conditional on its concrete-memory execution
model. It does not yet cover arbitrary parallel PTX executions, even of this
barrier-free entry.

To prove the complete requested implementation correspondence still requires:

1. Eight-byte memory observations, sources for each read, ownership and
   synchronization, related to the PTX memory rules; then a proof that permitted
   parallel executions supply the reads used by the sequential reasoning.
2. Fetched instruction proofs for the shared-memory cell phases, assembly,
   reductions and PCG update kernels, joined to the existing ordered TorchLean
   calculation lemmas. Barriers must establish which writes later loads observe.
3. Composition through the host's launches and stopping/breakdown branches,
   retaining the GPU reduction order and the separate exact residual certificate.

Assuming that each phase produces its mathematical answer would bypass precisely
these obligations. The result certificate remains useful independently: it
certifies an accepted solution even while the implementation proof is incomplete.
