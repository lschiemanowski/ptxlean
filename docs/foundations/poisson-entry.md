# From launch inputs to cell coordinates

Before gathering a cell's input values, each element kernel executes seven
instructions. They establish the addresses, thread and cell indices, an active
flag, and the thread's two-dimensional position in the cell. These instructions
are now a separate proof boundary; they do not establish the gathered values.

For a cell of width `w`, a thread with index `t` computes:

```
live = t < w*w
row = t / w
column = t % w
```

For example, at width three, thread five handles row one, column two. Threads
nine through thirty-one still execute this setup, but their `live` flag is
false. The later guarded gather must skip their loads and stores while keeping
them involved in the barrier. The prologue proof itself contains no barrier.

## What is executed

[CellPrologue](../../integration/torchlean/PoissonPTX/CellPrologue.lean) models the
actual seven-instruction prefix:

```ptx
mov.u64 %shared, scratch;
ld.param.u64 %base, [arena];
mov.u32 %lane, %tid.x;
mov.u32 %cell, %ctaid.x;
setp.lt.u32 %live, %lane, 9;
div.u32 %i, %lane, 3;
rem.u32 %j, %lane, 3;
```

The typed program takes the width as a parameter. Execution fetches each
instruction using the current program counter; seven successful steps finish
at counter seven. Running out of instructions or using an unsupported zero
divisor fails. Stopping after seven steps denotes reaching this prefix boundary,
not returning from the kernel.

The launch context supplies the arena parameter value, the address of `scratch`
within shared memory, and the unsigned 32-bit thread and cell indices. This is
consistent with the existing kernel context abstraction, but it does not prove
CUDA parameter passing, symbol allocation or the driver ABI. The register
container uses 64-bit words; 32-bit values are zero-extended, and division and
remainder inspect only their low 32 bits.

## What the theorems establish

`fetched_exists` constructs an execution for any initial registers and memory,
provided the program counter starts at zero, the width is positive, and its
square fits in 32 bits. `fetched_correct` proves that every such seven-step
execution has the explicitly calculated final state. This covers Q1 through Q4
(widths two through five), including padding lanes.

[CellPrologueEntry.ready](../../integration/torchlean/PoissonPTX/CellPrologueEntry.lean)
extracts the resulting base, shared address, lane, cell, row, column and active
flag. For an active lane, `coordinates` proves that both coordinates are below
the width and that `row * width + column` reconstructs the lane index.
`thread_registers` specializes the result to the 32 threads of a cell, deriving
the six registers expected by the arithmetic entry contract.

All global and shared array bytes remain unchanged, as do every register other
than the six written registers. No initial register value or desired final
coordinate is assumed. Allocation metadata is also preserved by the explicit
final-state equality.

## Fidelity and checks

The semantic review used the pinned PTX ISA 9.4 HTML whose SHA-256 is recorded in
[the source manifest](../../references/nvidia/ptx-isa-9.4/manifest.json), covering
`mov`, `setp`, integer `div` and `rem`, `%tid` and `%ctaid`. The shared symbol move
produces an address within shared memory, not a generic pointer. Division and
remainder are unsigned; zero divisors have unspecified results in PTX and are
outside this fragment. This prefix does not claim complete instruction-family
coverage, and it adds no entries to the ISA coverage ledger.

The Lean renderer traverses the very same typed program used in the fetched
proof. The saved-PTX checker compares all seven instructions before the first
gather guard, checks register declarations and shared allocation size, and
rejects extra intervening instructions. This is text-binding evidence, separate
from Lean proof checking and hardware conformance.

[CellPrologueChecks](../../integration/torchlean/PoissonPTX/CellPrologueChecks.lean)
checks all 32 lanes at each Q1–Q4 width from nonzero initial registers and bytes.
It also checks the maximum unsigned lane, unsupported zero width, a wrong entry
counter, and mutations to the row calculation and predicate boundary. Python
mutation tests exercise the emitted-code binding.

## Gathering the cell input

Each active lane first reads one connectivity entry: an unsigned node number
stored in four bytes. That number selects an eight-byte value from the source
vector. The lane copies that word into its own shared-memory slot. There is no
floating-point arithmetic here: even signed zero and NaN payloads are copied
unchanged. Using an eight-byte load for connectivity would incorrectly combine
adjacent indices and could cross an allocation boundary.

[CellGather](../../integration/torchlean/PoissonPTX/CellGather.lean) describes all
twelve instructions and proves both existence and the final state of their
fetched execution. [The layout proof](../../integration/torchlean/PoissonPTX/CellGatherLayout.lean)
turns ordinary array conditions into memory-access validity: aligned allocations,
indices in range and sizes small enough that integer addresses do not wrap.
The prologue's base addresses and cell, lane, row and column registers survive.

[The TorchLean theorem](../../integration/torchlean/PoissonPTX/CellGatherTensor.lean)
relates the stored word to `gather o values e`. Its premises say how the initial
connectivity bytes and source-vector bytes represent those inputs. The source
index is obtained by executing the load; the desired result is not supplied.

This is a snapshot proof: the loads read a fixed initial input memory. The concurrent prefix theorem below now establishes
its input reads. Connecting its shared store records to later arithmetic loads
in a joint history remains open. We do not
reset the program counter or install gathered bytes and call that composition.

The pinned PTX review covers unsigned `mad.lo.u32`, `mul.wide.u32`, and
ordinary global/shared loads and stores. The index multiply-add wraps at 32 bits;
the widening multiply produces a 64-bit product. The memory forms have no
synchronization of their own. These are bounded forms, not whole-family coverage.

The same typed program renders the complete guarded body of all three emitted
source-vector variants. The checker binds the body and its immediate barrier.
Mutation tests reject incorrect widths, strides, operands, destinations and
extra instructions. [Kernel checks](../../integration/torchlean/PoissonPTX/CellGatherChecks.lean)
cover adjacent four-byte indices, invalid bounds and alignments, nonzero addresses
and preservation of unusual floating-point bit patterns.

Run `integration/torchlean/check.sh` for the registered proofs and axiom audit,
and `python3 -m unittest discover -s hardware -p 'test_*.py'` for binding tests.

## The concurrent entry

[CellEntry](../../integration/torchlean/PoissonPTX/CellEntry.lean) combines the
seven setup instructions, the active-lane branch, twelve gather instructions,
and the first barrier. The barrier occupies counter 20; the next instruction
is 21. Threads may interleave arbitrarily, and waiting threads cannot advance.

Loads choose candidate values. [IndexSources](../../integration/torchlean/PoissonPTX/IndexSources.lean)
checks the four-byte indices against individual initial bytes or bytes from
actual eight-byte stores. The read records are separate from the existing
word/barrier list because these index reads cannot write or synchronize. This
is a restricted global-index extension, not a general mixed-width PTX model.

[CellEntryInputs](../../integration/torchlean/PoissonPTX/CellEntryInputs.lean)
proves that the prefix has no global stores. Consequently compatible global
reads must recover their initial values. [CellEntryReplay](../../integration/torchlean/PoissonPTX/CellEntryReplay.lean)
uses this result to recover each lane's local instruction trace from the actual
concurrent execution. No local trace or desired gather answer is an input.

[CellEntryResult](../../integration/torchlean/PoissonPTX/CellEntryResult.lean)
therefore proves that a completed active lane's shared word is its TorchLean
gather entry. [CellEntryBarrier](../../integration/torchlean/PoissonPTX/CellEntryBarrier.lean)
proves that crossing counter 20 requires an actual release and advances every
lane to 21. [CellEntryLaunch](../../integration/torchlean/PoissonPTX/CellEntryLaunch.lean)
derives the arithmetic launch contract. Its `resume` operation merely numbers
the continuation from zero: it preserves all memory, registers and barrier state.

A [32-thread witness](../../integration/torchlean/PoissonPTX/CellEntryChecks.lean)
uses nonzero bases, cell one, permuted connectivity, ordinary numbers, signed
zero and a NaN payload. Its complete execution and sources are checked. Leaving
out the last barrier participant prevents release. The same witness instantiates
the general launch theorem. This is an existence example, not the eventual
general existence proof.

The remaining issue is shared visibility in the continuation. Each lane has
executed its store, but subsequent loads must be tied to those records through
the barrier in one combined history. Source restriction must also account for
later output stores, which were absent in the prefix. Neither a copied shared
snapshot nor the change in counter numbering proves that obligation.
