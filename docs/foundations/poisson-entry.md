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

The next issue is connecting this visibility result to the numerical theorem. Each lane has
executed its store, but subsequent loads must be tied to those records through
the barrier in one combined history. Source restriction must also account for
later output stores, which were absent in the prefix. Neither a copied shared
snapshot nor the change in counter numbering proves that obligation.

## From lane results to recorded stores

A lane's final local memory is only one part of a concurrent execution. The
memory argument for another lane needs an actual store record: who wrote,
where, when in the program, and which bits. It also needs to know that another
writer cannot overwrite those bytes.

[CellEntryOccurrence](../../integration/torchlean/PoissonPTX/CellEntryOccurrence.lean)
proves that a completed active lane cannot avoid instruction 19, its store.
This remains true even if the old bytes already contain the correct answer.
[CellEntryPadding](../../integration/torchlean/PoissonPTX/CellEntryPadding.lean)
proves the opposite for inactive lanes: their branch bypasses the store.

[CellEntryProducers](../../integration/torchlean/PoissonPTX/CellEntryProducers.lean)
then derives each record's address and word from the actual execution. It proves
that different lanes' eight-byte slots do not overlap and that a byte covering
a given slot must belong to its owner, at the matching within-word offset.
[CellEntryStoreTensor](../../integration/torchlean/PoissonPTX/CellEntryStoreTensor.lean)
connects the recorded value to TorchLean's cell-input entry. The ordinary
allocation, initial-byte representation and completed-run conditions remain
visible; no desired store list or output word is supplied.

[The producer checks](../../integration/torchlean/PoissonPTX/CellEntryProducerChecks.lean)
instantiate coverage, padding exclusion and separation on the nonzero 32-thread
run. These results provide the writer side of the barrier visibility proof below.

## Why another lane sees the gathered word

[CellEntryHistory](../../integration/torchlean/PoissonPTX/CellEntryHistory.lean)
recovers an actual arrival by every participant before the first barrier
completes. It proves every gather store precedes its writer's arrival. Once
a lane reaches instruction 20, its remaining prefix contains no more stores.
Padding lanes must arrive too, even though they wrote no gathered values.

[CellGatherPreservation](../../integration/torchlean/PoissonPTX/CellGatherPreservation.lean)
checks the other side of the interval: the later arithmetic writes only shared
planes 1 through 6, and the output tail writes global memory. The gathered
plane 0 is untouched. This fact is derived for arbitrary actual body runs.

[CellEntryContinuation](../../integration/torchlean/PoissonPTX/CellEntryContinuation.lean)
combines those facts with the necessary byte-source rules. A subsequent read of
a gathered slot must return the gathered word. It cannot use old initialization
after the performed write. Different bytes may still choose different source
records; every covering record supplies the same proved byte.

The theorem takes actual prefix and continuation runs. Its prefix input-source
premises are discharged by the joint-history theorem described below. The
numerical proof uses a derived initial-byte view, also explained below. The continuation changes only the instruction-counter origin;
it does not install a convenient shared snapshot.

[Visibility checks](../../integration/torchlean/PoissonPTX/CellEntryVisibilityChecks.lean)
exercise actual producer ordering on the nonzero 32-thread prefix, force a later
observation to see its gathered minus-two bits, and reject stale bytes. The
appended observation is a memory-interface test, not a fetched arithmetic run.

## Connecting visibility to the numerical result

The arithmetic theorem calls its input memory “initial.” At the start of the
whole kernel, shared memory has not yet been filled; at the start of arithmetic,
its input is what the gather just published. These are different proof views.

[CellEntryPublication](../../integration/torchlean/PoissonPTX/CellEntryPublication.lean)
builds the second view from actual post-gather lane memories. It proves agreement
with every gathered store byte and preservation of untouched bytes. This is an
accounting view, not a replacement of the running threads' memories.

[SourceCut](../../integration/torchlean/PoissonPTX/SourceCut.lean) converts the
joint byte-source assignment: prefix stores become this view's initial bytes,
and later stores retain their identities with shifted positions. The real
barrier excludes stale initialization on covered bytes. The body's separation
from gathered slots preserves its subsequent performed-write conditions.

[CellEntryCorrespondence](../../integration/torchlean/PoissonPTX/CellEntryCorrespondence.lean)
then connects the actual numerical result and published cell-output tensor to
TorchLean's gather and cell calculation. Coefficients are read from their initial
arena tables. Output records may be published in any order. The modular proof takes prefix and body executions separately. The joint-history
version derives the prefix's input admission; obtaining both executions from
one full-entry run is now proved.

[The rebasing regression](../../integration/torchlean/PoissonPTX/CellEntryRebaseChecks.lean)
executes lane two through a coefficient load and a shared load after the actual
nonzero gather. The latter reads lane zero's minus-two word. Lane two's local
bytes at that address are still the old pattern; the checked source account,
not a fabricated memory update, establishes the new value. This partial witness
exercises both source contracts without claiming complete-run existence.

## Why the earlier input reads are justified

The full history contains global output stores. Therefore “the gather contains
no global stores” alone does not justify its earlier reads: their possible byte
sources are checked against the whole history. The proof derives separation in
an order that avoids assuming the answer.

1. [Control](../../integration/torchlean/PoissonPTX/CellEntryControl.lean)
   derives the arena, lane and cell registers without any read-value premise.
   [The branch proof](../../integration/torchlean/PoissonPTX/CellEntryActive.lean)
   excludes padding lanes from the gather.
2. [Connectivity addresses](../../integration/torchlean/PoissonPTX/CellEntryIndexAddress.lean)
   follow the actual low-word multiply-add and four-byte scaling instructions.
   The input layout places these bytes before the output region.
3. [Index admission](../../integration/torchlean/PoissonPTX/CellEntryIndexInputs.lean)
   excludes every later output store and forces the four-byte index to come
   from initialization.
4. [Source addresses](../../integration/torchlean/PoissonPTX/CellEntrySourceAddress.lean)
   use those justified indices. Initial connectivity bounds and the source
   array's separation then force the eight-byte value reads to initialization.

[The joint-history cell theorem](../../integration/torchlean/PoissonPTX/CellEntryJointCorrespondence.lean)
uses this result to remove separate prefix-admission premises from the published
TorchLean tensor result. Input and output arrays must be disjoint in the stated
layout, and integer address calculations must not wrap. These are physical
storage conditions; no desired intermediate or final value is supplied.

[The regression](../../integration/torchlean/PoissonPTX/CellEntryJointChecks.lean)
instantiates derived admission on the nonzero gather and actual cross-lane
continuation. It also rejects a layout placing output over connectivity.
That witness remains partial. A separate full-entry witness now executes the
zero-data case through all four barriers and every thread's return; it checks
four output stores and both byte-source admission conditions.

## One execution from entry to return

A single execution of the complete cell entry now derives the first-barrier
split and both fetched subruns. Instruction counters stay absolute in the
execution: arithmetic starts at counter 21. The proof translates its local
view in both directions, including branch destinations, data records and
barrier sites. A barrier generation counts completed uses of the barrier;
events before and after the first release use different generations, so
translating later sites leaves the earlier barrier's identity unchanged.
This transports the byte-source conditions without supplying computed values.
The resulting theorem publishes the TorchLean cell tensor from the full run's
actual global-store history. Layout, represented input arrays, necessary
byte-source admission and completion of the active lanes remain explicit
premises. Coefficient tables are still decoded initial inputs.

[The full-entry theorem](../../integration/torchlean/PoissonPTX/CellWholeCorrespondence.lean)
uses one execution, starting at instruction zero. It derives the first-barrier
boundary rather than asking the caller to identify it. The native execution
uses the emitted instruction counters throughout. Its proof view subtracts 21
from body counters and records; a generation-sensitive change of barrier keys
preserves which writes precede which reads. Memory addresses, loaded bits,
thread identities and source positions do not change.

[The nonzero witness](../../integration/torchlean/PoissonPTX/CellWholeChecks.lean)
checks a gather and cross-lane read. [The complete zero-data witness](../../integration/torchlean/PoissonPTX/CellWholeZero.lean)
executes all 32 threads through return, including the 28 padding lanes, and
checks its four output stores and necessary byte-source conditions. These
witnesses do not establish termination for every input or GPU scheduling policy.

## Naming the operator and assembling cells

The complete cell theorem names the operator whose coefficients were uploaded.
A representation contract relates each initial binary64 word of the B, D and W
tables to the corresponding TorchLean coefficient, and requires equal numbers
of quadrature points and interpolation nodes for this square-table kernel.
The proof preserves the ordered calculation when transporting tensor dimensions
and concludes equality with that operator's localAction. This is an input
representation contract, not an assumption about the computed output. External
host generation and serialization of those tables are not proved by it.

[The operator theorem](../../integration/torchlean/PoissonPTX/CellOperatorCorrespondence.lean)
concludes equality with `localAction o.b o.d o.w (gather o values cell)`.
Its new premises specify the input bytes and dimensions. They do not state
anything about intermediate or output values.

The assembly traversal loop now has correctness and execution-existence
proofs. Every completed fetched execution performs the ordered left fold over
its initial cursor range, including its actual four-byte contribution indices
and eight-byte values. A physical layout of the two allocated input arrays,
with every index in range, discharges all access premises. If the cursor starts
at or before the unsigned end index, each iteration advances it without wrap,
so a returning execution exists. No iteration count, read value or result is
assumed. The proof uses a read-only memory snapshot for this loop slice.

The emitted loop slice is bound to its Lean instruction list through the exit
label. The isolated loop theorem returns at that label; the emitted entry
continues with optional boundary masking and an output store. Entry setup,
that continuation and inter-launch memory visibility still need composition.
A nonzero kernel-checked witness sums the same three contributions in two
orders and obtains different results, exercising the reason for preserving
floating-point order. Empty-list, insufficient-fuel and invalid-index checks
exercise completion and failure behavior. Fuel is only a bound on executable
witness search; it is absent from the relational correctness theorem.

[The loop proof](../../integration/torchlean/PoissonPTX/AssemblyLoop.lean)
recovers all iterations from comparisons, branches and fetched loads.
[The layout proof](../../integration/torchlean/PoissonPTX/AssemblyLayout.lean)
explains why each index and value read fits its allocation.
[Existence](../../integration/torchlean/PoissonPTX/AssemblyExists.lean)
follows by decreasing the number of entries remaining.

For example, adding `2^53`, `1`, then `-2^53` in binary64 yields zero; adding
`-2^53`, `2^53`, then `1` yields one.
[The checked execution](../../integration/torchlean/PoissonPTX/AssemblyChecks.lean)
loads those values via actual four-byte index tables. The table order is part
of correctness, even though both orders enumerate the same values.
