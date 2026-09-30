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

The indexed gather still needs an actual 32-bit connectivity load, the following
64-bit input load, a shared store, and the first barrier. Those instructions must
preserve the prologue registers and establish the arithmetic slice's initial
shared tensor. We do not reset the program counter or install gathered bytes to
claim that this composition has already been proved.

Run `integration/torchlean/check.sh` for the registered proofs and axiom audit,
and `python3 -m unittest discover -s hardware -p 'test_*.py'` for binding tests.
