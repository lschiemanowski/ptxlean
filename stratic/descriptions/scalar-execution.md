# Scalar execution

The scalar machine describes instructions operating on individual values in one
thread. It handles integers and their bits, registers, memory reads (loads),
memory writes (stores), and choices of the next instruction (branches). An
instruction's input values are its operands; a true/false condition controlling
whether it executes is its predicate. Memory values are 32-bit words. Unsigned
32-bit arithmetic, abbreviated `u32`, keeps results modulo `2^32`, so overflowing
results wrap into the range from zero to `2^32 - 1`. The record of steps taken is
a trace; it retains the actual values and addresses used by loads and stores.

The instruction representation has a documented relationship to textual PTX.
Unsupported syntax and features cannot silently execute as supported operations.
Invalid instruction use and memory accesses are explicit outcomes. Local finite
runs and bounded execution procedures have checked relationships; exhausting a
bound is not evidence of program termination.

A read value may determine data written later, a later memory address, or which
instructions run next. These are data, address, and control dependencies. Their
role in permitted memory behavior must be justified when combining threads.
Kernel proofs state their memory and scheduling assumptions and distinguish a
sufficient restricted way to execute a kernel from a model of every PTX execution.

Reusable execution and safety rules support concrete scalar kernel proofs.
Examples establish functional results, memory safety, execution existence, and
termination under explicit premises, without substituting any one property for
the others. Explanations connect source semantics and instruction traces to the
Lean definitions and proofs.

The kernel examples compute on corresponding array elements and traverse a
bounded part of an array using actual instructions. Their contracts state the
initial registers and memory layout, the results and unchanged storage, valid
access ranges, and enough execution steps to finish. Combining per-thread results
requires explicit conditions on who can write which locations and how the
threads may be scheduled.

Reusable proof rules combine instruction steps and finite runs, use properties
preserved by execution (invariants), prove termination with a decreasing
nonnegative quantity, and preserve memory that the run never writes.

## State, instructions, and stopping

A state records everything needed for the next step: a program counter identifying
the next instruction, separate groups of 32-bit value and 64-bit address registers,
true/false predicate registers, and a list of memory words. These register groups
are called banks. Initial registers, predicates, and memory are caller inputs,
not assumed zero. Instructions read operands from the incoming state. A false
predicate skips a supported operation and advances the program counter; the
trace still records the skipped step. Unknown operations are rejected even
under a false predicate.

The subset includes 32/64-bit copies, wrapping `u32` addition and subtraction,
multiplication retaining its low 32 bits, unsigned minimum and maximum,
operations on individual bits, shifts, and unsigned comparisons. Address arithmetic uses unsigned 64-bit values (`u64`);
converting `u32` to `u64` fills the new upper bits with zeros (zero extension).
Loads and stores access globally shared memory using relaxed ordering at GPU
scope: they cover threads on that GPU but do not themselves provide a
release/acquire synchronization pair. Branches and explicit exit are included.
Shifts use the full unsigned count; counts at least 32 produce zero. Excluded
operations include floating-point arithmetic, indivisible read/update operations
(atomics), thread-rendezvous instructions (barriers), work initiated for later
completion (asynchronous operations), and collective operations on hardware
thread groups called warps.

One attempt to execute the next instruction is a dispatch. It can advance,
execute exit, report an invalid operation or access (a fault), or encounter
unsupported syntax. The runner is given a maximum number of dispatches, called
fuel. Using all fuel reports exhaustion; it does not establish that the program
finished. Completion requires executing exit. Falling off the instruction list
is a fault, not an implicit exit. Skipped instructions and exit also consume
fuel. A separately defined step-by-step proof of a finite run agrees with the
executable runner, including its exhausted prefixes.

## Concrete memory and candidate observations

Concrete execution reads the current memory list, called its arena. Byte address
`4*i` denotes word `i`, starting at address zero. Addresses contain 64 bits and
arithmetic on them can wrap. Every accepted access checks four-byte alignment
(a starting address divisible by four) and that all bytes fit inside the arena.
Stores replace existing words without resizing the list. These access-safety
results also apply to a run that later faults or exhausts its fuel; they do not
prove successful completion. Faults are outcomes of this safe interpreter, not
a claim that hardware traps in that particular way for every invalid PTX access.

Candidate execution can substitute proposed values for load results. These can
affect later registers, stores, addresses, and branches. Evaluating such a run
with safe addresses does not prove that PTX permits its observations of memory.
A general concurrent admission rule must also exclude values justified only by
circular dependencies, the issue called no-thin-air. Simply forbidding all
cycles is not a justified replacement. Restricted kernel connections state
their own sufficient assumptions.

The text interface accepts supported instruction names, called mnemonics, with
operands already classified by type and branch labels already resolved to targets.
Encoding and decoding preserve supported instructions. Reading raw PTX text,
checking declarations, resolving labels, and validating launches are separate
tasks. So are application binary interface (ABI) rules, which specify how code
passes arguments and uses storage when called. An internal store of a literal
constant is excluded from supported PTX text: PTX store data must be in a register.
The simple arena and typed interface keep instruction proofs manageable while
leaving these frontend and runtime obligations explicit.
