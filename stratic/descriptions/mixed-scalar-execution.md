# Mixed scalar and floating-point execution

A kernel can move encoded numbers between memory and registers, perform
floating-point arithmetic, then store the result. This execution layer puts
those instructions in one program while reusing the scalar state. Every
instruction and recorded step carries a tag identifying whether it uses the
existing integer and memory rules or binary32 arithmetic. A
floating-point step is never represented by an integer instruction with a
substituted result.

Each dispatch reads the instruction at the current program counter. A scalar
instruction uses the existing scalar evaluation, including its predicates,
branches, faults and explicit exit. A floating-point instruction uses the
binary32 instruction relation, including every result admitted by its numerical
contract. Its optional predicate controls execution exactly as in that relation.
A missing instruction reports the scalar invalid-program-counter fault. Unknown
scalar operations remain unsupported even under a false predicate. Each event
retains the instruction actually fetched, its position and its original effects.

This slice uses PTX ISA 9.4 with a numeric target requirement of at least sm_70.
The floating-point operations alone need only sm_20, but the scalar memory
instructions use relaxed ordering and GPU scope, whose qualifiers require
sm_70. The numeric condition selects features; it does not validate complete
GPU target names. Unsupported targets have no admitted dispatch, rather than
an invented hardware fault.

A finite path is a sequence of advancing steps. It can stop before the program
finishes and therefore proves no termination by itself. A completed run follows
a finite path with an actual exit instruction. Faults and unsupported operations
are separate terminal outcomes. Exit retains its own event; faults and unsupported
operations retain the current state without inventing an instruction event.
This interface describes finite executions. It does not introduce a fuel-bounded
runner or treat an empty path as successful completion.

Memory reads use the current caller-supplied list of words, the arena. They do
not obtain arbitrary candidate observations. This is a sequential, isolated
execution discipline: outside threads, the host and asynchronous work must not
interfere with the arena during the example. It is not a replacement for PTX's
concurrent memory rules or a proof that arbitrary PTX kernels execute sequentially.
The word arena does not model mixed-width or overlapping byte accesses, runtime
allocation, permissions, address translation or argument passing.

Every successful memory access retains the scalar alignment and whole-access
bounds checks. Floating-point steps have no memory effect. Advancing steps
preserve arena length, so safety applies to every event in a finite path or run,
including paths that later stop with a fault. Memory not targeted by any recorded
store remains unchanged. These are lifted properties of the original instruction
rules, rather than new arithmetic or memory definitions.

Every eligible state has a dispatch outcome, but that does not mean every
program terminates. Constructing a floating-point next state uses existence in
the numerical result set. Universal run properties must cover all members of
that set, including its conservative freedom for NaNs, special “not a number”
results. A chosen numerical reference can witness existence but cannot replace
the allowed execution relation. Hardware progress and exact NaN realizability
remain separate questions.
