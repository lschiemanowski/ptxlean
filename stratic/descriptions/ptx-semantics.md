# PTX semantics

The PTX semantics defines which executions of a PTX program are permitted.
An execution describes what the threads do, including the values they read
and write. NVIDIA's specification can allow several outcomes for the same
program and initial data. A correctness proof must cover the permitted outcomes,
not just one convenient run of a simulator.

## One thread and many threads

For one thread, an instruction might add two register values, read a value from
memory (a load), write one (a store), choose the next instruction (a branch), or
finish. Scalar execution describes steps operating on individual values. It
tracks registers and control flow, the choice of which instruction runs next,
and connects these steps to proofs about complete kernel computations.

With many threads, we must also explain how their memory accesses interact.
Suppose one thread writes a result and then sets a flag. Another thread reads
the flag and then reads the result. Seeing the flag does not by itself guarantee
that the reader sees the new result. The program needs the appropriate
synchronization: instructions and conditions that establish the required
ordering between the threads. This small example is called message passing;
it demonstrates when the reader must see the new result and when an old value
remains possible.

The execution environment describes which threads are grouped together, which
memory each can access, and which participants a synchronization operation can
coordinate. It also states the GPU and PTX-version requirements of instructions.
Permission to access memory and synchronization with another thread are separate
questions.

## How the formal model represents this

The model combines two kinds of rules. Instruction rules describe a thread's
individual steps. Memory observations and ordering describe how reads and writes across threads
fit together: which write supplies a read's value, and which accesses must be ordered.
A proposed collection of thread steps and read values is called a candidate
execution. Evaluating its individual instructions does not establish that its
memory behavior is permitted.

The connection between these rules is part of the proof. The reads and writes
checked by the memory rules must be the ones produced by the thread instructions,
including the values actually computed in registers. A simulator can help
construct executions, but a simulator's chosen order of steps must not silently
exclude other behavior that PTX allows.

## What a kernel proof promises

Different proof statements answer different questions:

- **Safety:** do accesses satisfy the stated memory bounds and access conditions?
- **Correctness of completed executions:** if an execution finishes, does its
  result satisfy the kernel's specification?
- **Execution existence:** is there an execution satisfying the model's rules,
  rather than a specification that accidentally permits no execution at all?
- **Termination or progress:** under what conditions does execution finish or
  continue to advance?

Scheduling determines when each thread gets to run.
These guarantees are stated separately, with their required assumptions. For
example, constructing one schedule that finishes does not prove that every
schedule finishes. A stronger progress claim may need a scheduling assumption
that threads are not indefinitely denied execution opportunities. Reusable
proof rules derive from the semantics and retain those conditions.

## Coverage and faithfulness to PTX

The scope is the full instruction set and computing model of PTX version 9.4.
It includes arithmetic, conditional execution and branching, memory,
synchronization, operations involving groups of threads, and operations that
start work whose completion is awaited later.
Legal instruction forms, types, and GPU/version restrictions are part of that
scope. Each implemented fragment states its restrictions; partial coverage
must not be presented as a complete model of PTX.

A missing formalization, an instruction unavailable on the selected GPU, and
behavior for which PTX provides no guarantee are different cases. They must
remain distinguishable. In particular, missing support must not make a
correctness theorem appear true merely because there are no admitted executions.

Definitions and their explanations are tied to passages of NVIDIA's PTX manual.
Lean checks that proofs follow from our definitions. Semantic fidelity asks a
separate question: do those definitions express NVIDIA's documented behavior?
Source review, proofs connecting parts of the model, and independent evidence
address that question. Ambiguities remain visible, and correspondence with a
compiler, runtime, or physical GPU requires its own justification.
