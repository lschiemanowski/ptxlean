# Execution environment

The execution environment describes the setting in which thread instructions
run: where each thread belongs, which memory it may use, and which instruction
forms the selected GPU and PTX version support. These are separate requirements.
An instruction may be supported but use an invalid address; an allowed memory
access may still need synchronization before another thread can observe its data.

Thread groups and scopes describe who can cooperate. A cooperative thread array
(CTA) is a group of threads that can use shared memory and synchronization;
CTAs launched together form a grid. A scope specifies which participants an
operation includes. The thread-group description explains these relationships,
including groups of CTAs called clusters and cooperation across a GPU.

Storage and valid memory accesses describe which regions have been reserved,
who may read or write them, and which addresses fit. They also state which byte positions are allowed as starting addresses
(alignment) and what is known about initial contents. A checked
connection shows how the scalar interpreter's memory accesses satisfy a
particular allocation contract.

Instruction and hardware requirements describe which combinations of instruction
form, PTX version and GPU capability are supported. A form outside the implemented
checker is distinguished from an illegal use of a represented form. Passing this
check establishes neither a valid memory address nor correct kernel execution.

Memory observations and ordering is a separate responsibility: it determines
which writes may supply read values and what synchronization guarantees. It uses
the thread identities and scopes supplied here. Its whole-word and byte-level
models are two representations of observations, not two modes of this environment.
Their conditions for accepting executions do not automatically include the full
allocation or hardware checks. Combining these guarantees requires explicit
proofs, with the assumptions of each check retained.
