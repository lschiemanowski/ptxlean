# Reusable pure instruction families

A pure instruction here reads finitely many 32-bit values and true-or-false
predicate values, then writes one 32-bit register. It cannot read or write
memory, change an address or predicate register, branch, or terminate a thread.
The common mechanism advances the program counter and uses the existing scalar
state, whose initial register values are supplied by the caller.

Each family specifies its operations, their numbers of value and predicate
operands, the permitted result relation, and the targets supporting each
operation. A result relation can allow several output words. The family must
prove that a result exists for every assignment of its operand values; this
interface is for total pure operations on those values. That proof establishes
nonemptiness, not fidelity to PTX. The family-specific semantics, target
conditions and source justification still need independent review.

An instruction's guard decides whether it executes. Its predicate operands are
separate inputs to the operation itself, such as a selector choosing between two
words. Value operands can name registers or carry exact 32-bit literals.
Predicate operands can name a predicate register with either polarity, or carry
a Boolean constant. The generic representation does not assert that every such
operand is legal PTX text: a family's decoder and register-type rules must
establish which forms the source language permits.

When the guard is true, every input is evaluated in the incoming state before
the destination is written. Sources may repeat or name the destination. Only
that value register changes, and the program counter advances by one. When the
guard is false, all register banks and memory remain unchanged and only the
program counter advances. A fetched step additionally requires that this exact
instruction occurs at the current program counter and is supported on the
selected target, including when its guard is false.

The occurrence records the actual instruction, its original program counter,
and whether it executed. Its read list contains the guard's predicate register,
then all value-operand registers and all predicate-operand registers in their
argument order. Repeated reads remain repeated. A skipped instruction records
only its guard read, and no destination write. These lists describe direct
syntactic register operands; they are not a proof of PTX memory dependencies or
that every operand can affect every result. No occurrence carries a memory event.

The common proofs expose the exact enabled and skipped transitions, destination
result relation, unchanged state, instruction origin and one-step existence.
Determinism requires a separate proof that the family's result relation permits
at most one value. Family source proofs and text decoders can reuse this
mechanism without modifying the scalar state or duplicating its transition
rules. It supplies no complete-kernel termination result and adds no instruction
to the accepted PTX coverage merely by admitting a family.
