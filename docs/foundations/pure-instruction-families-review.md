# Independent review of the pure instruction-family mechanism

Reviewed against source SHA256 `02eb8b1cb85b2d40f7e0befe65a75be57ae91cff09e6c2a78ad9c6e04ca98fd5`.
The reviewer did not author the implementation. This is a mechanism review,
not acceptance of any new PTX instruction form.

The family result relation remains visible in every enabled transition; two
allowed outputs remain distinct possible transitions. Determinism is conditional
on a functional leaf relation. All operands are evaluated in the incoming state,
including a destination alias. False guards advance only the instruction pointer;
unsupported targets and missing fetches admit no successful step even with a
false guard. No memory, address register or predicate register is modified.

Independent kernel-checked probes exercised a nondeterministic family, a source
that aliases the destination, a guard sharing its predicate with a data operand,
ordered metadata including duplicate reads, skipped metadata and unsupported
target rejection. These are mechanism tests, not hypothetical PTX opcodes.
Fresh source elaboration, the public dependency audit and the independent probes
passed. Public dependencies are standard Lean axioms only.

The target predicate, result relation, textual legality and source interpretation
remain per-leaf review obligations. Syntactic register-read metadata is expressly
not claimed to be a PTX dependency or no-thin-air algorithm. The mechanism has
no parser, memory accesses, branches, complete-program execution, or guarantee
that the caller supplied a semantically faithful family.
