# Scalar execution

The scalar machine executes a specified subset of integer and bit instructions,
predicates, register operands, address calculations, loads, stores, branches,
and explicit termination. Word arithmetic has fixed-width PTX behavior. Dynamic
instruction occurrences retain control and memory effects; executed register
values determine store operands and computed addresses.

The instruction representation has a documented relationship to textual PTX.
Unsupported syntax and features cannot silently execute as supported operations.
Invalid instruction use and memory accesses are explicit outcomes. Local finite
runs and bounded execution procedures have checked relationships; exhausting a
bound is not evidence of program termination.

Data, address, and control dependence must be accounted for when relating scalar
runs to permitted memory behavior. Any sufficient execution discipline or
unimplemented general dependency semantics is distinguished from a complete
characterization of PTX executions. Kernel proofs expose their applicable
memory and scheduling conditions.

Reusable execution and safety rules support concrete scalar kernel proofs.
Examples establish functional results, memory safety, execution existence, and
termination under explicit premises, without substituting any one property for
the others. Explanations connect source semantics and instruction traces to the
Lean definitions and proofs.

The scalar kernel examples execute concrete instruction lists for elementwise
integer computation and bounded traversal. Their contracts identify initial
register and memory representations, returned values, preserved storage,
access bounds, and a sufficient execution bound. Any lane-wise composition
states the ownership and scheduling discipline under which local results apply.

Reusable proof rules compose instruction steps and finite execution segments,
express loop invariants and termination measures, and preserve memory outside
the writes of a run.
