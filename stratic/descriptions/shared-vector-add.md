# Vector addition in a shared allocation

All lanes execute their scalar load, load, add, store, and exit instructions
against one explicit memory allocation. Each lane reads designated input words
and owns its output word; input/output separation and output uniqueness are
part of the representation or proved premises. Initial registers and memory
are explicit inputs.

A thread-step semantics permits instruction-level interleavings. Invariants
establish that other lanes cannot change a lane's inputs or overwrite its
output, that completed lanes return the modular sum, and that every actual
access remains in bounds. An explicit schedule constructs a completed execution;
no unrestricted scheduler fairness or hardware progress is inferred.

Memory events come from actual local instruction execution. A checked connection
to the restricted relational memory constraints supplies compatible observations
and ordering, with all scope, address, initialization, and dependency restrictions
stated. The interleaving machine itself is not declared to be all PTX behavior.
