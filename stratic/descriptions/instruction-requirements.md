# Instruction and hardware requirements

Instruction eligibility asks whether a particular instruction and its options
are supported by the selected PTX version and GPU. It is checked separately
from storage access and from ordering between threads. A supported instruction
can still be given an invalid address. An unimplemented form is reported
separately from an illegal use of a represented form.

A target records the PTX version and the GPU architecture capability, conventionally
written with an `sm_` number. An instruction form records the options being
checked. The current checker handles scalar 32-bit loads and stores whose kind
of storage is explicit. It checks combinations of storage, scope and cluster
addressing; it is not a parser or a validator for an entire PTX program.

For the represented forms, the checker requires PTX 6.0 and `sm_70` or later for
explicitly scoped relaxed, acquire or release accesses. Cluster scope or cluster
shared-memory addressing requires PTX 7.8 and `sm_90` or later. Scoped forms use
global or shared memory, and cluster addressing uses shared memory. An absent
scope represents the default form with no explicit ordering qualifier, called
weak; it is not an explicit `.weak` spelling.
Which ordering direction applies is supplied by the load or store syntax.

The checker distinguishes three results: supported, illegal with a reason, and
unsupported with a reason. PTX versions beyond the pinned 9.4 version are
unsupported. Stores to device-function parameters, arguments passed to a GPU function,
are also unsupported here; they require calling and storage conventions outside
this fragment. A result of
supported is qualified by the restricted input forms the checker represents.
It does not establish support for unrepresented instructions or options.

A checked example establishes eligibility of the relaxed GPU-scoped global loads
and stores used by the scalar text interface on PTX 9.4 with `sm_90`. That result
does not establish compilation, address safety or correspondence with a physical
GPU. Connections to execution retain these as separate obligations.
