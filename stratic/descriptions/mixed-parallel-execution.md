# Cooperating integer and floating-point threads

A cooperating thread array (CTA) is a group of threads that can share a small
memory region and wait for each other at a barrier. This execution layer lets
threads fetch integer, binary32 and barrier instructions from one common
instruction list. Binary32 is the usual 32-bit floating-point format. Each thread
keeps its own registers, predicates and program counter, which identifies its
next instruction. A schedule chooses one thread to take the next step; no
simultaneous or lockstep hardware execution is assumed.

There are two separate lists of memory words: global storage and the group's
shared storage. A memory instruction explicitly selects one of them. The tag
also remains on its trace event, so an access cannot silently change its memory
space. Every emitted access is four-byte aligned and within the selected list;
stores preserve both list lengths. Those facts hold even for a finite execution
prefix that later faults. They do not establish allocation permissions,
initialization, or successful program completion.

A load may use a proposed value. This makes it possible to describe candidate
executions before asking whether PTX's memory rules permit them. A successful
load's address check does not justify its value. This layer currently has no
complete connection from its traces to the permitted memory observations for
several dependent barrier rounds. Treating the current list contents as the
only allowed observations would hide that missing obligation.

A full-group barrier uses resource zero, a named synchronization slot, repeatedly.
Each completed use advances a generation number so that separate uses are not
confused. The first arrival records the instruction site. Waiting threads cannot
fetch another instruction, and later arrivals must match the site and resource.
Completion requires all participants. From a reset barrier, every execution
preserves the invariant that waiting threads remain at the recorded site; hence
release advances all participants from the same instruction. A finite schedule
witness fetches and completes two successive barriers at different sites using
the same resource and successive generations. It proves existence of that
control execution, not scheduler fairness or memory visibility.

The represented barrier discipline requires full participation without early
thread exits. General barriers with explicit participant counts, divergent
barriers, other resources, asynchronous barriers and multiple CTAs interacting
are outside this layer. Initial registers and memory are supplied explicitly.
The selected numerical target check is PTX 9.4 with sm_70 or newer; full GPU
launch limits, register declarations, PTX text parsing and runtime calling
conventions remain separate obligations. Fault and rejected-barrier outcomes
are interpreter results, not assertions about hardware traps.
