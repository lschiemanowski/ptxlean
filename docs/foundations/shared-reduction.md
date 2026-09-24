# A whole-program shared-memory reduction

The kernel adds the first `n` words of a global allocation and stores the result
at word `n`. The result is an unsigned 32-bit modular sum: overflow wraps modulo
2^32. Shared scratch has at least `n` words. Its initial contents and any extra
words are arbitrary. Each of the `n` threads receives its lane ID in register0;
all other initial registers and predicates are arbitrary supplied values.

The source program has labelled blocks. A label consists of a block and its
local instruction index; this makes branch destinations explicit without changing
the meaning of the scalar instructions. Every transition between blocks is a
fetched branch, except the barrier's specified continuation upon completion.

1. Each producer converts its lane number to an address register, doubles it
   twice, and loads the global word at that byte offset. It branches to the shared
   store, writes its actual loaded register value to the corresponding shared
   slot, then branches to the barrier.
2. Every thread executes the one full-CTA barrier, resource0. The canonical
   completion proof derives that all lanes are actually at the common site.
   Nonleaders cannot exit before that barrier.
3. After completion, a real predicate comparison and guarded branch select lane0.
   Other threads execute exit. The leader executes moves initializing its count,
   accumulator and byte cursor; these are not entry assumptions.
4. The leader loops through shared words in increasing address order. Each
   iteration executes a load, modular add, address increment, counter decrement
   and backward branch. PCs therefore repeat. When the counter reaches zero,
   the leader branches to an actual global store and then exits.

`SharedReductionMachine.program` is the fixed fetched instruction program.
`step` selects its current instruction, and `runWith` allows an arbitrary
candidate observation at each dynamic dispatch. Global and shared arenas persist
in the machine state. An individual scalar evaluation sees the selected arena;
its returned memory supplies every writeback. Registers are preserved across
arena selection. The machine is target-neutral; PTX admission uses the separate
ISA9.4/sm_70-or-later qualification proved in `SharedReductionControl`.

`SharedReductionProgram.full_execution` proves the complete concrete schedule
halts every thread and produces exactly `input.set n (total input n)`. It also
proves the shared result is `input.take n ++ scratch.drop n`, with the barrier
reset to generation1. Its premises are positive participant count, nonwrapping
address/counter sizes, and valid initial arena lengths. No desired observations,
source identity, sum, barrier completion or final state are premises.

`SharedReductionTrace.full_accesses` derives the exact memory-only projection of
that actual run: each producer's global load and shared store, then the leader's
`n` shared loads, then one global output store. Values and addresses arise from
executed scalar steps. The equality excludes missing and invented memory events.
The unfiltered trace retains all dynamic occurrence positions, arithmetic,
branches, barrier arrivals/completion and exits. A repeated PC is never a unique
memory-event identifier.

The reusable local-block proofs in `SharedReduction` remain available, but their
staged theorem is not the whole-kernel theorem. `SharedReductionProgram` supplies
the missing fetched transitions, real initialization and register continuity.
`SharedReductionControl` separately establishes that arbitrary reachable barrier
arrivals stay tied to waiting lanes and that an actual release cannot bypass a
lane's earlier computation. Memory projection, source/coherence constraints and
an actual grounded witness are additional layers; the concrete schedule alone
does not establish universal weak-memory correctness.

The model represents all participants of one CTA, one barrier phase and resource,
full-word aligned accesses through the ordinary generic proxy, relaxed GPU-scope
global and CTA-scope shared operations, initialized storage, and no interfering
thread/host/peer-CTA or asynchronous access. Repeated uses of a location retain
its storage identity; global and shared offset0 are distinct. A real launch must
supply eligible geometry, actual lane identities, valid allocation translation
and lifetime. The omitted barrier count means all CTA threads participate; its
explicit-count multiple-of-warp-size rule is not an extra divisibility assumption
on abstract `n`. Concrete32- and64-thread configurations are available. Neither
a finite schedule witness nor a protocol completion-predicate equivalence proves
GPU fairness or a complete warp scheduler.

## Putting the proofs together

Start with `SharedReductionCorrectness`. Its five public entries expose the
contracts without requiring the reader to supply the intermediate invariants:

- `completed_execution` constructs the fetched schedule, exact final global and
  shared storage, all-thread exit, and valid memory graph with a grounding proof.
- `emitted_access_safe` checks every emitted access under arbitrary candidate
  choices and schedules, even when the run does not finish.
- `read_contract` derives the loop's observations from the combined memory
  constraints. Its caller does not select fresh values or identify the intended
  source write.
- `candidate_output` proves that every actual global store writes the modular
  sum to word `n`, for any admitted finite candidate execution.
- `completed_candidate` proves exact final global storage when the actual leader
  exits. All other words are preserved. Termination is a premise of this
  conditional correctness theorem; the separate constructive theorem establishes
  a complete execution exists.

The universal proof passes through actual control and publication history,
computed producer addresses, prior global-load provenance, source compatibility,
barrier ordering, loop address bounds, accumulator arithmetic and persistent
writeback. Each intermediate assumption is discharged by the preceding layer.
See `reduction-{control,history,data,loop,result}.md` and
`shared-reduction-memory.md` for those responsibilities.

The examples show why memory admission matters. For input `[3,5]`, an override
can make the first shared read return an old scratch value `91`. The fetched
program then finishes and writes `96`. Lean checks this actual execution and also
proves that no read-source or write-order choices make its memory graph valid.
Thus a terminating interpreter run alone is insufficient for PTX correctness.
Wrapping arithmetic, preserved scratch tails, 32/64-lane schedules, an incomplete
barrier and a wrong global observation have separate checked examples.
