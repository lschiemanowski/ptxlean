# Reusing shared memory between reduction stages

The cell calculation writes different intermediate arrays. The dot reduction
instead keeps updating the same shared array: 256 lane sums are reduced with
strides 128, 64, 32, 16, 8, 4, 2 and 1. A location can therefore have several
real writers over time, even when one lane owns that location throughout.

The earlier `Compatible` condition checks that a read byte comes from an actual
store or initialization. `Performed` prevents selecting initialization when an
overlapping write precedes the read through a completed barrier. Neither one
alone distinguishes an old store from the current stage's store. That weakness
was harmless for the cell's single-writer planes, but cannot justify the
in-place reduction.

The [repeated-write rules](../../integration/torchlean/PoissonPTX/RepeatedShared.lean)
make the additional obligations explicit. `Before` combines actual same-thread
memory order and the existing `Across` relation, which names a writer's barrier
arrival and the subsequent completion before a reader's access. It closes those
edges transitively. It never treats the chronological interleaving of different
threads as synchronization. In an actual fetched run, the existing barrier
history theorem establishes that completion includes every participant.

`OrderedSources` requires an explicit write-order relation, called coherence.
It requires causally ordered overlapping writes to respect that relation. It
excludes a source that is causally after the read, and excludes a source older
in coherence than a write already ordered before the read. Initialization is
also excluded in the latter case. Only shared accesses enter these extra rules;
the existing general byte-compatibility condition still checks values, spaces,
addresses and actual store provenance.

The selected producer is derived, not built into those rules.
`WritersAround` is a condition on the actual history: every other overlapping
store is before the selected write or after the read. Given that condition and
the selected write's order before the read, `read_from_stage` excludes every
other possibility separately for each byte. All bytes then select the same
actual write, and byte equality gives word equality. No desired load result,
floating-point sum or whole-word atomicity assumption appears in this argument.
The reduction's eventual control/address proof must discharge `WritersAround`.

The [execution regressions](../../integration/torchlean/PoissonPTX/RepeatedSharedChecks.lean)
run a small single-participant block that writes 3, synchronizes, writes 7,
synchronizes, reads, then writes 9. Candidate execution accepts chosen read bits
until source checking. Reading 3 from the first store and reading 9 from the
future store both satisfy the earlier constraints, but fail `OrderedSources`.
Reading 7 satisfies the new constraints. The universal regression also forces
the read to 7 for arbitrary proposed bits and sources.

The [ordering regressions](../../integration/torchlean/PoissonPTX/RepeatedSharedOrderChecks.lean)
show that an unsynchronized store/read pair in different threads has no `Before`
path. A separate actual two-participant execution supplies a cross-thread path
through arrival and completion records. These small blocks exercise the proof
interface; they are not the emitted 256-thread dot kernel.

## Source review and limits

The local NVIDIA PTX ISA 9.4 HTML was checked against the pinned SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The interpretation above follows these sections, paraphrased here:

- [Initialization, §8.2.6](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#initialization)
  supplies an initial write for each byte before threads start.
- [Memory synchronization, §8.9.4](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#memory-synchronization)
  connects participating barrier operations across threads.
- [Causality order, §8.9.5](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-order)
  builds base order from program order and synchronization. For the same
  identity address and generic proxy, that supplies the relevant causal order.
- [Coherence, §8.10.1](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#coherence-axiom)
  makes causal order between overlapping writes constrain coherence.
- [Causality, §8.10.6](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-axiom)
  excludes future sources and coherence-older sources after an ordered write.
- [Barrier instructions, §9.7.15.1](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar)
  describe when prior accesses are performed relative to participating threads
  and when later accesses can be requested.

These are necessary constraints for synchronous shared memory within one block,
with identity addresses, generic proxy and the existing full-participant
barrier interpretation. They are not complete PTX admission: the construction
does not model every coherence restriction, proxy, alias, asynchronous access,
exited-participant case, atomicity rule or dependent no-thin-air requirement.
It also does not convert binary64 accesses into the separate u32 byte-graph
model. The link to NVIDIA is a reviewed interpretation of the pinned text;
Lean proves the implications of the stated definitions.

The 256-thread reduction still needs its emitted instruction representation,
access ownership and stage ordering proofs, exact rounded strided folds and
reduction tree, and a general admitted execution witness. The full solver's
stopping decision and exact-real residual bound remain separate work.
