# Reduction publication history

Each thread publishes to shared memory at most once before reaching the common
barrier. A thread's actual arrival is preceded by its own actual shared store;
barrier completion is preceded by every participant's store and arrival. Every
later leader shared load follows that actual completion. These are statements
about the emitted execution trace, including arbitrary scheduling and candidate
read values, not assumptions that reads are fresh or that the sum is correct.

The proof tracks forward control progress through the producer, publication,
barrier and continuation blocks. A count of actual publication events agrees
with whether a lane has passed its publication instruction. Repeatedly scheduling
a waiting or exited lane cannot publish again. Completion history connects
continuation blocks to an emitted completion, rather than interpreting a block
name as evidence that synchronization happened.

Addresses and stored values need separate data-flow proofs: this child records
which thread issued a store and its order relative to arrivals, completion and
loads. The memory adapter combines those actual-history facts with address
identity, source compatibility and PTX ordering constraints. No desired read
value, final output or memory freshness is an invariant premise.

The same single-CTA, single-resource, single-site, no-pre-barrier-exit slice and
outside-interference exclusions apply. A finite trace-order result is not a
fairness claim or a model of arbitrary divergent warp barriers. Dynamic trace
positions, rather than repeated program counters, distinguish loop occurrences.
