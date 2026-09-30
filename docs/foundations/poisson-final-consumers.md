# Why the final threads see the middle results

The middle phases produce shared matrices S5 and S6. The final phase reads those
matrices and computes `S5 D + S6 B`. A store alone does not establish that another
thread sees it. The proof must identify the executed store, the intervening
barrier and the actual load's permitted byte sources.

The concurrent arithmetic extension does this in one execution history. It does
not replace the load instruction by “read the expected tensor value.” Candidate
loads still choose arbitrary words; the source constraints rule out inappropriate
choices. The initial shared input and entry registers remain the same explicit
conditions as for the middle slice.

## The theorem's input and result

[completed_run](../../integration/torchlean/PoissonPTX/CellConsumerRun.lean)
takes one execution of the concurrent arithmetic fragment. It recovers the
middle prefix and its continuation automatically. No intermediate state or
prearranged schedule is supplied, and no extra barrier is inserted.

Here is why the split exists. Initially every thread is before the last middle
barrier. Guards cannot jump past it. The first step that puts any thread beyond
it must therefore release that barrier. At this release, all participants are
at the same barrier instruction, so all move to the instruction immediately
after it. The steps up to and including that release form a completed middle
execution; the remaining steps form its continuation. This argument works even
when only the output thread being examined has finished final arithmetic.

The reusable [split_run](../../integration/torchlean/PoissonPTX/ConcurrentCut.lean)
lemma proves this for any prefix ending in a protected barrier in the current
concurrent model. Here “protected” means every earlier branch lands no later
than the barrier; the Q1–Q4 instruction certificates establish that condition.

One byte-source assignment must satisfy the necessary `Compatible` and
`Performed` constraints on the entire event history. Compatibility says that each
read byte comes from initialization or a matching executed store. The barrier
constraint excludes initialization when a matching shared write has been
performed before that read. These remain necessary conditions, not the full PTX
memory model.

For every active coordinate whose final arithmetic completes, the actual register
holding its result equals TorchLean's ordered binary64 local cell calculation:

```
Bᵀ (W ⊙ ((B U) Dᵀ)) D + Dᵀ (W ⊙ ((D U) Bᵀ)) B
```

B and D are the basis and derivative tables; W contains integration weights;
U is the initial shared input. `⊙` multiplies corresponding entries, and `ᵀ`
swaps rows and columns. Parentheses and increasing inner indices fix the rounded
operation order. The proof concerns decoded floating-point values and retains
freedom in NaN bit encodings.

## How the memory connection is proved

1. **Find the final reads.** Kernel-checked certificates for Q1–Q4 track addresses
   while discarding loaded values. Every final shared read addresses plane 5 or
   6 after the last barrier. Padding threads skip the arithmetic.
2. **Find the producer.** The actual program's store coverage and forward control
   establish a unique writer and actual store event at that word address.
   Barrier arrival and completion provenance order that store before the read.
   Every read byte must therefore come from the producer's recorded word.
3. **Use one memory history.** The continuation contains no stores. It cannot
   create a new source for an earlier middle read. The proof derives the middle
   prefix's source constraints from the whole-history assignment, rather than
   assuming two independently valid but potentially unrelated assignments.
4. **Follow the arithmetic.** Symbolic instruction soundness connects the actual
   loads and registers to the two ordered products and final addition. Substituting
   the proved middle-plane equations gives the complete local cell formula.

`stored_run` then applies the existing fetched integer-index, global-store and
return proof to this **actual concurrent result state**. Its input is no longer
a manufactured shared-memory snapshot. The output location must satisfy the
existing alignment and allocation conditions; the fetched tail has an independent
execution-existence theorem under those conditions.

## The precise remaining boundary

The arithmetic fragment described above is now the target of a proved
[execution projection](poisson-concurrent-output.md). A combined concurrent
machine executes the index/store/return tail while other threads continue,
and padding lanes branch to the real return. Its arithmetic run, retained
event positions and result-register relation are derived.

[Output-store separation](poisson-output-separation.md) preserves retained
read sources. Actual store bounds now follow from launch registers, and completed active
lanes' byte memories contain their TorchLean values. The combined proof derives
their actual store records and publishes them into one global TorchLean output
tensor independently of merge order; CUDA host visibility remains separate.

The automatic split is proved for this arithmetic fragment. Applying it inside
a complete emitted-kernel correspondence still requires the omitted instructions
and their control and memory effects. Prologue/gather, full
launch and host composition, complete PTX memory admission, arbitrary-input
execution existence and GPU progress retain their separate boundaries.

## Reproduce the checks

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_poisson*.py'
```

`CellConsumerChecks` gives a completed zero-data Q1 execution with 32 threads,
including 28 padding lanes. Its actual loads and stores satisfy the single
whole-history source assignment, and the single-run theorem supplies its result
without accepting the witness's preconstructed middle/final split as an input.
This establishes nonvacuity, not general termination. A changed final addition
fails the symbolic numerical certificate. Existing asymmetric nonzero final-body
examples and saved-PTX bindings provide separate regression evidence.

The emitted PTX has not changed. The existing frontend binds the same middle
bodies, guards, barriers and final arithmetic used by these proofs, and separately
binds the fetched output tail. Its receipt remains a checked text connection,
not a verified parser or hardware-conformance theorem.
