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

[completed_arithmetic](../../integration/torchlean/PoissonPTX/CellConsumerOutput.lean)
takes a completed middle execution and its continuation from the same state at
the existing last barrier. Both are executions of fetched instructions. A lifting
lemma embeds the middle run into the extended program, and `combined` joins the
runs without inserting a new barrier or replacing memory.

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

`stored_local` then applies the existing fetched integer-index, global-store and
return proof to this **actual concurrent result state**. Its input is no longer
a manufactured shared-memory snapshot. The output location must satisfy the
existing alignment and allocation conditions; the fetched tail has an independent
execution-existence theorem under those conditions.

## The precise remaining boundary

The concurrent fragment stops after the addition. The index/store/return tail
still runs in the separate fetched model. We have not yet incorporated those
global stores into the concurrent machine or proved their interleaving with other
threads' final reads. In this arithmetic fragment, padding lanes jump to the
arithmetic cutoff; the actual skipped tail and return require the full-kernel
connection.

The theorem is supplied with the actual cut at the last barrier. Extracting this
cut automatically from every complete kernel execution is also still an
obligation. No extra synchronization is assumed or added. Prologue/gather, full
launch and host composition, complete PTX memory admission, arbitrary-input
execution existence and GPU progress retain their separate boundaries.

## Reproduce the checks

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_poisson*.py'
```

`CellConsumerChecks` gives a completed zero-data Q1 execution with 32 threads,
including 28 padding lanes. Its actual loads and stores satisfy the single
whole-history source assignment, and the main theorem supplies its result.
This establishes nonvacuity, not general termination. A changed final addition
fails the symbolic numerical certificate. Existing asymmetric nonzero final-body
examples and saved-PTX bindings provide separate regression evidence.

The emitted PTX has not changed. The existing frontend binds the same middle
bodies, guards, barriers and final arithmetic used by these proofs, and separately
binds the fetched output tail. Its receipt remains a checked text connection,
not a verified parser or hardware-conformance theorem.
