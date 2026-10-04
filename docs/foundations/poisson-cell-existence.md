# Constructing finite cell executions

The cell's universal correspondence theorem says what every completed,
source-admitted execution computes. An existence theorem answers a different
question: do valid inputs actually have a finite execution in this model?
Neither statement guarantees GPU scheduling progress or hardware conformance.

## The gather prefix

`CellEntry.admitted_prefix_exists` starts with arbitrary global input bytes,
valid connectivity and allocated input/shared storage. It constructs the real
setup and gather instructions for every lane. Active lanes copy their selected
input word; padding lanes skip that work. Every lane then participates in the
first barrier. Release comes from the existing barrier transition after all
arrivals, not from advancing one lane's instruction counter in isolation.

The construction first proves local execution up to instruction 20, before the
barrier. It lifts each local instruction into the concurrent relation while
recording the exact bytes read. A finite lane schedule preserves those records.
The actual barrier round then moves all participants to instruction 21.

`CellEntry.initial_sources` admits the recorded connectivity and input reads.
The prefix has no shared loads and no global writes, facts derived from the
fetched program. Consequently initial-byte sources suffice. The existing
universal gather proof independently identifies each completed lane's result.

## The arithmetic phases

`CellConsumer.Witness.middle_exists` constructs three real arithmetic/barrier
rounds. `arithmetic_exists` appends the final arithmetic phase. These helpers
cover all supported widths, two through five, including padding participants.

The witness runs each lane's phase body in turn. Its read policy uses
`ByteHistory.publish`, a byte view formed by folding the actual recorded stores.
A load takes its bits from this view; a store still modifies the selected
thread's real state and records its actual register value. The helper never
installs a presumed tensor or shared-memory snapshot into that state.

For example, if an earlier lane stores a word at shared address `a`, a later
read's eight bytes can be traced to the recorded store and its byte offsets.
`ByteHistory.origin` selects the latest preceding store covering each byte.
`recorded_admitted` proves compatibility and the necessary barrier-performed
rule. `source_earlier` excludes future sources. These results apply only to the
chosen existence policy; universal correspondence continues to use the weaker
necessary admission conditions. Complete PTX memory admission is not inferred.

The byte helper also handles partial overlaps and distinct address spaces.
Its small overlapping-write checks test that helper alone: the deliberately
unaligned records in those checks are not asserted to be valid PTX executions.
Actual arithmetic access validity still requires aligned eight-byte accesses.

## Why the steps cannot get stuck on an address

The allocation contract states that the coefficient tables and seven shared
planes fit inside aligned, nonwrapping allocations. A symbolic interpreter
tracks only address expressions through the actual instruction list. Loaded
and floating-point values are discarded for this purpose.

A finite certificate checks every active lane and every arithmetic memory
instruction. It gives the address space, aligned offset and complete eight-byte
coverage. `next_valid` combines the certificate with physical allocation bounds
to prove the actual step's access condition. It assumes neither a successful
future trace nor a numerical answer.

`SequenceSafe` traverses the instructions once, retaining the current symbolic
state. `certificate_bounds` proves that this establishes the original
per-instruction contract. The larger certificates are checked a matrix row at
a time and combined into the same universal statement. This limits proof-checker
memory without reducing coverage or trusting a native computation result.

## One complete cell and grid

`CellWhole.exists_recorded` joins the actual prefix to the actual body. It
starts from arbitrary valid input bytes, physical allocations and launch
indices. The continuation receives the prefix's computed registers and byte
publication. Nothing installs a presumed shared tensor into its machine state.

The final branch follows the emitted program. Active lanes execute the two
final contractions, separately rounded addition, output index calculation,
eight-byte store and return. Padding lanes jump past the arithmetic and store
to the same return instruction. `tail_exists_complete` proves the active tail
executes all six instructions. The complete witness ends with every lane halted
and all four collective barrier rounds released.

`CellWhole.Inputs` adds the connection between input bytes and TorchLean:
connectivity, vector contents and coefficient tables represent the specified
operator. It contains no execution, expected result or read-source choices.
`Inputs.exists_corresponding` constructs an actual execution and applies the
universal cell theorem to prove that its published output is the TorchLean
cell action. The output word comes from the actual result register and store.

`InputFamily.exists_grid` repeats this construction for a finite mesh and uses
the existing grid scheduling and source-lifting proofs. Blocks share the global
input memory and output array; each block has private shared storage and
barriers. A serial block schedule suffices to prove existence. It does not
restrict the existing universal result to serial GPU scheduling.

## What remains outside this result

Finite host PCG composition remains an obligation. The accepted solver target is a fresh residual bound for the same
discrete equations. An exact residual certificate is already a separate layer;
it does not by itself prove the PTX execution/host correspondence or convergence
for every input. Necessary byte-source admission, complete PTX admission,
external table serialization, CUDA visibility and GPU conformance remain
distinct claims.
