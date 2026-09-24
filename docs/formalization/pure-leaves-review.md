# Selection and signed minimum/maximum review

The coordinator reviewed the exact Luna candidates against the locally pinned
PTX ISA 9.4 source, independently of the worker's proof claims. The manual hash
is `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The accepted patches and their independent replay receipts are recorded separately
in `formalization/results/select32` and `formalization/results/signed-minmax32`.

## Source correspondence

The [selection section](../../references/nvidia/ptx-isa-9.4/index.html#comparison-and-selection-instructions-selp)
specifies that a true predicate copies the first source and a false predicate
copies the second. The selected `selp.b32` leaf copies complete words without
numeric conversion. Its selector is a predicate register, separate from the
positive or negative instruction guard. The leaf deliberately excludes negated
selector syntax, other widths/types, raw-text parsing and register declarations.
It accepts two word registers or already-decoded immediate words, one destination
register and one positive predicate selector. The section was introduced in
PTX 1.0; its special `sm_13` restriction applies to `.f64`, not this `.b32` slice.
Section SHA256: `8781e1d81a058fbac02e290afeca05c1a45ea6f12c8e9bdcabbde18a5dc75347`.

The [minimum](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-min)
and [maximum](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-max)
sections distinguish signed from unsigned comparison. The scalar `.s32` leaves
compare `BitVec.toInt` and return an unchanged source word. All bits, including
negative values and both endpoints of the signed range, are admitted. Equal
values select the second source, consistent with the source's strict comparison;
equal signed values have the same bits. The universal `compute_toInt` theorem
relates the result to integer minimum/maximum without a range assumption.
These forms were introduced in PTX 1.0 and have no extra target restriction;
`.relu`, packed lanes and other widths are separate excluded forms.
Section hashes are `a9ce7fb6368d2ec29f4f4ff171e57f234b1f8908c7da69f0dcc91b16de1ee5f2`
and `44e15ff2f0031099a1a4cdb8d7601e21689dfb7976e243550b1a6f3777989eb3`.

For both leaves the target predicate selects ISA 9.4 and a numeric feature floor
of `sm_10`. It is not a recognized target-name validator and does not claim a
modern assembler accepts obsolete targets. The caller supplies type-compatible
register declarations and decoded immediates. Instruction guards, incoming-source
reads and single-destination behavior agree with the common operand/predication
sections pinned by the instruction ledger. Syntactic read metadata preserves
all operands and repeats; it is not a PTX semantic-dependency calculation.

## Proof and execution review

Both leaves use `Pure32.Family.ofFunction`, exact lowering and abbreviations of
`Pure32.Eval` and `Pure32.Step`. They do not add a second interpreter. Lowering
preserves guard, destination, operation, operand order and selector polarity.
Enabled execution reads the incoming state, writes only the destination and
advances PC. Disabled execution advances PC, emits guard-only read metadata and
has no writes or memory effect. Aliasing needs no inequality premise.

Fetched-step origin recovers the original leaf at the actual PC from the mapped
program. The proofs transport the shared evaluation across equality of the
lowered instruction; they do not assume the desired result or chosen instruction.
The target condition is checked even for a false guard. Missing fetch is rejected,
not treated as kernel termination. Existence is one-step existence for every
supplied state, not whole-program termination or hardware conformance.

The coordinator inspected the source and all public proof statements. Fresh
replay checks the frozen universal signatures, source-specific arithmetic and
text outcomes, frames, aliases, repeated operands, both guard polarities,
nonzero-PC fetch, target exclusion and malformed/unsupported text. Named theorem
and definition dependencies are inspected separately; only standard Lean axioms
are admitted. Passing these checks substantiates this restricted formalization;
it is not proof of general PTX coverage or a hardware correspondence theorem.

## Preserved evaluator repairs

The original v1 drivers remain unchanged. Candidate-only elaboration exposed
ambiguous names from opening both Ptx and Scalar, insufficient Fin-index type
annotations and concrete `by decide` uses for a proposition whose public
interface did not require a Decidable instance. V2 qualifies names, annotates
those indices and unfolds the concrete target/family definitions in proofs.
Every asserted proposition and expected outcome is unchanged. Failed original
replays and both driver versions are retained. These are coordinator evaluator
defects, distinguished from the worker's earlier incomplete proofs.

The selection candidate passed after one model repair; the signed candidate
after two. Coordinator feedback identified ordinary conjunction/equality
transport and tactic sequencing errors. Reviewers did not edit the leaf sources.
The two tasks consumed five headless calls, bringing the campaign to fourteen;
this is an assisted development demonstration, not a held-out success rate or
cost-effectiveness estimate. Raw usage remains per receipt because resumed-session
counters may be cumulative and no billing amounts were returned.

## Independent defect probes

Both unchanged candidates pass their drivers. The selection probe changes only
unsupported-name error classification. The signed probe raises the feature floor
to `sm_20`. Each altered module still compiles with completed proofs and an
allowed-axiom audit, but its unchanged v2 driver rejects the altered behavior.
The exact diffs, commands and diagnostics are retained in each result directory.
These two observations demonstrate detection of those defects only; they do not
establish completeness or a statistical sensitivity of the review process.
