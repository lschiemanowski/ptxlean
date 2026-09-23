# Independent review of the two-kernel squared-affine example

Reviewed source: [PtxAffineSquareKernel.lean](../../integration/torchlean/PtxAffineSquareKernel.lean),
SHA-256 `0f62552dc611aaf5ddf767a046e11ff873003b9d9106abb9be8d043226105626`.
The reviewer made no source or shared-configuration edits. No independent
semantic or proof blocker was found for this exact module.

This review uses the independently reviewed [affine execution](affine-kernel-proof-review.md),
[serialized launch](serialized-launches-review.md) and
[squared-affine error](squared-affine-error-review.md) contracts. The reviewer
authored the generic storage and affine memory-graph components; their separate
independent reviews are the coordinator's responsibility. The current module and
its launch/numerical connections were authored separately from this review.

## Memory layout, aliases and independent launch state

The entry arena is exactly `[x, weight, bias, oldIntermediate, positiveZero]`
followed by an arbitrary tail. The three encoded inputs, old intermediate bits
and tail words are arbitrary. The fifth entry is deliberately the positive-zero
input to the second kernel, not an arbitrary old output word.

The first argument vector selects byte offsets `[0,4,8,12]`. The second selects
`[12,12,16,16]`: both multiplicands alias the first kernel's saved intermediate,
and the positive-zero bias aliases the second output. The existing affine
execution loads all three operands before its store, so both aliases are handled
without a new distinct-address assumption. `first_initial` and `second_initial`
derive address validity from the displayed layout, for every tail.

The two seeds are independent parameters containing arbitrary value registers,
address defaults and predicates. Each request constructs a new state at PC zero
through the existing argument binder. No first-launch register value is silently
carried into the second launch. Their equality is not prohibited either: fresh
state means explicit assembly, not a requirement for different bit patterns.

## Universal execution and exact handoff

`first_run_iff` and `second_run_iff` specialize the actual affine run
characterization. Each conclusion identifies both numerical result relations,
the exact final scalar state and the complete seven-event trace. They do not
replace the interpreter by an arithmetic function or choose a reference result
for the universal claims.

`launches_correct` first obtains the actual first run from the caller-known live
cell. It then derives the middle cell from that run's exact writeback. Only after
proving this saved-memory equality does it obtain the second run from the middle
cell. This is the important data connection: the second relation consumes the
actual stored intermediate word twice, rather than an assumed real value or a
register left over from the first execution.

The theorem derives both exact traces and states, both storage updates and all
four admitted arithmetic results. The first launch changes only the intermediate
slot; the second changes only the output/zero-bias slot. `outputMemory` retains
all initial inputs and the arbitrary tail. `pipeline_frame` additionally
preserves every other logical allocation. `pipeline_correct` obtains the same
word-level relation and final cell for every admitted completed two-launch chain.

## Existence and the concrete fixture

`pipeline_of_results` is explicitly a construction lemma given four admitted
arithmetic results. The public `pipeline_exists` discharges that premise by
constructing four numerical relation members for arbitrary input bit patterns.
It then constructs actual halted runs and both writebacks. No finite-input,
correct-output or convenient-intermediate premise is smuggled into existence.
The live initialized cell and eligible target remain explicit conditions.

`two_launch_example` instantiates the complete construction, for arbitrary two
seeds, with x=1.5, weight=2 and bias=0.25. It derives first product 3.0, saved
intermediate 3.25, square 10.5625 and the same final value after explicit positive
zero addition. The final output encoding is `0x41290000`. Each fixed bit result
requires kernel conversion of the numerical reference when applying
`envelope_self`; the proof is not merely symbolic reference membership. The
conclusion contains an actual two-launch chain and the exact final stored cell.

Successful launches terminate by their actual fetched affine `exit` instructions.
They are not incomplete finite prefixes. The already reviewed affine control
proof supplies six advancing steps followed by exit for each invocation. This
module constructs neither a hardware scheduler nor an asynchronous completion
protocol.

## Numerical result and the actual TorchLean target

`stored_forward_error` first extracts the actual four words from
`pipeline_correct`. It applies `SquareError.results_error` to precisely those
words and retains the equality identifying the final cell's output slot. Its
conclusion is therefore about the real interpretation of the word actually
stored at byte offset 16.

The first two guards constrain multiplication and addition using only the finite
interpretations of the initial encoded inputs. The second pair uses the explicit
initial-input expression
`R = fp32Round (fp32Round (xh*wh) + bh)`.
The earlier numerical proof derives the actual intermediate's interpretation as
R; the pipeline does not assume that result. The later guards constrain `|R*R|`
and `|R*R| + eps32(R*R)`. Neither a finite square nor a desired final value is a
premise.

All four actual roundings are retained: multiply/add in the producer and
multiply/positive-zero-add in the consumer. The inherited error budget includes
both consumer rounding allowances, `2*|A|*E` and the quadratic `E*E` propagation
term, where A is the ideal affine value and E its first-stage error bound.

The final comparison is directly with
`Tensor.item (AffineSquareVJP.graph.forward (AffineSquareVJP.inputs ...))`.
The reviewed `forward_value` specialization identifies this actual pinned
TorchLean graph with the scalar polynomial. The graph is built from the existing
`affineSquare` graph and converted through the upstream typed-graph interface;
it is not an unrelated local numerical function with the same displayed formula.
This review checked that forward dependency. The full generated VJP has its own
[independent review](affine-square-vjp-review.md). No PTX backward implementation,
rounded-execution derivative or PyTorch bitwise correspondence is claimed here.

## Lifetime and runtime boundaries

`second_launch_after_release_rejected` uses the reusable lifetime theorem after
an arbitrary valid history of subsequent storage operations. It excludes revival
of the old allocation identity, even following a same-size replacement. It does
not merely check the immediately freed state or assume that no later allocations
occurred.

The semantic interpretation remains one thread and one live initialized global
word arena per launch, ISA94/sm70 eligibility, compatible bit-register operands,
explicit nearest-even arithmetic and no interfering work. Runtime waiting,
write visibility, identity-preserving argument translation and allocation
lifetime enforcement are external correspondence obligations. They are not
derived from PTX thread exit or memory scope. Per-launch graph witnesses use
entry snapshots; no combined cross-kernel PTX memory graph or fresh physical
initialization writes are asserted. The conservative NaN envelope does not
establish hardware realizability of every admitted NaN payload.

The Stratic description and study guide were checked against these boundaries.
They accurately separate arbitrary-bit execution existence, finite real accuracy,
actual modeled instructions, ideal TorchLean meaning and runtime correspondence.

## Independent mechanical checks

Run from `integration/torchlean`:

```text
lake env lean PtxAffineSquareKernel.lean
lake env lean /tmp/affine-square-kernel-independent-audit.lean
```

Fresh source elaboration passed without warnings. The independent audit
inventoried all 23 explicit public definitions and theorem declarations, matched
every reported name against that inventory, and checked multiline dependency
reports. The [complete audit](affine-square-kernel-audit.txt) contains the exact
names for registration. Only `propext`, `Classical.choice` and `Quot.sound`
appear; no new unchecked axiom or proof hole was found. The source hash was
rechecked after the audit and remained unchanged.
