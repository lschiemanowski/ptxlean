# Independent review of the recomputing backward implementation

No blocking implementation, statement or proof issue was found. Reviewed source:
`integration/torchlean/PtxAffineBackward.lean`, SHA-256
`51f2494ffedeba8f9f6d83dd5c6d2fcfbac9620e8c789ff8f47e59c7877d68f4`.
The directly inspected four-launch dependency `PtxBinary32/BackwardPipeline.lean`
has SHA-256 `6173bf79baa3a8898c5245bb1122d24ad395a31fd39c2edde1723e840be8c582`.
The previously reviewed numerical and observation dependencies remain unchanged:
`BackwardError.lean` at `f455c4088698b29df46a173c456834bdb48496d9707c924db868489c73030531`
and `PtxGradientView.lean` at `921ee67ea0f310628ae93502c96f7724b60f1d3c347945f204130d61f37353a8`.

## Actual execution and stored-value provenance

The initial `Data.saved` field is the bias input in this wrapper. This naming
is inherited from the reusable four-stage backward layout; it is not a premise
that a saved activation already exists. The recomputation arguments are byte
offsets 0,4,8,8. Input x, weight w and bias are loaded before the store replaces
the bias slot with the new activation. `recompute_initial` establishes alignment
and bounds for the ten-word prefix independently of arbitrary extra words and
register seeds. The underlying `Affine.run_iff` permits valid address aliases
and characterizes the actual fetched loads, arithmetic, store and exit. Thus the
bias/output alias is justified by load-before-store execution, not an unproved
assumption that disjoint inputs survive.

`recompute_run_iff` derives the original encoded affine result relation, exact
final state and trace. `recompute_memory` changes exactly the selected slot.
`recompute_correct` joins that run to the actual launch's identity-preserving
writeback. There is no arbitrary postcondition standing in for execution.

`pipeline_correct` eliminates the first actual launch, passes its exact stored
cell to the existing four-stage pipeline, and derives all ten rounded arithmetic
results plus exact final allocation contents. The four later stage layouts
preserve x, w, seed, constants and saved activation while writing q, db, dx and
dw. Both final branches read the same actual db word; they do not independently
recreate an ideal sensitivity. `withSaved` and `outputData` retain the arbitrary
tail. Other allocations are explicitly preserved by `pipeline_other_allocation`.
Generic `SuccessfulLaunch` access safety applies to every emitted memory event.

`pipeline_exists` constructs five actual terminating launches for arbitrary
encoded x, w, initial bias and seed, arbitrary old result bits, arbitrary tails,
and independently supplied register banks. Its premises are the live correctly
owned initialized arena and target eligibility, not finite values, a desired
result or numerical accuracy. Conservative NaN-envelope nonemptiness is used
at the arithmetic boundary; this is modeled execution existence, not evidence
that every included NaN payload is physically realizable.

## Numerical and generated-backward correspondence

`results_approximate` derives the recomputed saved word's finite real value
R=round(round(xh*wh)+bh) and its error relative to ideal x*w+b. The two
recomputation guards depend on initial finite interpretations. The subsequent
`BackwardError.Guards` use that explicit R expression and initial xh, wh and dh,
not actual intermediate words whose finiteness should be proved. The proof
propagates the derived activation error through the four selected affine stages,
including their actual zero additions. The complete implementation has ten
rounded arithmetic instructions, not a fused or idealized derivative evaluation.

`stored_backward_approximation` obtains both numerical result relations from
the given actual chain; they are not theorem premises. It then relates the exact
stored dx,dw,db words to the actual TorchLean `graph.vjpWithSeed`. Budget order
is correct: the input-gradient bound uses w and its representation error, the
weight-gradient bound uses x and its error, and the bias-gradient bound is the
shared base bound. The conclusion also exposes `vjpChecked` success through
the proved upstream graph result. There is no assumed AD success, correct saved
activation, saved error, encoded result relation, or final approximation premise.
Initial finite interpretations, input/seed representation errors and sufficient
range guards remain genuine numerical conditions.

`five_launch_example` constructs a real five-launch chain with x=2, w=3, b=1,
d=2. Kernel reduction checks the explicit encoded arithmetic: A=7, q=4, db=28,
dx=84 and dw=56. The final stored cell is the claimed one. The proof is universal
in the incoming register banks and old output bits; it does not merely evaluate
the ideal derivative polynomial.

## Independent checks and scope

Fresh `lake --no-cache env lean PtxAffineBackward.lean` passed without warnings
or errors from the integration package. An independent inventory found all 21
public declarations: `Data`, nine definitions and eleven theorems. An independent
import driver produced exactly 21 `#print axioms` reports; the established audit
accepted only `propext`, `Classical.choice` and `Quot.sound`. The forbidden-token
scan passed and the source hash was unchanged after checking. Full reports are
in [recomputed-affine-backward-audit.txt](recomputed-affine-backward-audit.txt).

The Stratic description and study guide match the scope. They correctly describe
a separately selected recomputing backward, rather than automatically generated
PTX or a full forward invocation returning the square. The interpretation of
serialized transitions still requires external runtime completion, visibility,
lifetime and interference guarantees. Thread exit is not used to prove those.
This is one thread, one initialized aligned whole-word global allocation and
nearest-even binary32 with gradual underflow under the selected ISA/target
boundary. There is no general cross-kernel memory graph, physical ABI, arbitrary
network compiler, floating-point differentiation, bitwise PyTorch agreement or
hardware-conformance claim. No source changes or weakened specifications were
needed for this review.
