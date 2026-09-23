# A backward implementation with its own proof

The reference network is F(x,w,b)=(x*w+b)^2. TorchLean automatically constructs
its exact real backward computation. For an incoming output weight d it returns
input, weight and bias sensitivities (2*d*A*w, 2*d*A*x, 2*d*A), where A=x*w+b.
The code verified here is selected separately. It is a small numerical backward
implementation whose stored outputs must be proved close to that actual reference.

## Five explicit launches

There are ten explicit arithmetic roundings across the five launches.
Each launch reuses the seven-instruction affine program: three whole-word loads,
a rounded binary32 multiply, a rounded binary32 add, a store of the result bits
and explicit exit. The initial ten-word arena is:

| Word index | Byte offset | Initial purpose |
|---|---|---|
| 0 | 0 | input x |
| 1 | 4 | weight w |
| 2 | 8 | bias b, then recomputed saved A |
| 3 | 12 | incoming output weight d |
| 4 | 16 | positive two, encoding 0x40000000 |
| 5 | 20 | positive zero |
| 6 | 24 | arbitrary old dx bits |
| 7 | 28 | arbitrary old dw bits |
| 8 | 32 | arbitrary old db bits |
| 9 | 36 | arbitrary old q bits |

Extra words follow this layout and are preserved. The request sequence is written
explicitly; it is not obtained by compiling TorchLean's automatically generated
backward graph:

| Launch | Input/bias/output byte offsets | Stored computation |
|---|---|---|
| Recompute | 0,4,8,8 | A=round(round(x*w)+b) |
| Scale seed | 16,12,20,36 | q=round(round(2*d)+0) |
| Bias sensitivity | 36,8,20,32 | db=round(round(q*A)+0) |
| Input sensitivity | 32,4,20,24 | dx=round(round(db*w)+0) |
| Weight sensitivity | 32,0,20,28 | dw=round(round(db*x)+0) |

The first launch reuses the bias slot safely: it loads the bias before writing A.
The last four launches use that saved value, the same q word and the same db word.
Registers are assembled independently for each launch from arbitrary supplied
banks; no result is silently passed through a previous launch's registers.

This is a recomputing backward implementation. It does not perform a full forward
invocation that returns F's squared value, because the backward only needs A.
There is no KV cache. It is deliberately simple, with five launches and explicit
zero additions; it is not an optimized training implementation.

## A concrete checked run

With x=2, w=3, b=1 and d=2, recomputation produces A=7. The following launches
produce q=4, db=28, dx=84 and dw=56. The final gradient observation is ordered
(dx,dw,db)=(84,56,28), matching the actual checked TorchLean example.
The original old gradient/q bits and incoming register values need not be zero.
The example is about actual instruction executions and exact writeback, rather
than evaluating only the derivative polynomial.

## Saved values are conclusions

The general correctness statement begins with finite interpretations and input
errors for the encoded x,w,b,d words. Two initial range guards establish finite
recomputation. Its actual instruction results establish the saved word's value
R=round(round(xh*wh)+bh), and the existing affine theorem bounds its difference
from ideal A. Neither a correctly computed saved value nor its provenance is
assumed.

The [backward arithmetic guide](backward-affine-errors.md) explains the next
four stages' bounds. Its guards use R and the initial finite seed/operand values;
they do not assume that a returned gradient is finite. Its saved-value promise
is discharged by the actual first launch. The final proof follows exact memory
handoff through all five launches and applies the numerical results to the
three words actually stored at offsets 24, 28 and 32.

The [gradient observation interface](gradient-storage-view.md) decodes those
words into an actual TorchLean scalar tensor pack and states separate absolute
bounds for its three components. Its reference is the graph's actual generated
VJP. The checked reference call succeeds by its own theorem. Nonfinite words
cannot pass as real zeros, and real-value comparison does not identify bit
encodings: the interface explicitly preserves the distinction between signed
zero words with the same real value.

## What is and is not established

The actual instruction semantics, fixed layout, exact store handoff and finite
chain construction establish this restricted implementation's correctness and
execution existence. Existence applies to arbitrary initial bits, whereas the
real-valued error guarantee needs the numerical input conditions. The derivative
meaning comes from the actual upstream graph and its local derivative proofs.
These are separate ingredients, each checked in Lean.

The runtime contract still requires completed, visible memory between serialized
launches and exclusion of interference. A thread exit alone does not establish
that contract. The example uses one thread and one logical global allocation,
initialized aligned whole words, nearest-even binary32 operations with gradual
underflow and numeric sm_70+ features under PTX ISA 9.4. There is no physical
pointer/launch ABI proof, cross-kernel memory graph or hardware-conformance proof.

This is one scalar backward example. It does not establish arbitrary TorchLean
graph lowering, general training losses, mixed-precision policy, useful bounds
for an entire network, bitwise PyTorch agreement or a Gemma backward. Those
broader responsibilities remain explicit in Stratic.

Reproduce with `./scripts/check.sh` and `./integration/torchlean/check.sh` from
the repository root. The integration audit includes the numerical, gradient-view,
actual four-stage pipeline and recomputing-prefix endpoints. Independent reviews
check the proof statements and semantic boundaries separately from compilation.
