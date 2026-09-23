# Four separately authored backward kernels

This implementation computes the three sensitivities for a scalar squared-affine
network from an encoded input x, weight w, saved affine value A and incoming
output weight d. The saved value belongs to a cache-free forward computation;
this execution layer accepts its word as input. A later numerical connection must
relate it to the ideal real value x*w+b. No desired gradient or correct saved-value
predicate is assumed to obtain the execution results here.

The instruction sequence is chosen manually, separately from TorchLean's
automatic differentiation. It launches the existing seven-instruction affine
program four times: q=2*d+0, db=q*A+0, dx=db*w+0, and dw=db*x+0. Every stage
performs three bit-preserving loads, one nearest-even multiplication, one
nearest-even addition, one store and explicit exit. Positive-zero additions
remain actual instructions. Each multiplication and addition has its own result
word admitted by the original binary32 relation.

The initialized arena contains x, w, saved A, d, positive-two bits, positive-zero
bits, old dx, old dw, old db and old q, followed by arbitrary extra words. The
four argument lists use byte offsets [16,12,20,36], [36,8,20,32], [32,4,20,24] and
[32,0,20,28]. Intermediate values therefore pass through actual memory between
launches. Old output words are arbitrary. Each launch has its own independently
supplied register and predicate state; only the allocation's stored contents
persist automatically.

Every admitted completed four-launch chain must produce the original four
affine result relations, with the actual q feeding db and the actual db feeding
both dx and dw. Its final allocation contains the exact four stored output words;
inputs, constants and the extra words are preserved. Other allocations are also
preserved. Each stage's final state and seven-event trace follow from its actual
fetched run, and every emitted memory access passes the live allocation checks.
A chain exists for all initial input bit patterns and all four register seeds,
without finite-value or final-output assumptions.

These are execution and correspondence results for the explicitly authored
binary32 program. They do not by themselves establish an error bound relative to the exact
TorchLean-generated sensitivities, and they do not differentiate floating-point
rounding. The numerical bridge must account for saved-forward error and all
eight explicit arithmetic roundings. Constructing the real backward specification
and constructing or verifying this kernel sequence remain distinct activities.

The scope is the serialized one-thread, one-allocation global word arena, PTX
ISA 9.4 and the numeric sm_70-or-later feature condition. Accesses are initialized,
aligned and whole-word, with no interfering host, thread or asynchronous work.
A real runtime must establish completion, visibility, lifetime and argument
correspondence. Thread exit alone does not prove those obligations. This is no
claim about general cross-kernel PTX memory graphs, GPU progress, hardware NaN
realizability, a TorchLean-generated PTX backward, or a full transformer backward.
