# A complete reference softmax forward pipeline

The pipeline computes stable softmax for a nonempty row of encoded binary32
scores. It uses the existing parallel maximum and sum programs and sequential
passes for exponentiation and normalization. This is a reference composition,
not an optimized parallel softmax implementation.

The numerical goal is the pinned TorchLean tensor operation
`Activation.softmaxVecSpec (Tensor.ofFn scores)`, where each score is the exact
real value of its original stored word. Rounding and approximation mean that
the encoded outputs need not equal these ideal values bit for bit.

## Follow the same memory through every phase

For n=2^depth scores, allocate 2*n+2 global words. Initially they contain

```
[ score_0, ... score_(n-1) | one, ... one | zero | zero ]
```

The n unit weights and zero bias let the existing dense kernel implement the
sum without duplicating its synchronization and memory proofs. They remain real
loads and arithmetic instructions, not operations erased by the proof.

1. **Maximum.** The parallel reduction reads the score prefix and stores an
   attained maximum at index n, temporarily overwriting the first unit weight.
   All other global cells are proved unchanged for every completed admitted run.
2. **Exponentials.** A sequential pass handles each index i. Two fetched loads
   read score_i and the stored maximum. Four arithmetic instructions compute the
   shifted exponential, and a fetched store overwrites cell i. Later steps cannot
   change an earlier result; the maximum at n remains intact throughout.
3. **Restore the weight.** One fetched store writes encoded positive one at n.
   The resulting actual arena is proved equal to the sum kernel's required layout.
   No host operation constructs an exponential vector to substitute for these
   stored results.
4. **Sum.** The parallel unit-weight reduction stores its denominator at 2*n+1.
   It preserves the exponential prefix and all other constant cells.
5. **Normalize.** Each sequential step loads one exponential and the stored
   denominator, executes `rcp.rn.f32` and `mul.rn.f32`, and stores the result back
   to its prefix cell. The denominator is outside the overwritten prefix.

For two scores, the memory shape is especially easy to follow:

```
initial:      [ x0, x1, 1, 1, 0, 0 ]
maximum:      [ x0, x1, m, 1, 0, 0 ]
exponentials: [ u0, u1, m, 1, 0, 0 ]
restore:      [ u0, u1, 1, 1, 0, 0 ]
sum:          [ u0, u1, 1, 1, 0, S ]
normalize:    [ y0, y1, 1, 1, 0, S ]
```

Here u0 and u1 range over the instruction model's permitted approximate results.
The proof covers each permitted arithmetic outcome of each completed pipeline;
it does not replace exponentiation with one deterministic reference choice.

## What the execution proof means

Each parallel phase contains an actual fetched run, completed threads and an
admitted memory graph. Separate theorems construct such runs and expose their
safe access traces. The sequential stages execute the existing scalar memory
operations against the current arena with no competing writer. Their byte
addresses are four times their word indices. Validity requires both an allocated
word and index less than 2^62, so conversion to a 64-bit address cannot wrap.

The pipeline target is PTX 9.4 and SM 7.0. The scalar arithmetic stage components
also support the weaker SM 2.0 threshold inherited from their instruction leaves.
Each elementwise stage uses registers 0 and 1 for loaded operands and register 2
for arithmetic scratch, preserving other registers, address registers and predicates.

Finishing a stage and starting the next is an explicit operation of the
composition model. Entry state and reduction scratch are initialized there.
These boundaries perform no softmax arithmetic. They are not a CUDA allocator,
runtime launch implementation, device-visibility proof, or single fused kernel.
The sequential passes do not claim arbitrary concurrent read observations.

## Existence and accuracy are separate

The row length is a power of two up to 1024. Original scores must be finite and
have magnitude at most 2^124. These conditions establish that the exponential
instructions receive supported nonpositive finite arguments. The pipeline's
existence theorem constructs every phase without assuming the desired final
answer or intermediate successful execution.

Accuracy needs an additional guard. For maximum m, let delta_i be the proved
shifted-exponential allowance derived from original score_i and m. Let
`sigma=(n-1)/8192` bound rounding in the sum and `D=sigma+sum(delta_i)`.
Under `D<=1/2`, the denominator is at least one half. This derives finite reciprocal
and product results rather than assuming them. The guard depends only on the
original scores and their maximum. Equal-score rows satisfy it at every supported
size, so the condition is not vacuous.

Writing u_i for the real value of the actual stored exponential and S for the
real value of the actual stored sum, each output is
`round32(u_i*round32(1/S))`. With `rho=eps32(1/S)` and
`tau_i=eps32(u_i*round32(1/S))`, its absolute error against TorchLean's ideal output
is at most

```
tau_i + (1+delta_i)*rho + (delta_i+D)/(1-D).
```

The sum of these coordinate allowances also bounds departure of the computed
row sum from one. Exact positivity of computed outputs is not promised: the
conservative exponential relation can permit tiny negative values near zero.

## Read the proof in layers

- [SoftmaxMemory.lean](../../integration/torchlean/PtxBinary32/SoftmaxMemory.lean): actual fetched load–arithmetic–store stages.
- [SoftmaxSweep.lean](../../integration/torchlean/PtxBinary32/SoftmaxSweep.lean) and [SoftmaxStorage.lean](../../integration/torchlean/PtxBinary32/SoftmaxStorage.lean): preservation between sequential invocations.
- [SoftmaxReductions.lean](../../integration/torchlean/PtxBinary32/SoftmaxReductions.lean): admitted parallel reductions and exact whole-arena changes.
- [SoftmaxPipeline.lean](../../integration/torchlean/PtxBinary32/SoftmaxPipeline.lean): the complete memory-connected execution relation and extracted arithmetic.
- [SoftmaxPipelineExists.lean](../../integration/torchlean/PtxBinary32/SoftmaxPipelineExists.lean): constructive existence from original finite scores.
- [PtxSoftmaxPipeline.lean](../../integration/torchlean/PtxSoftmaxPipeline.lean): final stored values compared to pinned TorchLean softmax.

Run `python3 integration/torchlean/check.py` after provisioning the pinned
Lean and numerical dependencies. This builds the proofs, freshly checks examples
and audits public declaration dependencies. It runs no GPU benchmark.

A parallel elementwise implementation, fused execution, arbitrary row sizes,
masked softmax, and a backward kernel remain separate work. Lean checking proves
the formal statements; it does not establish NVIDIA hardware conformance or
resolve the documented approximation-policy ambiguity.
