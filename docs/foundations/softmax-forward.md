# Softmax forward execution

The pipeline computes stable softmax for a nonempty row of encoded binary32
scores. Its maximum, exponential, sum and normalization phases run parallel
programs. A simpler composition with sequential elementwise passes remains as
a reference. The two compositions allow exactly the same final output arrays.
The parallel version still has separate phases; it is not a fused or benchmarked
GPU kernel.

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
2. **Exponentials.** Thread i handles index i. Two fetched loads read score_i
   and the stored maximum. Four arithmetic instructions compute the shifted
   exponential, and a fetched store overwrites cell i. Threads can interleave
   these instructions freely; the maximum at n remains intact throughout.
3. **Restore the weight.** One fetched store writes encoded positive one at n.
   The resulting actual arena is proved equal to the sum kernel's required layout.
   No host operation constructs an exponential vector to substitute for these
   stored results.
4. **Sum.** The parallel unit-weight reduction stores its denominator at 2*n+1.
   It preserves the exponential prefix and all other constant cells.
5. **Normalize.** Thread i loads exponential_i and the stored denominator,
   executes `rcp.rn.f32` and `mul.rn.f32`, and stores the result back to cell i.
   The denominator is outside the overwritten prefix.

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
safe access traces. Elementwise instructions execute through a small parallel
adapter for the existing scalar and floating-point instruction relations. Loads
can propose arbitrary values; memory admission must justify those values using
actual initial writes or program stores. Byte addresses are four times their
word indices. Validity requires both an allocated word and index less than 2^62,
so conversion to a 64-bit address cannot wrap.

The pipeline target is PTX 9.4 and SM 7.0. The scalar arithmetic stage components
also support the weaker SM 2.0 threshold inherited from their instruction leaves.
Each elementwise stage uses registers 0 and 1 for loaded operands and register 2
for arithmetic scratch, preserving other registers, address registers and predicates.
The parallel pass entry interface sets the program counter to zero and installs
each thread’s own-cell pointer in address register 0 and the common-scalar pointer
in address register 1. Those pointer values are inputs to this fragment; calculating
them with fetched PTX instructions or establishing a CUDA launch interface remains
outside the proof. All other initial register values may be arbitrary.

Finishing a stage and starting the next is an explicit operation of the
composition model. Entry state and reduction scratch are initialized there.
These boundaries perform no softmax arithmetic. They are not a CUDA allocator,
runtime launch implementation, device-visibility proof, or single fused kernel.
The reference passes use direct sequential reads. The parallel passes quantify
over admitted read observations and arbitrary instruction interleavings.

## Why an in-place parallel pass reads the right inputs

Take the two-score normalization pass. Both threads can load their numerators
before either stores an output; either can finish first. Each uses the same
unchanged denominator at index 5. A possible instruction order begins

```
thread 1: load cell 1
thread 0: load cell 0
thread 1: load denominator
thread 0: load denominator
... arithmetic and stores interleave ...
```

Reading a cell and later overwriting it might seem to require sequentially
consistent memory, where every thread observes one common order. Here the
existing weaker memory constraints suffice. Only thread i can write cell i,
and its store is later than its load in that thread's instruction order. The
memory model's no-future rule prohibits sourcing a load from this causally later
store. Consequently its only source is the cell's initial write. No thread
writes the common denominator. This proves the operands rather than inserting
the intended operands into the execution definition.

The universal result covers every completed admitted execution. For existence,
a separate construction can run lanes one after another, realizing any selected
set of arithmetic outcomes. It constructs initial-write sources and orders
writes by their trace positions, then proves that this particular graph meets
the same memory constraints. This chosen witness does not restrict the universal
result to that schedule and makes no fairness promise.

## Why keep a sequential reference?

The reference is a useful numerical boundary. For each pass we prove that its
possible final arrays are exactly those allowed by the per-element instruction
relations, with every other cell unchanged. Both the sequential and parallel
programs satisfy this statement in both directions: actual execution implies
the array contract, and every allowed array has an actual execution witness.
Composing this result shows that the two full pipelines have exactly the same
possible final arrays. Their instruction traces need not match.

The existing error proof therefore applies to the parallel pipeline without
changing its numerical policy. In particular, an approximate exponential is
still allowed every result of the existing relation. We do not choose a single
reference exponential and call that parallel correctness.

The additive adapter also keeps the executable interpreter for earlier parallel
reductions unchanged. Exponential semantics currently use real-valued relations;
existence proofs construct Lean witnesses but do not supply an executable
floating-point exponential approximation or a GPU runner.

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
- [ParallelUnary.lean](../../integration/torchlean/PtxBinary32/ParallelUnary.lean): the additive parallel adapter and actual access safety.
- [UnaryPointwiseReads.lean](../../integration/torchlean/PtxBinary32/UnaryPointwiseReads.lean): ownership and no-future exclude incorrect read sources.
- [ParallelUnaryAdmission.lean](../../integration/torchlean/PtxBinary32/ParallelUnaryAdmission.lean): a separately constructed graph for an existence witness.
- [UnaryPointwiseLaunch.lean](../../integration/torchlean/PtxBinary32/UnaryPointwiseLaunch.lean): completed admitted passes and stored-array correctness.
- [SoftmaxParallel.lean](../../integration/torchlean/PtxBinary32/SoftmaxParallel.lean): parallel composition, two-way output equivalence and independent existence.
- [PtxSoftmaxParallel.lean](../../integration/torchlean/PtxSoftmaxParallel.lean): parallel stored values compared to pinned TorchLean softmax; [PtxSoftmaxPipeline.lean](../../integration/torchlean/PtxSoftmaxPipeline.lean) holds the shared accuracy contract.

Run `python3 integration/torchlean/check.py` after provisioning the pinned
Lean and numerical dependencies. This builds the proofs, freshly checks examples
and audits public declaration dependencies. It runs no GPU benchmark.

The [parallel backward pipeline](softmax-backward.md) consumes these actual
stored outputs and includes their error in its gradient guarantee. Fused
execution, arbitrary row sizes and masked softmax remain separate work.
Lean checking proves
the formal statements; it does not establish NVIDIA hardware conformance or
resolve the documented approximation-policy ambiguity.
