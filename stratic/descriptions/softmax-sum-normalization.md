# Summation and normalization

This component sums the encoded exponential values of a nonempty softmax row
and normalizes one value by that computed sum. The sum has a fixed balanced
binary tree: neighboring pairs are added, then neighboring pair results, until
one value remains. Every addition rounds to the nearest binary32 value, choosing
the even final bit on a tie. The supported row length is a power of two, at most
1024. Each stored input is finite and has absolute value at most two. These are
conditions on the supplied words, not assumptions about successful intermediate
arithmetic. Small negative approximate exponential values are allowed; positivity
must not be inferred from the ideal exponential alone. The existing shifted
exponential sequence supplies the magnitude bound of two from its actual
nonpositive base-two argument and the exponential instruction error contract.

The first parallel sum specializes the existing dense kernel to one row, exact
positive-one weights, positive-zero bias and no activation. Its actual instruction
list still loads those constants, multiplies each input by one and adds zero at
the end. Those operations preserve the finite real value but do not justify a
claim about preserving every zero sign. Reusing the checked kernel retains its
actual address calculations, shared-memory tree, barriers and stored-output
proof. This is a reference implementation; removing the extra work needs a
separate program and correspondence proof.

For n inputs, global storage contains n inputs, n positive-one weights, a
positive-zero bias and an output word: 2*n+2 words. Shared storage contains
(depth+1)*n words, where n=2^depth. One cooperating thread array, whose threads
share memory and wait at group barriers, processes the row. Unused initial
registers and shared contents may be arbitrary. Every completed admitted
execution has the stated numerical result and preserves the global input and
constant regions. A separate finite schedule constructs a completed admitted
execution with safe accesses. Neither claim establishes GPU execution, launch
compatibility, scheduler fairness or performance.

The numerical proof derives finite intermediate sums from the input magnitude
and tree depth. It bounds the error against the exact sum of the actual encoded
input values, keeping it separate from each exponential's error against its
ideal real value. A conservative uniform allowance of 2^-13 per tree addition
covers this bounded domain, giving a sum error at most (n-1)*2^-13. The exact
multiplications by one and final addition of zero introduce no real-value error.
A sharper allowance can replace this bound without changing the arithmetic order.

Let delta_i bound each exponential error and let sigma be the proved summation
allowance. If sigma+sum_i delta_i is at most one half, the stable softmax's ideal
denominator lower bound of one implies that the computed denominator is at
least one half. This guard is explicit; it is not an assumption that the
reciprocal or final result already exists. It also explains which upstream
accuracy information a complete softmax proof must supply.

Normalization uses rcp.rn.f32 followed by mul.rn.f32. The reciprocal rounds one
divided by the actual computed denominator; multiplication then uses that
rounded reciprocal and the actual numerator word. The scratch destination must
differ from the numerator register, since the numerator remains live for the
second instruction. It may coincide with the denominator register. From a
finite denominator at least one half and a finite numerator of magnitude at
most two, the proof derives finite reciprocal and product values, their separate
rounding errors, fetched execution existence and preservation of unrelated state.
This is a scalar instruction sequence, not a proof of parallel normalization
stores or of a combined softmax launch.

The sum and normalization guarantees discharge the corresponding local stages
of the softmax error bound. Any resulting comparison with the ideal softmax
must still retain the exponential errors and the explicit total-error guard.
A separate reference-forward responsibility connects these components through
actual loads, stores and phase writeback. This component's register interface
alone does not establish that complete execution.

The component interface puts an original numerator in register 0 and the actual
stored sum in register 1, then runs scalar normalization with register 2 as scratch.
Its theorem combines the completed admitted sum execution with those fetched
scalar runs to bound each normalized value against the ideal exponential divided
by the ideal sum. Initializing these registers is an explicit mathematical
handoff; PTX loads, broadcast and combined launch execution remain unimplemented.
