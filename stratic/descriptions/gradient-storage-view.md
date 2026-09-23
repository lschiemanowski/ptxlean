# Three stored gradients and their real-valued view

A stored gradient is still an exact 32-bit word. This view keeps three words
in the order input sensitivity, weight sensitivity and bias sensitivity. The
caller selects those words from memory; the view itself neither invents
addresses nor checks whether an allocation can be read. Execution and layout
proofs must establish that the selected words are the actual stored outputs.

Each word is interpreted as binary32 only when it represents a finite number.
If any word is an infinity or a NaN, meaning a nonnumeric floating-point result,
the whole real-valued view fails. Otherwise it returns an actual TorchLean pack
of three scalar tensors. A scalar tensor contains one real number and has no
array dimensions. The approximation contract retains these exact words as its input;
the real view does not replace their bit patterns.

Componentwise approximation means that each of the three decoded real numbers
differs from the corresponding reference sensitivity by at most its specified
absolute-error bound. The reference may be any three-scalar TorchLean pack.
The contract is equivalent to the three individual numerical inequalities;
there is no default value for a missing finite interpretation and no assumed
successful backward call.

For the existing graph computing `(x*w+b)^2`, the reference is the actual
TorchLean-generated backward result with real output seed d. A seed weights the
output sensitivity propagated backward. The checked call succeeds, and its
three reference values are `2*d*(x*w+b)*w`, `2*d*(x*w+b)*x` and `2*d*(x*w+b)`.
Given finite interpretations of the stored words and numerical bounds against
these formulas, the interface proves approximation of that actual generated
result and exposes the checked call's successful return.

Agreement within an error bound is distinct from equality of stored bits.
Positive and negative zero have different encodings but the same real value;
real decoding is not claimed to be injective. This interface proves no rounding
bound, kernel execution, allocation safety, tensor-wide layout or PTX backward
correctness by itself. Those proofs supply the selected words and numerical
inequalities to this observation interface.
