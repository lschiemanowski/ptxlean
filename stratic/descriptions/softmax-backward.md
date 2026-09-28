# Parallel softmax backward

The backward takes the actual stored softmax outputs and a row of incoming
sensitivities: numbers describing how strongly each output contributes to a
surrounding result. For ideal weights p and sensitivities g, it returns
p_i*(g_i-q), where q is the sum of p_j*g_j over the row. This is the true
vector-Jacobian product of the ideal real-valued softmax. The supplied PTX
program is developed separately from TorchLean's automatic backward construction.
It does not differentiate floating-point rounding or the approximate exponential.

The implementation first computes qHat, an approximation of q, by combining
pairwise sums in a balanced tree. It reuses the existing parallel reduction
with one row, stored forward outputs as inputs, sensitivities as weights, and
positive-zero bias. Multiplication at each leaf and addition at
each tree node remain actual rounded instructions. A parallel difference pass
loads each sensitivity and the stored qHat, multiplies qHat by exact minus one, and
adds that result to the sensitivity. A parallel multiplication pass then loads
each stored forward output and difference and writes the gradient. The separate
passes favor reuse of checked execution and memory contracts; fusion is outside
this component. Multiplying by minus one and adding does not claim a new
subtraction-instruction formalization.

The forward output prefix is retained as storage when forward scratch is
released. Incoming sensitivities and fresh scratch are supplied in separately
specified regions of the resulting memory buffer, called the arena. These allocation and storage-view
operations perform no derivative arithmetic. Original row inputs and values passed
between launches come from fetched loads; arithmetic intermediates come from
actual instructions. Each dot product and difference passed to the next phase
comes from an actual store. Sources remain read-only during each pointwise pass, and
each output cell has one writer. Entry pointers are an explicit input interface,
not a CUDA argument-passing proof. Completed phase boundaries retain the existing
model-level waiting and initialization contract.

For n entries, words 0 through n-1 retain the forward outputs and words n
through 2*n-1 hold incoming sensitivities. Word 2*n is the positive-zero bias,
and word 2*n+1 holds the computed dot product. The difference pass appends n
output words starting at 2*n+2; the multiplication pass appends n gradient words
starting at 3*n+2. The final arena has 4*n+2 words and preserves both input rows.

The first domain retains nonempty power-of-two rows of at most 1024 entries.
For accuracy, original scores are finite, have magnitude at most 2^124, and
satisfy the forward guard: the accumulated exponential and sum error allowance
is at most one half.
Incoming encoded sensitivities are finite and have magnitude at most 2^60.
Their exact real values are the initial backward reference inputs. Forward
accuracy and the numerical normalization proof bound the actual stored weights;
the derived weight magnitude is at most four. Products, the dot result,
differences and gradients have respective magnitude bounds 2^62, 2^72, 2^73
and 2^75, establishing finite encoded results. These conservative bounds leave
room for signed accumulation without requiring intermediate range premises. Successful intermediate execution, intermediate
finiteness and final gradient accuracy are conclusions rather than caller premises.
The gradient error includes the inherited forward error, rounded dot-product
error, difference error and final multiplication error, each kept explicit.

Write epsilon_i for the inherited error of stored pHat_i from ideal p_i.
The dot rounding allowance sigmaDot sums half-grid-spacing errors at every
leaf product and tree addition on their actual rounded operands. With
q=sum_j p_j*g_j, Q=sigmaDot+sum_j abs(g_j)*epsilon_j bounds the dot error.
The stored gradient error is at most
`mulError_i + abs(g_i-q)*epsilon_i + abs(pHat_i)*(subError_i+Q)`.
Here subError_i bounds rounding of g_i-qHat, and mulError_i bounds rounding of
pHat_i times that rounded difference. Multiplication of the finite qHat by
minus one is exact as a real value. Incoming values have no additional
quantization allowance because the reference uses their exact stored values.

Every completed admitted backward execution satisfies the stored-output
contract and preserves its input regions. Separately, a finite schedule and its
memory-admission proof establish that a complete execution exists. Backward
alone has a witness for arbitrary input words; whole forward/backward existence
requires only the original finite-score domain, without an accuracy guard or
incoming finiteness. The stronger conditions above are needed for the numerical
comparison. All actual
accesses are checked for allocation bounds and alignment. The combined theorem
starts with original scores and incoming sensitivity words, runs forward and
backward, and compares the stored gradients with TorchLean's real derivative.
All results permitted by the arithmetic relations remain covered. Bitwise
agreement with a concrete PyTorch backend, arbitrary row lengths, masking,
fused execution, GPU progress and benchmarking remain separate obligations.
