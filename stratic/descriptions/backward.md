# Backward specification and verification

A backward computation answers how changes in selected inputs or parameters
affect a weighted combination of the network's outputs. For a real-valued network
`F`, the matrix of output derivatives is its Jacobian, written `DF(x)` at the
chosen input and parameter values `x`. Given output weights `y_bar`, the target
is `DF(x)^T * y_bar`, a vector-Jacobian product (VJP). The transpose turns output
weights into sensitivities of the selected variables. These incoming weights
are also called a cotangent. A VJP can be passed through successive computations
without constructing the full derivative matrix or first choosing a particular
scalar training objective, called a loss. The contract assumes differentiability
where the classical derivative is required.

TorchLean constructs the backward computation automatically. Checked theorems
connect it to the mathematical VJP under explicit assumptions. Each use identifies
the supported operations and the conditions needed by their derivative rules.

The PTX backward implementation is authored separately, together with its
correctness proof. Reusable lemmas, proof-automation procedures called tactics,
and model assistance can help construct that proof. Automatic differentiation
of the TorchLean specification does not generate the PTX implementation or prove
that implementation correct.

There are separate obligations to show that the mathematical derivative exists,
that the backward computation computes it, that numerical errors are bounded,
and that the PTX implementation corresponds to that computation. Execution
existence, safety, and termination also need their own proofs. Constructing a
backward specification does not establish that its GPU implementation finishes.

Explanations trace the incoming cotangent through the specified backward
computation and its kernel contracts. They identify the differentiated variables,
saved-value or recomputation requirements, differentiability hypotheses, and
numerical and execution guarantees supplied by each theorem.
