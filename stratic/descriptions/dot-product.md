# Sequential binary32 dot product

The kernel multiplies corresponding entries of two arrays and adds the products,
from first to last, starting at positive zero. Its ideal real result is the sum
of all pairwise products. Empty arrays produce positive zero. This is a reusable
scalar-output computation for a vector-input neuron, without an activation or a
backward computation in this component.

One thread runs an actual PTX loop over two contiguous arrays of binary32 words.
Each multiplication and addition rounds separately to nearest with ties to even;
there is no fused multiply-add and no reassociation of the sum. The caller supplies
initialized storage, the two input addresses, the output address and a 32-bit
length. The code initializes its own accumulator. Length and address conditions
exclude counter truncation and pointer wraparound, including the final one-past
pointers. Every read and write must be aligned and within the supplied allocation.
The output is written only after all reads; the reusable contract permits it to
alias an input word, while a caller wanting both inputs preserved supplies a
separate output word. All other memory remains unchanged.

Every completed execution has the prescribed accumulation order and exactly
10*n+5 instruction events for n pairs. Every advancing prefix can finish and is
shorter than that bound, so no infinite instruction execution is admitted.
These guarantees cover all bit patterns and all results admitted by the existing
floating-point contracts. They do not assume a deterministic choice of NaN bits.
The execution proof uses a finite proof of all possible instruction successors;
it does not change the semantics into a fuel-limited runner.

For numerical accuracy, each encoded input must represent a finite real value.
The caller bounds its deviation from the intended real input. Explicit range
conditions, computed recursively from those initial values and the specified
rounding operation, keep each product and running sum finite. The proof derives
finiteness and an absolute error bound for the stored result. The bound accumulates
input encoding errors and both rounding errors at each iteration; no final result
or intermediate accuracy is assumed. Its size depends on the input magnitudes and
number of terms, and need not be small for every admitted input.

Memory reads use the existing isolated sequential word arena. Other threads,
the host and asynchronous work must not interfere while the kernel runs. The
fragment targets PTX 9.4 with the existing numeric sm_70-or-later condition.
Launch argument setup, byte-aliasing semantics, concurrent reductions, hardware
conformance and bitwise agreement with a PyTorch backend remain outside this
contract. The proof reuses instruction definitions already present in the project;
Lean validity and fidelity of those definitions to NVIDIA's specification remain
separate claims.
