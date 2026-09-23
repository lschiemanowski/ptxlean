# Tensor layouts and an exact integer bridge

A tensor names values by logical coordinates. A memory layout tells us which
stored word supplies each coordinate. The first bridge uses a one-dimensional
tensor and three consecutive 32-bit words per coordinate: left input, right
input, and output. Every coordinate has its own output word. The allocation is
global memory accessible to the modeled threads; the implementation name
`SharedVector` refers to one allocation shared by threads, not PTX's separate
shared-memory address space.

The tensor view reads the supplied allocation and converts each unsigned word
to its natural-number value, or to the same exact value as a real number.
The standalone view has a default for a missing word; the execution contracts
prove every selected word exists, so that default is never used. The vector-add program loads
the two input words, adds them, stores the output, and exits. The arithmetic
wraps modulo `2^32`: the output coordinate is the remainder of the input sum
after division by `2^32`, including when that sum overflows. This correspondence
uses actual TorchLean tensors and the existing instruction-level execution.

Under the additional condition that each input sum is less than `2^32`, the
output tensor is exactly TorchLean's pointwise addition of the two real-valued
input tensors. The condition is a property of the input values, not an assumed
output equality. The real-valued view is an exact embedding of unsigned integers;
it supplies neither a floating-point interpretation nor a numerical error bound.

Execution existence is separate from the arithmetic identity. For an allocation
containing all three words per coordinate and addresses that do not wrap at
64 bits, a finite schedule executes all five instructions of every thread.
The allocation bounds and unchanged words outside the outputs remain explicit.
This establishes a finite execution, not fairness of a GPU scheduler.

The relational memory result ranges over the existing restricted vector-add
candidate family. Reads must select a write to the same location carrying the
same value. Because no thread writes an input location, those read-source
conditions force the original input values. Full memory validity has a separate
constructive witness with labels matching the execution. This bridge does not
claim arbitrary dependent PTX programs, device behavior, PyTorch correspondence,
or support for other tensor layouts and numerical formats.


A separate gradient observation keeps three exact binary32 words in input,
weight and bias sensitivity order. Finite words decode to an actual TorchLean
pack of scalar tensors; any nonfinite word makes that view fail. Three absolute
error bounds compare this decoded pack with the actual generated backward.
The kernel's layout and execution proof must establish which stored words are
being observed. Equal real values need not have equal encodings: positive and
negative zero remain distinct words.
