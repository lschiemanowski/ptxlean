# An affine calculation through memory

This small example computes a product followed by addition of a bias, the
formula x*y+b. It connects a concrete instruction program to a numerical error
bound on the word actually stored in memory. It is a scalar example of reusable
execution and numerical contracts, not a neural-network or TorchLean backward
verification.

The program executes seven instructions: load the left input, load the right
input, load the bias, multiply with nearest-even rounding, add the bias with
nearest-even rounding, store the output, then exit. Binary32 is the 32-bit
single-precision format. Nearest-even rounding chooses the closest representable
result and resolves an exact tie by choosing an even last bit. Multiplication
and addition are separate instructions with separate rounding; this is not a
fused multiply-add, which would round only once.

The caller supplies initialized memory and four valid addresses: three inputs
and an output. Each address is four-byte aligned and its entire four-byte access
fits within the arena, the modeled list of memory words. Address registers hold
those modeled addresses and the program counter starts at the first instruction. Initial
value registers, predicates and surrounding memory are otherwise arbitrary.
All three inputs are loaded before the only store, so input and output addresses
may coincide. Input values always refer to the initial memory snapshot. An input
slot that is also the output slot need not retain its initial value.

Every completed run must produce actual intermediate and output words admitted
by the numerical multiplication and addition relations. The intermediate word
written by multiplication is the word read by addition. Final memory is exactly
the initial arena with the output slot replaced by that output word. The five
working value registers contain the three loaded inputs, intermediate and final
result; every other value register, all address registers and all predicates are
preserved. Every non-output memory slot is preserved.

The trace records exactly seven fetched instructions at positions zero through
six. It includes three loads with their actual addresses and values, the two
floating-point steps, the actual output store, and explicit exit. Floating-point
events retain their own instruction identity and have no memory effect. Exit
leaves the program counter at six. Under the initial address conditions, a
completed run exists for every encoded input, including exceptional values.
There are exactly six advancing steps before exit: arbitrary admitted numerical
choices cannot create a longer advancing path or a fault. Shorter finite paths
are still incomplete, not evidence of termination.

For an accuracy bound, the encoded inputs must represent finite real values xh,
yh and bh. Their differences from the ideal real inputs x, y and b are bounded
by nonnegative budgets ex, ey and eb. The exact product magnitude must not exceed
the largest finite binary32 value. The sum of that product magnitude, its local
rounding-error allowance and the actual bias magnitude must also fit that limit.
These conservative conditions concern only the original inputs. They establish
finiteness of both arithmetic stages; they do not assume a correct or finite
output as a premise.

Every completed run satisfying those conditions stores a finite value whose
absolute difference from x*y+b is bounded by both rounding contributions and
the propagated input errors. The multiplication contribution includes the effect
of perturbing both inputs together. The bound uses the existing numerical
composition contract without choosing a special execution or replacing the
intermediate word by an exact real product. Encoded equality and closeness to
the ideal real value remain distinct claims.

This is one thread executing in an isolated, initialized global-memory arena;
no other thread, host operation or asynchronous work accesses the modeled memory
during the run. The target slice is PTX ISA 9.4 with sm_70 or later because the
loads and store use explicit relaxed ordering at GPU scope. At the external
text boundary, bit registers declared `.b32` carry the encoded values through
both `.u32` memory transfers and `.f32` arithmetic without a numerical conversion.
Checking register declarations, runtime storage permissions, pointer translation,
launches and hardware behavior remains outside the example. Numerical existence
uses the reviewed conservative NaN result set and is not a claim that every NaN
encoding in that set is realizable on hardware.

The four memory events projected from the actual trace match a separately checked
memory graph: three loads at instruction positions zero, one and two, followed
by the store at position five. Initialization events come from the supplied
initial arena, once per word. Each load reads its initial value, including when
all pointers coincide. The graph satisfies the existing necessary memory rules;
that fact alone is not a general sufficiency theorem for dependent PTX programs.

The actual register read/write records also show that every computed-value
dependency goes forward in instruction order: inputs loaded from the initial
arena feed multiplication and addition, whose output feeds the store. This
fragment-specific grounding excludes a value justified only by a cycle in this
program. It does not replace the general PTX rule against circular justification
with an assumption that all dependency graphs must be acyclic.
