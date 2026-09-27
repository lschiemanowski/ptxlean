# Bounded approximate exponential instruction

The base-two exponential of x is 2 raised to the power x. This responsibility
covers a bounded fragment of ex2.approx.f32, using binary32 (32-bit floating
point), the pinned PTX 9.4 version and sm_20 or later. It preserves subnormal
numbers, the small representable values near zero, and excludes the optional
flush-to-zero mode. The typed text interface accepts exactly this spelling,
a word-register destination and one word operand; it is not a raw PTX parser.

The supported input domain consists of finite nonpositive values, both
infinities, and NaN (not a number). Both signs of zero produce exactly positive
one. Negative infinity produces positive zero; positive infinity produces
positive infinity. NaN permits any NaN output in the existing conservative
payload policy. For strictly negative finite inputs, every finite result in the
reviewed two-ULP neighborhood is retained. ULP means the spacing of the floating
point grid: the neighborhood uses the larger spacing at the nearest-even rounded
reference and at the returned value. This covers the two named conventions,
without claiming a unique interpretation of NVIDIA's wording or physical
realizability of every permitted bit pattern.

Positive finite operands have no enabled step in this fragment. This is missing
formalization coverage, not a claim that NVIDIA leaves their behavior undefined
or that a GPU cannot execute them. It must remain visible in every existence
contract. A disabled predicate skips even an unsupported input, without requiring
an arithmetic result. An enabled instruction reads its operand in the original
state, writes exactly its destination, and advances the instruction position.
Source and destination may be the same register. Other registers, predicates,
address registers and memory are preserved. The occurrence records the actual
instruction, position, reads and writes, with no memory access.

A program step requires actual fetch at the current instruction position and the
selected target. A next state exists exactly when the predicate is disabled or
the enabled operand is in the supported numerical domain. This is one-step
existence, not a whole-kernel termination or hardware progress guarantee.
For an enabled instruction, finite nonpositive input gives a finite output
with error at most 5*2^-24 from 2^x, including reference rounding. The actual destination also connects to the
natural-exponential base-conversion proof when preceded by its encoded multiply.
These numerical bounds do not replace source review, memory/storage contracts,
or proof of a parallel softmax program.
