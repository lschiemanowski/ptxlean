# Bit-vector proof support

A bit vector is a value with a fixed number of bits. Shared proof support lets
instruction proofs reason about one output bit at a time and about changing the
width of an unsigned value. These are facts about Lean values; they do not define
an instruction or establish agreement with PTX.

Observing a bit of a conditional value is the same as selecting the corresponding
bit of either branch. Selecting a value or zero therefore selects its bit or
false. Boolean expressions on the right of an equality are parenthesized explicitly
so the theorem compares values rather than accidentally asserting that a bit is
true. Bits outside the value's width are false, including for zero-width values.

Increasing the width preserves an unsigned value. Reducing that width again
recovers the original value. The opposite journey, reducing then increasing,
recovers a value only when it fits within the smaller width. That range condition
is essential: reducing 256 to eight bits gives zero, so increasing it again cannot
recover 256. Immediate decoders use these facts after checking their allowed range.

The support reuses the pinned Lean library, keeps width and range conditions
visible, and introduces no instruction-specific semantics or new proof assumptions.
Worked examples demonstrate conditional bitwise operations and immediate-value
conversions. Instruction-specific output laws and exact decoding properties remain
the responsibility of each instruction family.
