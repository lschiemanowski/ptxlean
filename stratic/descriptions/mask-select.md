# Mask and select kernel

This example combines scalar memory access with reviewed bitwise and selection
instructions. Its function takes three 32-bit words x, y and mask. It computes
x AND mask, returns y if that masked word is zero, and otherwise returns the
masked word. All input bit patterns are allowed; this is exact bit arithmetic.

The memory input is x, y, an arbitrary old output word, and an arbitrary tail.
The kernel loads x and y, overwrites the x register with the masked value,
compares that value with zero, selects the result, stores it into the third
word and exits. This source/destination overlap exercises incoming-value reads.
Initial registers and predicate values are otherwise arbitrary. Byte addresses
zero, four and eight are aligned and in bounds by this explicit input layout.

The result theorem covers every completed execution, and a separate constructive
witness supplies an execution ending in exit. The final memory retains both
input words and the entire tail and changes only the output word. Every recorded
memory access is valid. The computation uses the pure-kernel single-thread arena
and its ISA 9.4, numeric SM-at-least-70 domain; it is not a concurrent launch or a
claim about hardware scheduling. The example does not add a tensor or floating
point interpretation to these words.
