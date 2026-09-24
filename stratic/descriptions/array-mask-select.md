# Array mask and fallback

An in-place array kernel replaces each 32-bit word x by x & mask, except
that a zero masked value is replaced by a caller-chosen fallback word. Here &
means bitwise AND: a bit survives only when it is set in both operands. Mask
and fallback are fixed immediate operands in the program; they are not loaded
from an external argument format.

The array occupies a consecutive part of an initialized list of words. An
arbitrary prefix and suffix surround it and must be preserved. A 64-bit byte
address points to the first array word, and a 32-bit unsigned counter holds
the number of words remaining. Other registers initially have arbitrary values.
The array length must be less than 2^32, and the byte address just past the
array must be less than 2^64. These conditions prevent counter truncation and
address wraparound, including the pointer increment after the last store.

At each iteration the kernel tests for an empty remainder and exits if the
counter is zero. Otherwise it loads one word, masks it, compares with zero,
selects the fallback when needed, stores the result, increments the address
by four bytes, decrements the counter and branches back. The mask and select
steps use the reviewed collection of pure instruction definitions. Loads, stores,
comparison, arithmetic, branch and exit use the existing scalar rules.

A constructive execution witness processes arbitrary array lengths satisfying
these bounds, including zero. Every completed execution produces the mapped
array, preserves the surrounding memory and ends at exit. Every finite
execution prefix can complete to that result, and its number of advancing
steps is bounded by ten times the array length plus two. Thus no infinite
sequence of advancing instructions is possible in this model. The completed
trace includes the exit event and has ten times the array length plus three
events. Memory accesses start at multiples of four bytes and stay within the supplied
initialized list of words.

This is a single-thread, isolated word-memory example for PTX ISA 9.4 and
GPU architecture number SM 70 or later. Termination concerns this instruction
model, not scheduling or progress on a GPU. No raw PTX parsing, launch argument convention, concurrent
interference, byte aliasing or hardware correspondence is established.
Checking the Lean proofs establishes the stated model's results; fidelity of
the instruction definitions to NVIDIA's semantics is a separate review claim.

The proof constructs one iteration, moving a word from the unprocessed array
to the processed part, then uses induction on the remaining list. The proved
uniqueness of instruction results connects that witness to all executions.
From the repository root, run `lake build` followed by
`lake env lean examples/array_mask_select.lean` to check concrete instances
and inspect the generic theorem signatures. The printed lists evaluate the
list specification; the command checks proofs rather than launching a GPU.
