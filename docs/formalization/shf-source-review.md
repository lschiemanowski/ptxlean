# Funnel-shift source review

The selected source is the local hash-pinned PTX ISA 9.4 manual, section
`logic-and-shift-instructions-shf`. Its section digest is
`3dbb54947209e5144a5407d03642e7be049776fe90f5a7506965dd2168b3dfd1`;
the complete manual digest is recorded in the source manifest. NVIDIA's source
is fetched locally and is not distributed with this project.

The selected forms are `shf.l.clamp.b32`, `shf.l.wrap.b32`,
`shf.r.clamp.b32`, and `shf.r.wrap.b32`. The first input supplies the low
32 bits and the second the high 32 bits. Left shift returns the upper half
of the shifted concatenation; right shift returns its lower half. Vacated
bits are zero. Counts are unsigned 32-bit words, capped at 32 in clamp mode
and reduced modulo 32 in wrap mode. There is no small-count precondition.
At count zero, left returns the second input and right the first; at clamped
count 32 those choices reverse. Wrapped count 32 behaves like zero.

The four all-input result equations use Lean's zero-filling word shifts by
natural-number amounts. Such a shift by 32 gives zero; it does not silently
mask the count. The independent concrete checks instead shift an integer
concatenation and extract a half. Preparation compared these two arithmetic
accounts on 656 cases, including every effective count, unequal source words,
zero/all-one words, top bits, 33, 63, 64 and the maximum unsigned count.
This arithmetic preparation was not a complete Lean reference preflight.

The manual introduces these instructions in PTX3.1 and requires SM32 or higher.
The leaf deliberately selects ISA exactly9.4 and numeric SM at least32, including
skipped instructions. This is a feature threshold, not architecture-name validation.
Sources are compatible 32-bit registers or already converted immediates; the
control remains a full word operand. The typed decoder is not a raw PTX parser
and does not check register declarations. Predication, incoming-state reads,
source/destination overlap, repeated reads and frame properties use Pure32.

The rotation example supplies the same word twice. Its wrap forms match Lean's
standard rotations for every count, including counts greater than 32. Clamp
mode is not interchangeable for arbitrary counts: once capped, counts above
32 give the original word when both sources agree. The combined-kernel example
inherits the existing ISA9.4/SM70 restriction. That stricter example boundary
is not an added instruction requirement.

Lean kernel validity, source fidelity, and hardware conformance are separate
claims. The result equations fully specify the requested computation, so worker
success under this contract does not establish independent interpretation of PTX.

The independent GLM request returned **accept**, with no findings. Its explanation
incorrectly generalized the wrap count-zero result as the second source; that is
true only for left shifts. Right shifts return the first source. The coordinator
checked both directions explicitly against the source, candidate equations and
concrete checks. This wording error does not change the candidate, but illustrates
why an advisory verdict cannot replace source inspection or proof checking.

Fresh replay passes the 21 unchanged universal obligations and concrete driver v2.
The original v1 concrete driver is retained as failed evidence: coordinator
copying accidentally included unrelated PRMT cases, and two test-expression choices
needed correction. No result equation or candidate implementation was weakened.
Three altered modules (swapped source words, wrap replaced by clamp, and clamp at
31) compile and audit with their own altered proofs, but both external drivers
reject them. Their rejection checks the acceptance boundary, not hardware behavior.
