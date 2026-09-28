# A complete reference softmax forward computation

The forward computation turns a nonempty row of finite binary32 scores into
encoded softmax outputs. The row length is a power of two, at most 1024, and
scores have magnitude at most 2^124. Its maximum and sum reductions use the
existing parallel programs. Between them, sequential passes load operands,
execute the modeled exponential or normalization instructions, and store results.
These passes provide a simple reference implementation, not a fast parallel
softmax kernel or a GPU performance claim.

All phases share one global word arena. For n scores, its first n words initially
hold the scores, followed by n positive-one weights and two zero words. The
maximum reduction temporarily writes its result at index n. Each exponential
step loads a score and this stored maximum, computes the shifted exponential,
and overwrites that score's cell. After the pass, an actual store restores the
positive-one weight at index n. The sum reduction can then use the same arena
as its unit-weight dense specialization, placing its denominator at index 2*n+1.
The normalization pass loads each exponential and this stored denominator,
executes rounded reciprocal and multiplication, and overwrites the exponential
with the output. The passes access one element at a time; the maximum and
denominator remain intact until all their consumers have read them.

The composed execution contains actual fetched instructions and exact memory
writeback at each phase. Parallel phases retain their admitted read observations
and separate completed-execution witnesses. Sequential passes read the current
arena directly, so their contract requires no concurrent interference. Resetting
entry registers, allocating shared scratch and waiting for a phase to complete
are explicit operations of the composition model. They do not implement CUDA
allocation, launch, waiting or device visibility. No arithmetic value is supplied
by those operations in place of a load or store.

The numerical theorem uses the exact real values of the original stored scores.
It derives the finite attained maximum, exponential range and approximation
errors, and the sum's rounding error. If the sum of exponential error allowances
plus (n-1)/8192 is at most one half, the computed denominator is at least one
half. Rounded reciprocal and product then remain finite. Each output is bounded
against the stable real softmax, retaining exponential, sum, reciprocal and
multiplication errors separately. The error guard is a sufficient accuracy
condition, not a claim that other inputs cannot execute correctly. Existence
must not assume successful intermediate arithmetic or the desired output.

The initial domain excludes masks, empty rows, NaN or infinite scores and
non-power-of-two rows. The backward computation is separate. Correctness of
this model does not establish that every allowed numerical outcome occurs on
hardware, hardware conformance, scheduler fairness, or runtime correspondence.
