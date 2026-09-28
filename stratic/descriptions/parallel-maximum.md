# Parallel finite-row maximum

This component selects a maximum from a nonempty power-of-two row of finite
binary32 words. One cooperating thread array, a group whose threads can share
memory and wait at a common barrier, handles the row. The first domain has at
most 1024 entries. The result is an original input word, its real value is at
least every input's value, and some input attains it. Both signs of zero and
subnormal values are included; NaNs and infinities are outside the real theorem.

The pairwise selector compares ordered integer keys derived from the floating
encodings. Nonnegative encodings have their sign bit flipped; negative encodings
have every bit flipped. Unsigned key comparison then agrees with real ordering
on finite inputs. Selection returns one original word without arithmetic rounding.
Positive zero wins over negative zero; identical keys choose the left input.
The implementation uses existing integer comparisons, bit operations and moves,
not an assumed floating maximum operation or a new max.f32 instruction model.

Each thread loads its input from global storage and publishes it in shared
storage. A complete group barrier separates publication from reduction. At each
level, active threads combine disjoint pairs from the previous shared plane and
write the chosen words into a fresh plane. A plane is a separate allocated region
large enough for one word per thread. Inactive threads skip pair reads and writes
but still reach every barrier. Fresh planes prevent a writer from overwriting a
value that another thread still needs. Thread zero writes the root to a separate
global output cell; all threads then exit through fetched instructions. For n=2^depth
inputs, global storage needs at least n+1 words, with output at index n; shared
storage needs at least (depth+1)*n words. Each word occupies four bytes. The
one-entry case still publishes, synchronizes and stores, with no reduction round.

The program computes addresses and active-thread conditions from supplied thread
identities and fixed row dimensions. Register r0 initially holds each thread's
identity; other registers and shared contents may be arbitrary. The modeled
target is PTX 9.4 with SM version 70. Allocation, address nonwrapping, bounds and
alignment must be established for its actual accesses. Input global storage is
preserved. The result follows from actual fetched instructions and admitted read
observations: candidate loads cannot simply be assumed to return the desired
values. Completed barriers, unique writers and fresh storage establish which
writes can supply each read.

Two execution claims are distinct. Every completed admitted execution has an
upper-bound result attained by an input. Separately, a concrete finite schedule
constructs a completed execution and an admitted memory graph. Successful
completion, safety of emitted accesses and memory admission are separate proof
obligations; a safe prefix alone is not a termination proof. No hardware fairness,
performance, launch or benchmarking claim follows from these results.

The returned maximum preserves any common input-magnitude bound. In particular,
inputs bounded by 2^124 meet the magnitude and ordering premises of the shifted
exponential when paired with this result. Attainment supplies a score whose
shifted exponential is exactly positive one. The separate reference-forward responsibility connects this result through
actual memory operations to exponentiation, summation and normalization.
Arbitrary row lengths, masked rows and groups larger than this first domain need
separate extensions; padding must not introduce a spurious zero maximum into an
all-negative row.
