# A loop over an array

The [Stratic description](../../stratic/descriptions/array-mask-select.md) gives
the complete contract. This walkthrough explains the loop invariant and how a
halting witness becomes a termination proof. It builds on the
[straight-line mask-and-select example](pure-kernels.md).

The list specification has signature
**`transform (mask fallback : BitVec 32) (xs : List (BitVec 32)) : List (BitVec 32)`**.
Each input word becomes `x AND mask`, unless that value is zero, in which case
it becomes `fallback`. The kernel overwrites the input array in place.

From the repository root, with the pinned Lean toolchain installed:

```sh
lake build
lake env lean examples/array_mask_select.lean
```

The command prints `[52, 99, 99, 255]` and `[]`, checks concrete kernel execution
proofs, and prints the generic theorem signatures and two dependency reports.
The printed lists evaluate the list specification. The execution examples are
Lean proofs about the instruction model; this command does not launch a GPU.
The dependency reports use only Lean's standard logical axioms. The complete
core check is `bash scripts/check.sh`.

## The state and the eleven instructions

Memory initially has the form `front ++ xs ++ tail`, where `++` concatenates
lists. `front` and `tail` may contain arbitrary words; the array `xs` lies between
them. An address register `a0` contains `4 * front.length`, measured in bytes.
A word register `r3` contains `xs.length`. Register `r0` is scratch space for the
current word. Address and word registers are distinct banks, so `a0` and `r0`
do not overlap despite both having index zero.

A predicate register holds a Boolean value. `p1` decides whether the loop is
finished, and `p0` decides whether to select the fallback. The program counter
(PC) identifies the next instruction by its index in the following list.

| PC | Operation | Purpose |
| --- | --- | --- |
| 0 | Compare `r3` with zero into `p1` | Test whether any elements remain |
| 1 | If `p1`, branch to 10 | Skip the body when the array is exhausted |
| 2 | Load the word at `a0` into `r0` | Read the next input |
| 3 | `and.b32 r0, r0, mask` | Apply the mask using the reviewed bitwise family |
| 4 | Compare `r0` with zero into `p0` | Test the masked value |
| 5 | `selp.b32 r0, fallback, r0, p0` | Choose fallback if `p0` is true, otherwise keep `r0` |
| 6 | Store `r0` at `a0` | Replace that array element |
| 7 | Add four to `a0` | Advance by one 32-bit word |
| 8 | Subtract one from `r3` | Decrease the remaining count |
| 9 | Branch to 0 | Repeat |
| 10 | Exit | Finish execution |

Mask and fallback are immediate operands: their values are part of the supplied
program. `initial` sets the pointer, count, PC and memory directly. This is an
initial-state contract, not a proof about argument loading or a host launch
interface. Specializing these two operands keeps the loop small and avoids
adding an argument convention unrelated to its proof.

The load and store use the existing scalar arena rules for relaxed global memory
accesses at GPU scope. There is one thread and no interference. The memory model
here is an initialized list of words with concrete sequential reads. Neither
weakly ordered concurrent communication nor byte-overlapping accesses are being
introduced by this example. The composed model requires ISA 9.4 and architecture
number SM at least 70, as in the straight-line example.

## Why the two bounds are needed

`Bounds front xs` requires:

- `xs.length < 2^32`, so storing the count in 32 bits does not truncate it.
- `4 * (front.length + xs.length) < 2^64`, so the address immediately after the
  array fits in 64 bits. The final iteration still increments the pointer,
  although it never loads from that final address.

Every used address is a multiple of four bytes. The input layout supplies a
word at each address that is actually read or written. No assumptions about
array values, mask or fallback are needed. The bounds do not restrict the
surrounding words' contents or claim that an arbitrarily large abstract arena
could be allocated on a GPU.

For an empty array, instructions 0, 1 and 10 suffice. The pointer may refer
just past the end of the arena: it is never dereferenced. `empty_execution`
proves this even without the main theorem's conservative address bound. The
examples also check that a count of `2^32` and an overflowing one-past address
are excluded, while the adjacent representable case is admitted. Those checks
reason about list lengths symbolically; they do not allocate enormous arrays.

## Read the proof as a moving boundary

At the top of the loop, separate memory into **already processed words**, the
**unprocessed array**, and the **unchanged tail**. The pointer addresses the
first unprocessed word, and the count is the length of the unprocessed list.
Initially, the processed part is just `front`.

[`iteration`](../../Ptx/ArrayMaskSelect.lean) constructs ten actual transitions
for a nonempty remainder `x :: xs`. It restores the same top-of-loop shape with
`answer x fallback mask` appended to the processed part and with `xs` remaining.
This is the loop invariant: the structural property re-established after each
iteration. Its proof checks the load and store, register reads before writes,
pointer arithmetic, counter subtraction, and the back branch individually.

`execution` performs induction on the unprocessed list. For the empty list it
uses `empty_execution`. For a nonempty list it prepends `iteration` to the run
provided by induction for the shorter list. The next iteration is not allowed
to reset the state arbitrarily: `iteration` proves equality with the next
boundary state, including its registers. The result has exactly `10*n + 3`
events for `n` input words. A skipped guarded branch still contributes a fetched
instruction event; exit contributes the final event.

`correct` uses the reviewed catalog's proved determinism to compare **every**
completed run with that constructed witness. Therefore a completed run cannot
fault, report an unsupported case, or return a different array. `other_memory`
extracts the per-index statement for words before and after the array, including
out-of-arena indices, whose optional lookup remains absent.

`memory_safe` applies to all finite advancing prefixes, not just finished runs.
It establishes that emitted accesses are aligned and in bounds. Such a safety
result alone would not exclude a later fault; the separate completion and
termination results do that under the target and length conditions.

## Existence versus termination

One successful run need not exclude another run that loops forever in a
nondeterministic model. Here, each operation's permitted result is unique, and
`ReviewedPure.functional` proves that property for the catalog.

[`PureKernelRules.lean`](../../Ptx/PureKernelRules.lean) adds reusable rules
without changing the transition relation. `Run.prepend` composes a prefix and a
completed run. `Run.complete_prefix` uses determinism to show that any advancing
prefix of a state with a halting witness can extend to that same final state.
Its prefix is strictly shorter than the complete trace, which includes exit.
`Run.no_infinite_advances` rules out a next-instruction transition at every
natural-number time: taking a prefix as long as the witness would contradict
the strict bound.

For this array, `prefix_termination` bounds every advancing prefix by `10*n + 2`
events and supplies its successful completion. `no_infinite_execution` states
the corresponding infinite-execution exclusion explicitly. These are properties
of the instruction model. They do not assert scheduling fairness, elapsed time,
or progress on physical hardware.

The new proofs reuse existing scalar and reviewed pure semantics. They introduce
no new ISA form and provide no new independent evidence of hardware conformance.
Their kernel-checked validity and the fidelity of the underlying definitions to
the pinned NVIDIA manual remain separate claims.
