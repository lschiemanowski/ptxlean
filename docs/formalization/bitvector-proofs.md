# Working with fixed-width values

`BitVec n` is an unsigned pattern of exactly n bits. Its `toNat` is between zero
and `2^n - 1`. `getLsbD j` observes bit j, counting from the least significant bit;
it returns false when j is outside the width. These conventions include n = 0.
The shared helpers in `Ptx/BitVecProof.lean` concern Lean values, not PTX semantics.

## A reliable bit-proof sequence

For a conditional word, first move the observation through the conditional using
`Ptx.BitVecProof.getLsbD_ite` or `getLsbD_ite_zero`. Then use the library's
`BitVec.getLsbD_and`, `BitVec.getLsbD_or`, and `BitVec.getLsbD_not` to expose
Boolean operations. Complement requires the valid-index condition: outside the
width both the input and its complement have false observations. Finally use
Boolean case analysis or simplification on the exposed input bits. Small explicit
`simp only` lists can keep intermediate expressions in a predictable form.

Always parenthesize a Boolean expression on the right of an equality:

```lean
observedBit = (condition && sourceBit)
```

Without the parentheses, Lean can parse `observedBit = condition && sourceBit`
as a Boolean expression coercing the equality to a Boolean, followed by a
proposition asserting that expression is true. That is a different statement.
Inspect the elaborated goal before looking for a stronger tactic. The old LOP3
helper's false-condition branch demanded that an arbitrary source bit be true;
that was evidence of a statement problem, not a difficult valid theorem.

## Exact immediate conversions

`BitVec.ofNat n k` retains k modulo `2^n`. It silently drops upper bits when k
does not fit; it is not a range check. The pinned library supplies general width
facts. The three wrappers keep the `ofNat`/`toNat` spelling used by typed decoders:

- `toNat_widen`: increasing width preserves the numeric value.
- `narrow_widen`: widening then returning to the original width preserves the value.
- `widen_narrow`: narrowing then widening preserves a value that fits in the smaller width.

A decoder of an eight-bit immediate represented by a 32-bit word must check
`value.toNat ≤ 255` before using the final rule. The successful-encoding direction
gets its bound from the original eight-bit value. The successful-decoding direction
gets it from the decoder's accepted branch. They are different proof obligations.
Use these numeric equalities before simplifying the surrounding record equality;
uncontrolled rewriting can replace `ofNat` expressions by `setWidth` prematurely.
`BitVec.ofNat_toNat` rewrites to `setWidth`; equal-width conversion then simplifies
with `BitVec.setWidth_eq`. Library names alone do not guarantee the needed normal form.

Run the worked examples and their dependency reports:

```sh
lake build Ptx.BitVecProof
lake env lean examples/bitvector_proofs.lean
```

The examples prove a conditional AND law at arbitrary widths, show the two
immediate conversion directions, and distinguish the boundary values 255 and 256.
They include zero-width and out-of-width observations. They contain no LOP3
computation or proof of its eight-entry truth table. The worker must still finish
its instruction-specific bit law and exact typed decoder properties.
