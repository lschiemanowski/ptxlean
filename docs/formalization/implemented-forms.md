# Reading the accepted-form ledger

[The ledger](../../coverage/implemented-forms.json) records seventeen selected accepted
forms. It is separate from the [instruction-section inventory](coverage.md),
whose `not_assessed` entries are unchanged. Other existing scalar instructions
are not yet entered here, so even the ledger's seventeen-form count is not a count of
all implemented PTX forms.

| Exact form | Inputs → destination | Meaning | Manual conditions |
| --- | --- | --- | --- |
| `min.u32` | two unsigned 32-bit values → unsigned 32-bit register | Smaller input | PTX 1.0; all targets |
| `max.u32` | two unsigned 32-bit values → unsigned 32-bit register | Larger input | PTX 1.0; all targets |
| `clz.b32` | one 32-bit pattern → unsigned 32-bit register | Zeros before the first one, starting at bit 31; zero gives 32 | PTX 2.0; `sm_20` or later |
| `popc.b32` | one 32-bit pattern → unsigned 32-bit register | Number of one bits; zero gives 0 | PTX 2.0; `sm_20` or later |
| `add.rn.f32` | two binary32 words → compatible 32-bit register | Nearest-even sum; preserved subnormals; conservative NaN envelope | Arithmetic introduced in PTX 1.0; selected step requires ISA 9.4 and SM ≥20 |
| `mul.rn.f32` | two binary32 words → compatible 32-bit register | Nearest-even product; preserved subnormals; conservative NaN envelope | Arithmetic introduced in PTX 1.0; selected step requires ISA 9.4 and SM ≥20 |
| `selp.b32` | two words and a predicate → 32-bit register | First source if true, second otherwise | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `min.s32` | two signed 32-bit words → compatible register | Smaller signed value | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `max.s32` | two signed 32-bit words → compatible register | Larger signed value | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `and.b32` | two words → compatible 32-bit register | Bitwise AND | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `or.b32` | two words → compatible 32-bit register | Bitwise inclusive OR | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `xor.b32` | two words → compatible 32-bit register | Bitwise exclusive OR | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `not.b32` | one word → compatible 32-bit register | Complement all bits | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `cnot.b32` | one word → compatible 32-bit register | 1 if the input is zero; 0 otherwise | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `shl.b32` | word and unsigned 32-bit count → compatible register | Left shift, zero fill; counts clamped at 32 | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `shr.u32` | word and unsigned 32-bit count → compatible register | Right shift, zero fill; counts clamped at 32 | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |
| `shr.s32` | word and unsigned 32-bit count → compatible register | Right shift, sign fill; counts clamped at 32 | PTX 1.0; selected step ISA 9.4, SM ≥10 feature floor |

Every word input can come from a word register or a 32-bit immediate value.
The selection predicate is a register. All seventeen
forms support unconditional execution or execution guarded by a positive or
negated predicate. A false guard advances the program counter without writing
the destination. Register overlap is allowed: the incoming source value is read
before the destination changes. These are typed statement interfaces, not a
parser or type checker for complete PTX source files. The older unsigned and bit-count decoders record no architecture/version
eligibility decision. The selection, signed min/max and bitwise fetched steps require
ISA 9.4 and a numeric SM feature floor of 10.
The floating `Step` requires exact ISA 94 and numeric SM at least 20, although
this is not a target-name or architecture-suffix validator. Its source word bank
represents `.b32`/`.f32` registers; declared `.u32`/`.s32` registers do not become
float-compatible merely because they have the same width. A floating immediate
means an already decoded exact `0f`/`0F` literal, not an integer-to-float cast.
The result envelope fixes non-NaN bits, including signed zeros, while deliberately
overapproximating NaN possibilities. It does not certify quiet/signaling NaN
realizability, GPU execution, or a complete floating kernel. See the
[instruction source review](binary32-instructions-source-review.md).

The source was rechecked against the pinned PTX 9.4 integer instruction sections
[minimum](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#integer-arithmetic-instructions-min),
[maximum](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#integer-arithmetic-instructions-max),
[leading zeros](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#integer-arithmetic-instructions-clz)
and [population count](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#integer-arithmetic-instructions-popc).
Common input, destination and guard rules have their own pinned section anchors
in the ledger. Source fidelity is an independent review judgment, supported by
[the first source review](initial-source-review.md) and
[the bit-count review](bitcount-source-review.md); it is not a consequence of a
successful Lean build. The [pure-leaf review](pure-leaves-review.md) covers
selection and signed min/max, their exact shared-engine boundary and retained
evaluator corrections. The [bitwise review](bitwise-leaves-review.md) covers
the five .b32 logic forms and their separately replayed proofs. Other widths and
legal predicate-valued siblings remain unimplemented; `cnot.pred` is not a legal
sibling of `cnot.b32`. The [shift review](shift32-review.md) covers the three
selected shifts, unsigned counts and large-count behavior. Other widths and
`shr.b32` remain outside that leaf.

The separate signed minimum and maximum entries add only `.s32`. Other
scalar widths, packed half-word or quarter-word lanes, and `.relu` clamping of a
negative result to zero remain unimplemented. The manual lists those sibling forms explicitly, with
different target/version conditions for the packed and clamping forms; the ledger
marks them unimplemented rather than copying the selected forms' conditions onto
them. Both `.b64` bit-count siblings remain unimplemented and still require a
**32-bit destination**. Floating-point min/max sections are outside this ledger. For floating add/mul,
other rounding modes, implicit rounding spellings, `.ftz`, `.sat`, packed
`.f32x2` and `.f64` remain excluded. Unsupported here does not mean illegal PTX.

Each accepted record links the evaluator and instruction execution to the typed
frontend and arbitrary-input theorems. It also identifies the accepted patch and
fresh replay inside a verified evidence archive. A replay passing its mechanical
checks and an independent review accepting the source interpretation are separate
facts. The exact historical patch need not be identical to a present whole module:
subsequent reviewed extensions may have added instructions to that module.

Run `python3 scripts/check_implemented_forms.py` to check source hashes, section
anchors, current referenced file hashes, declaration sites, acceptance records
and archived patch/replay identities. Run
`python3 -m unittest discover -s tests -p test_implemented_forms.py` for the
checker regressions. Neither command executes Lean or a worker. A declaration
site is only a bounded source-text location check. It follows `namespace`,
`section` (also `noncomputable section`) and matching `end` commands, one per
line. Sections do not add name components. Ordinary dotted declaration names
are relative to the active namespace; `_root_.` explicitly starts at the root.
ASCII identifier components may contain letters, digits, underscores and trailing
apostrophes. Comments and strings are blanked with the existing lexical helper.
The scan recognizes `def`, `inductive`, `structure` and `theorem` declaration
headers, optional attributes and the `noncomputable`/`protected`/`private`
modifiers; private sites cannot fulfill public ledger references. Missing or
ambiguous fully qualified names fail, as do unbalanced or unsupported scope
commands. This is not name resolution or a general Lean parser: aliases,
macro-generated declarations, quoted names and syntax outside this bounded
header grammar are not supported. Lean builds and dependency audits remain
necessary. No additional form becomes accepted through this locator extension.

If a referenced file changes, the checker fails instead of silently carrying the
old entry forward. Review the effect on the represented instruction contract,
rerun the relevant Lean and semantic checks, then update the affected hash. A hash
refresh alone does not renew semantic acceptance. The historical evidence remains
immutable; current integrity checks do not retroactively rerun that history.
