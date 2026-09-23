# Reading the accepted-form ledger

[The ledger](../../coverage/implemented-forms.json) records four selected accepted
forms. It is separate from the [instruction-section inventory](coverage.md),
whose `not_assessed` entries are unchanged. Other existing scalar instructions
are not yet entered here, so even the ledger's four-form count is not a count of
all implemented PTX forms.

| Exact form | Inputs → destination | Meaning | Manual conditions |
| --- | --- | --- | --- |
| `min.u32` | two unsigned 32-bit values → unsigned 32-bit register | Smaller input | PTX 1.0; all targets |
| `max.u32` | two unsigned 32-bit values → unsigned 32-bit register | Larger input | PTX 1.0; all targets |
| `clz.b32` | one 32-bit pattern → unsigned 32-bit register | Zeros before the first one, starting at bit 31; zero gives 32 | PTX 2.0; `sm_20` or later |
| `popc.b32` | one 32-bit pattern → unsigned 32-bit register | Number of one bits; zero gives 0 | PTX 2.0; `sm_20` or later |

Every input can come from a word register or a 32-bit immediate value. All four
forms support unconditional execution or execution guarded by a positive or
negated predicate. A false guard advances the program counter without writing
the destination. Register overlap is allowed: the incoming source value is read
before the destination changes. These are typed statement interfaces, not a
parser or type checker for complete PTX source files. The arithmetic decoder
records no architecture/version eligibility decision.

The source was rechecked against the pinned PTX 9.4 integer instruction sections
[minimum](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-min),
[maximum](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-max),
[leading zeros](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-clz)
and [population count](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-popc).
Common input, destination and guard rules have their own pinned section anchors
in the ledger. Source fidelity is an independent review judgment, supported by
[the first source review](initial-source-review.md) and
[the bit-count review](bitcount-source-review.md); it is not a consequence of a
successful Lean build.

The unsigned minimum and maximum entries do not cover signed comparisons, other
scalar widths, packed half-word or quarter-word lanes, or `.relu` clamping of a
negative result to zero. The manual lists those sibling forms explicitly, with
different target/version conditions for the packed and clamping forms; the ledger
marks them unimplemented rather than copying the selected forms' conditions onto
them. Both `.b64` bit-count siblings remain unimplemented and still require a
**32-bit destination**. Floating-point min/max sections are outside this ledger.

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
site is only a simple source-text location check for the current single-namespace
modules. Lean builds and dependency audits remain necessary.

If a referenced file changes, the checker fails instead of silently carrying the
old entry forward. Review the effect on the represented instruction contract,
rerun the relevant Lean and semantic checks, then update the affected hash. A hash
refresh alone does not renew semantic acceptance. The historical evidence remains
immutable; current integrity checks do not retroactively rerun that history.
