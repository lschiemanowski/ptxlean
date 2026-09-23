# Independent read-metadata mutation probe

The frozen bitcount acceptance checker rejects a trace defect even though the
candidate still builds and its instruction proofs still check.

The control is Luna's final patch `bitcount-003`, SHA-256
`23f275350ed3b1a94aebd39c3ab9d3123cd9641151188e1c247ecdc17fa395d2`, applied to
base `abd21234e3b59ca427bf155bd8a53c6b75369f2e` in a new temporary worktree. Neither
the original replay nor root Lean sources were edited. The frozen checker is
`bitcount-u32-v2.lean`, SHA-256
`59bddc3cceb558578f8ace3e71dc2c107a31a0895b4bf649d363296c3a83c27a`.

The mutation changes only the `Op.reads` case for `.unary32` to return an empty
list. It preserves the arithmetic evaluator, state updates, parser and all proof
statements. This omits a real register dependency from emitted instruction trace
metadata. It is therefore a semantic defect in the trace even though computed
register values are unchanged.

| Check | Original candidate | Metadata mutation |
| --- | --- | --- |
| Build root `Ptx` and `Ptx.IntegerBitCount` | Pass | Pass |
| Frozen independent acceptance driver | Pass | Reject |
| Public bitcount/decoder theorem dependency audit | Pass | Pass |
| Fresh candidate proof-file elaboration | Covered by build | Pass |

The rejected checks are the two register-source overlap cases, one each for
`clz` and `popc`, at acceptance-driver lines 121 and 123. Their expected read list
is written independently as `[Register.word 0]`. The propositions are false for
the mutated evaluator's trace; rejection is not a timeout, missing declaration,
or build failure. The universal instruction theorems still pass because their
expected event uses `occurrence`, which shares the mutated metadata definition.

This one deliberately injected fault shows that explicit independent trace
expectations add coverage beyond compilation and self-referential execution
equalities. It does not measure the evaluator's general sensitivity or establish
that every semantic error would be rejected. No model calls were made.

[Probe artifacts](review-probes-v1/report.json) include the exact candidate,
mutation patch, frozen checker, theorem audit, reproducible harness, command
arguments, exit codes, source hashes and separate stdout/stderr logs. The mutation
was applied only after a passing control build and acceptance check.
