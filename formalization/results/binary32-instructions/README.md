# Third delegated instruction result

The final `binary32-003` candidate passed isolated mechanical replay and
independent source/proof review for `add.rn.f32` and `mul.rn.f32`. It adds an FP
instruction type over the existing scalar state, conservative encoded result
semantics, guarded state updates, actual instruction fetch and typed decoding.
The exact candidate is integrated. Prearchive [core checks](integration/ptxlean-fp-root-precheck.log)
passed with 604 audited declarations, and the [joint integration check](integration/ptxlean-fp-joint-precheck.log)
passed with 204 dependency reports. Those snapshots precede adding this archive
and the six-form ledger. Final full strict checks are recorded separately by
the coordinator; these historical logs do not claim to check later metadata.

The arithmetic meanings are nearest-even binary32 addition and multiplication,
with preserved subnormals. Fetched steps require ISA 9.4 and numeric SM at least
20. This feature condition does not validate target names or architecture
suffixes. Sources are compatible `.b32`/`.f32` registers or already-decoded exact
`0f`/`0F` literals; integer-to-float conversion and raw PTX parsing are excluded.
All input bit patterns are admitted. Non-NaN outputs retain exact reference bits;
NaN outputs use a conservative envelope without claiming every included bit
pattern is realizable by hardware. This is leaf-step existence, not complete
kernel execution or PyTorch correspondence.

## Calls and evidence

| Campaign call | Attempt | Result |
| --- | --- | --- |
| 7 | `binary32-001` | Produced an incomplete candidate with Lean elaboration errors; fresh module replay failed. |
| 8 | `binary32-002` | Repaired the required definitions/proofs. Independent core review passed; some worker examples remained too weak. Replay also exposed the coordinator's missing Bounds prerequisite. |
| 9 | `binary32-003` | Appended five meaningful named examples without changing any previous definition, required proof or anonymous example. Corrected independent replay passed. |

All calls ran in one recorded session with two explicit resumes. The coordinator
provided the source contract, exact types and 13 theorem signatures, independent
checks and dependency provisioning. Feedback directed ordinary elaboration
repairs and then fixed-bit zero/subnormal, negated-guard and aliased-result
examples. The worker supplied the proof implementation; independent reviewers
did not patch its Lean source. This is the third adaptive development task,
not three independent samples or a held-out model benchmark.

The final patch is
`5280b4c9504f4aad4eb232819651fbd9a8d8479498652d6cafb67970631488a6`,
based on `e00a9e51b4ab54649ce087be724f683e547f6789`. Its source hash is
`dfa76383c0500eac5752873a59dc337443c3fa81c0f1000d7ce76599deafad6b`.
The independent [source review](../../../docs/formalization/binary32-instructions-source-review.md)
and [proof review](../../../docs/formalization/binary32-instructions-proof-review.md)
record the boundaries and exact checked snapshots. The proof review covers
18 named theorems, ten definitions/types and 28 anonymous example proofs, all
with only standard Lean axioms. The fresh replay checks the specified 18 core
proof/definition endpoints and the independent acceptance driver; these counts
refer to different checks, not inconsistent claims about theorem coverage.

## Evaluator corrections

The original replay plan failed to build the already pinned Bounds prerequisite
imported by its driver. After that prerequisite was built, two generic alias
examples timed out during inference of an omitted instruction argument.
Supplying those two explicit arguments preserved every assertion and passed at
the same heartbeat limit. Both frozen drivers and metadata versions, failed
replays and the original diagnostics are retained. These coordinator defects
must not be counted as semantic failures of the completed instruction core.

The first mutation probe also had a coordinator setup failure: its unchanged
control failed before the intended comparison. That harness, report and logs
are retained. The second probe succeeded, and the third tightened the diagnostic
check to require the exact expected metadata error. The [final probe](review-probe-result.json), explained in the
[probe review](review-probes.md), compiles and
audits both control and a mutant omitting FP operand-register read metadata.
The control passes acceptance; the mutant fails exactly that independent trace
expectation. This demonstrates detection of one chosen compile-preserving defect,
not completeness of the evaluator. Compiled `.olean`/`.ilean` files and their
sidecars are excluded from retained evidence.

## Raw usage and interpretation

| Attempt | Input | Cached input | Output | Reasoning output |
| --- | ---: | ---: | ---: | ---: |
| `binary32-001` | 993,059 | 945,152 | 6,026 | 1,139 |
| `binary32-002` | 4,204,969 | 4,095,488 | 17,233 | 5,578 |
| `binary32-003` | 5,555,786 | 5,407,488 | 20,711 | 6,618 |

These are raw CLI counters; resumed values may be cumulative. **Do not sum the
rows** as independent usage or bills. No price or immutable served-model revision
was returned. Receipts distinguish the requested `gpt-6-luna` alias from absent
reported model identity. Calls used Codex headless and existing account
authentication. Coordinator specification, source/proof review, evaluator repair
and dependency setup are additional effort. The campaign has nine recorded calls
across the three tasks, with its checkpoint before call 201.

## Archive and replay

`worker-evidence.tar.gz` and `evidence-manifest.json` preserve all three attempts and provisioning, the nine-call campaign
snapshot, failed and passing replays, both driver versions, all three mutation
probes, independent review/check logs and supplied integration results. Every
archive member is individually hashed. Worktree caches are excluded.

Verify the finalized evidence without executing archived contents:

```sh
python3 scripts/check_worker_evidence.py formalization/results/binary32-instructions/evidence-manifest.json
```

Offline replay uses the archived `attempts/binary32-003` directory and
`formalization/checks/binary32-instructions-v2.json` with `worker_replay.replay`,
from a fresh destination and the pinned Lean/dependency setup. It requires no
model call. Reproducing verification of stored bytes does not promise identical
new inference output.

## Public distribution boundary

The distributed archive omits raw `events.jsonl` transcripts, whose tool outputs
may contain NVIDIA documentation. `evidence-manifest.json` records the original
archive digest and the names, byte counts and hashes of omitted members. Retained
patches, receipts and check results are byte-identical to the originals. Public
archive verification covers this subset; it does not make the omitted transcripts
available for inspection or session resumption. Historical source and base-commit
identities in retained evidence have not been rewritten.

The [publication history record](../../../docs/formalization/publication-history.md)
explains the unchanged historical identities and the limits of replay from the
public checkout. Current proofs and distributed evidence remain checkable.
