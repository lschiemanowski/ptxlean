# Delegated signed minimum/maximum result

The exact `signed-minmax32-003` candidate passed fresh replay and independent
source/proof review for `min.s32`, `max.s32`. It uses the shared Pure32 execution
mechanism. The accepted patch is `41338a792294b67881939ead14b8132ad86fee00fbd4afca36ef0897944a4f78`.
The all-public audit covers 35 declarations; only standard Lean axioms occur.

| Call | Attempt | Recorded outcome |
| --- | --- | --- |
| 11 | `signed-minmax32-001` | Incomplete proof script; fresh replay rejected module |
| 13 | `signed-minmax32-002` | Incomplete proof script; fresh replay rejected module |
| 14 | `signed-minmax32-003` | Accepted after fresh v2 replay; exact source integrated |

The original v1 evaluator is retained. Name qualification, explicit Fin-index
types and concrete target/family proof unfolding repair coordinator elaboration
defects without changing the asserted propositions or expected outcomes. The
worker sources were not patched by reviewers. All failed attempts, feedback,
original-driver failures and corrected fresh replays remain in the archive.

The [source and proof review](../../../docs/formalization/pure-leaves-review.md)
explains the exact slice, target feature floor and exclusions. The [probe report](review-probes/report.json)
records an unchanged passing control and a deliberately altered candidate that
still builds with its proofs but fails the same independent driver. This is
evidence about that selected defect, not general evaluator completeness.

These were assisted development calls with coordinator-provided contracts,
checks, reusable foundations and repair feedback. They do not estimate held-out
success, full-ISA productivity or cost effectiveness. The campaign has fourteen
recorded calls after both new tasks; dispatch pauses before call 201.

| Attempt | Raw input | Cached input | Raw output | Reasoning output |
| --- | ---: | ---: | ---: | ---: |
| `signed-minmax32-001` | 463313 | 432128 | 3674 | 868 |
| `signed-minmax32-002` | 1177930 | 1110272 | 15509 | 6730 |
| `signed-minmax32-003` | 2643397 | 2541056 | 23779 | 10712 |

Resumed-session counters may be cumulative: do not sum these rows or treat
them as bills. No billing amount or immutable served-model revision was
returned. Receipts distinguish the requested alias from missing reported identity.
No external API-key fallback or extra inference route was used.

`worker-evidence.tar.gz` retains the task, receipts, prompts, output, patches,
provisioning records, ledger snapshot, replay logs and checker versions. Its
manifest hashes each file and the archive. Verify without executing archive
contents using `python3 scripts/check_worker_evidence.py`. To replay without
inference, extract the archive to a fresh directory and call `worker_replay.replay`
with its accepted attempt and the repository’s `signed-minmax32-v2.json` module,
check and declaration lists. Use a fresh output directory; this reconstructs
stored bytes rather than promising identical new model output.

The exact integrated leaf milestone passed the [full root check](integration-check.log)
with 862 dependency-audited declarations. Its Stratic check record pins the
reviewed content. Joint TorchLean checking is reported separately.

## Public distribution boundary

The distributed archive omits raw `events.jsonl` transcripts, whose tool outputs
may contain NVIDIA documentation. `evidence-manifest.json` records the original
archive digest and the names, byte counts and hashes of omitted members. Retained
patches, receipts and check results are byte-identical to the originals. Public
archive verification covers this subset; it does not make the omitted transcripts
available for inspection or session resumption. Historical source and base-commit
identities in retained evidence have not been rewritten.
