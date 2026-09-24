# Delegated selection result

The exact `select32-002` candidate passed fresh replay and independent
source/proof review for `selp.b32`. It uses the shared Pure32 execution
mechanism. The accepted patch is `68386addc375d6477af4e315934f013e0686d17771b69d06ae95b43c53faed18`.
The all-public audit covers 32 declarations; only standard Lean axioms occur.

| Call | Attempt | Recorded outcome |
| --- | --- | --- |
| 10 | `select32-001` | Incomplete proof script; fresh replay rejected module |
| 12 | `select32-002` | Accepted after fresh v2 replay; exact source integrated |

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
| `select32-001` | 719767 | 667648 | 8781 | 1065 |
| `select32-002` | 1339492 | 1249536 | 12625 | 3028 |

Resumed-session counters may be cumulative: do not sum these rows or treat
them as bills. No billing amount or immutable served-model revision was
returned. Receipts distinguish the requested alias from missing reported identity.
No external API-key fallback or extra inference route was used.

`worker-evidence.tar.gz` retains the task, receipts, prompts, output, patches,
provisioning records, ledger snapshot, replay logs and checker versions. Its
manifest hashes each file and the archive. Verify without executing archive
contents using `python3 scripts/check_worker_evidence.py`. To replay without
inference, extract the archive to a fresh directory and call `worker_replay.replay`
with its accepted attempt and the repository’s `select32-v2.json` module,
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

The [publication history record](../../../docs/formalization/publication-history.md)
explains the unchanged historical identities and the limits of replay from the
public checkout. Current proofs and distributed evidence remain checkable.
