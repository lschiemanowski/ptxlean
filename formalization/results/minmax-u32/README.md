# First delegated instruction result

The exact saved `minmax-003` patch was accepted for the selected typed 32-bit
`min.u32` and `max.u32` interface. Its definitions, all 16 new theorem contracts,
decoder changes and source restrictions received independent review. Fresh
reconstruction passed the pinned baseline checks, the instruction module,
coordinator-owned assertions and explicit theorem-dependency audit. Integration
passed the full core checks and its expanded 353-declaration audit.

This is **one adaptive development task**, not a held-out benchmark. It supports
the conclusion that the requested Luna configuration can finish this task after
feedback. It does not establish a full-ISA success rate or cost effectiveness.

## Attempts and assistance

| Call | Attempt | Result |
| --- | --- | --- |
| 1 | `minmax-001` | CLI launch rejected conflicting sandbox/automatic-approval flags; no inference events. Count retained. |
| 2 | `minmax-002` | Worker added the instruction cases but stopped at a decoder-proof timeout, with required proofs incomplete. Not accepted. |
| 3 | `minmax-003` | Same-session repair completed the required proofs and preserved the edit boundary. Accepted after independent checking and review. |

The coordinator supplied the bounded task, named numerical theorem statements,
source references, review obligations and an independent assertion driver. Repair
feedback suggested diagnosing proof-search cost or increasing the local Lean
heartbeat budget, and clarified how to build the new module. It supplied no
min/max implementation or proof solution. Luna made the repairs, ultimately using
a larger file-level heartbeat budget for the expanded exhaustive decoder proof.
This affects elaboration resources, not theorem hypotheses or kernel checking.

The account route was Codex headless with `--model gpt-6-luna` and saved ChatGPT
authentication, without an API-key fallback. Receipts record the requested alias;
the event stream did not report a separate model identity or immutable revision.
There were three counted headless invocations, two with inference events and one
repair invocation. No headless review calls were made. Coordinator/subagent review
effort is additional work; the call count is not a total-effort or cost measure.

Receipts preserve the CLI's raw input, cached-input, output and reasoning-token
counters. The first substantive call reports 922580 input / 874752 cached input /
5991 output tokens; the resumed call reports 2852371 / 2757120 / 18753. These are
stored as reported, without summing possibly cumulative resumed-session counters.
Billing data was not returned. Neither missing billing data nor a failed launch
is interpreted as measured zero cost. The campaign remains subject to the user's
check-in before call 201.

## Evaluator repairs are also retained

The first fresh replay passed the worker module but exposed missing equality
instances in our independent driver. Replacing proof tactics preserved every
assertion and made the positive control pass. The first mutation run then showed
that a missing `Except` equality instance could obscure the precise reason for a
negative assertion's rejection. A checked derived instance fixed that evaluator
defect. The final driver and fresh replay pass with the same assertions.

All three replay results and both mutation runs are retained. The final
[review probes](review-probes.md) show two deliberately incorrect, internally
consistent submissions compiling their own proofs before independent assertions
reject them. These two probes do not certify the whole review process.

## Evidence and replay

`acceptance.json` identifies the reviewed patch and scope. `worker-evidence.tar.gz`
contains all three generation attempts, their exact prompts and tool-event
outputs, the campaign ledger, and the three fresh mechanical replay records.
`evidence-manifest.json` hashes every member and the archive. Verify it with:

```sh
python3 scripts/check_worker_evidence.py
```

Extract into a fresh directory, then replay without inference from the repository
root (choose unused output paths):

```sh
mkdir -p /tmp/ptxlean-worker-evidence
tar -xzf formalization/results/minmax-u32/worker-evidence.tar.gz \
  -C /tmp/ptxlean-worker-evidence
python3 - <<'PY'
import json, sys
sys.path.insert(0, 'scripts')
from worker_replay import replay
plan = json.load(open('formalization/checks/minmax-u32.json'))
result = replay('/tmp/ptxlean-worker-evidence/attempts/minmax-003', '.',
    '.formalization-runs/replayed-minmax', plan['modules'], plan['checks'], plan['declarations'])
assert result['mechanical'] == 'pass', result
PY
```

The base commit remains part of repository history. Replaying requires its pinned
Lean 4.33 toolchain. The saved candidate and checks permit offline verification;
no claim is made that another inference run would produce the same patch.
The first three runner versions were identified by hash without source copies;
the archive's `current-checkers` directory preserves the final implementations,
not those earlier versions. Future invocations also save their exact `runner.py`.

The instruction-section inventory remains separate: these two selected forms do
not complete either entire min/max section, wider register/type forms, raw PTX
parsing or the full computing model. All standard source-fidelity and hardware
boundaries still apply.

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
