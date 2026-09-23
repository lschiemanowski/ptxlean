# Second delegated instruction result

The exact `bitcount-003` patch passed fresh mechanical replay and independent
semantic/proof review for `clz.b32` and `popc.b32`. It adds a genuine one-input
scalar operation, precise count semantics for every 32-bit word, actual guarded
execution/frame proofs and the typed text forms. The exact candidate is integrated. The coordinator
ran `./scripts/check.sh` successfully with 574 audited declarations; the
[retained integration log](integration-check.log) records those core checks.
Joint TorchLean integration is reported separately. `acceptance.json` records
mechanical, source, proof, integration and mutation-review outcomes separately.

This is a second adaptive development task. It shows the requested Luna
configuration can finish this bounded task after feedback. It does not measure
a held-out success rate, general ISA fidelity, autonomous specification discovery,
or cost effectiveness.

## Calls and repairs

| Campaign call | Attempt | Result |
| --- | --- | --- |
| 4 | `bitcount-001` | Added unary semantics and partial proofs, then stopped with required zero-characterization proofs incomplete. Fresh replay rejected the candidate module. |
| 5 | `bitcount-002` | Completed the mathematical proofs and examples. Fresh baseline/module checks passed; acceptance failed because required execution lemmas were in the wrong namespace, and independently because the coordinator driver contained a formatting error. |
| 6 | `bitcount-003` | Added exactly the three required public theorem wrappers. The semantics and generic execution code were unchanged. Fresh replay with the corrected, assertion-identical driver passed. |

All three calls ran in one recorded session, with the latter two explicit
resumes. The coordinator supplied selected source sections, the unary-interface
choice, mathematical theorem contracts, exact execution signatures and independent
checks. First repair feedback directed the worker to finish ordinary list/bit
proof obligations and preserve the exact API. Second repair feedback required
the missing namespace wrappers. These were assisted development calls, not
independent attempts from an unchanged prompt. The worker supplied the
implementation and completed proofs; reviewers did not patch its Lean code.

The list contracts deliberately specify the mathematical counts: all true bits
at indices zero through thirty-one, and the initial false-bit prefix encountered
from thirty-one down to zero. The implementation chooses those same simple list
operations and proves their 32-bit result does not wrap. Independent source
review remains necessary even when a definition resembles its theorem contract.

## Preserved evaluator correction

The original `bitcount-u32.lean` driver remains unchanged. Its candidate-only
`execution_signature` split a record update over lines at an indentation Lean
rejects. The earlier baseline-prefix check did not reach that declaration, so
the coordinator did not discover the defect before the first completed candidate.
This is an evaluator error, not evidence that the instruction semantics were wrong.

`bitcount-u32-v2.lean` places that update on one line. All non-whitespace bytes
are identical: every assertion, theorem signature, required namespace and
expected result is unchanged. V2 still rejected call 5 for its three missing
names; it did not retarget expectations to accommodate that candidate. Both
failed replay records, both driver versions and their manifests are archived.
The final v2 driver and required dependency audit pass in a fresh reconstruction.

## Verification and remaining limits

The final saved patch is
`23f275350ed3b1a94aebd39c3ab9d3123cd9641151188e1c247ecdc17fa395d2`, based on
`abd21234e3b59ca427bf155bd8a53c6b75369f2e`. Fresh replay applied only its three
allowed changed files, then passed the clean baseline check, candidate-module
build, frozen v2 assertions and eleven required declaration audits.

Independent review additionally inspected all fourteen new named theorems and
three new helper definitions, including both list lemmas and all execution
wrappers. Dependency reports contain only standard Lean axioms or no axioms.
All 31 existing named Scalar theorem statements and seven ScalarText statements
remain unchanged. The exact source forms require PTX 2.0 and `sm_20` or later;
this does not claim the memory-only eligibility checker enforces those arithmetic
conditions. Both full instruction sections also support `.b64`, still outside
the implemented slice. Raw PTX parsing and hardware conformance are unproved.

The independent [mutation probe](review-probes.md) passed its unchanged control,
then removed only unary source-register read metadata. The incorrect candidate
still built and its instruction proofs and dependency audit passed; two explicit
trace expectations in the frozen v2 checker rejected it. This establishes
detection of that chosen defect, not completeness of semantic review.

## Raw usage and effort

| Attempt | Input | Cached input | Output | Reasoning output |
| --- | ---: | ---: | ---: | ---: |
| `bitcount-001` | 1,198,990 | 1,143,552 | 10,132 | 2,375 |
| `bitcount-002` | 4,377,096 | 4,250,880 | 25,565 | 8,459 |
| `bitcount-003` | 4,740,989 | 4,608,256 | 26,765 | 8,614 |

These are raw CLI-reported counters. Resumed-session counters may be cumulative;
**do not sum the rows** as independent invocation usage or bills. No billing
amounts or immutable served-model revision were reported. Receipts distinguish
the requested `gpt-6-luna` alias from absent reported model identity. The route
used Codex headless with existing account authentication, without API-key fallback.
Coordinator/source/proof review and evaluator repair effort are additional work,
not included in a count of three headless invocations. The shared campaign has
six recorded calls across both tasks; the checkpoint remains before call 201.

## Archive and offline replay

`worker-evidence.tar.gz` contains all three attempts, exact task inputs, prompts,
feedback, event streams, runner copies, final messages and patches; the six-call
ledger snapshot; two failed and one passing replay; both checkers/manifests;
and the independent complete-helper audit. Each replay's checker hash matches
the archived `current-checkers/worker_replay.py`. `evidence-manifest.json` hashes
every archive member and the archive itself. Worktree caches are excluded.

Verify both archived trials without extracting or executing their contents:

```sh
python3 scripts/check_worker_evidence.py
```

To select just this archive:

```sh
python3 scripts/check_worker_evidence.py formalization/results/bitcount-u32/evidence-manifest.json
```

Reconstruct and verify the accepted patch without inference, using fresh output
directories and the pinned Lean 4.34 toolchain:

```sh
mkdir -p /tmp/ptxlean-bitcount-evidence
tar -xzf formalization/results/bitcount-u32/worker-evidence.tar.gz \
  -C /tmp/ptxlean-bitcount-evidence
python3 - <<'PY'
import json, sys
sys.path.insert(0, 'scripts')
from worker_replay import replay
plan = json.load(open('formalization/checks/bitcount-u32.json'))
result = replay('/tmp/ptxlean-bitcount-evidence/attempts/bitcount-003', '.',
    '.formalization-runs/replayed-bitcount', plan['modules'], plan['checks'], plan['declarations'])
assert result['mechanical'] == 'pass', result
PY
```

The archive preserves previous failed evidence rather than replacing it with the
accepted patch. Rechecking these stored bytes is reproducible; an identical new
inference result is not promised.
