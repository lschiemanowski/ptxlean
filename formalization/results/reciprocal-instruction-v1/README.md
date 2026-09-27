# Rounded reciprocal instruction trial

`rcp.rn.f32` is accepted for the project's PTX ISA 9.4 / numeric SM ≥ 20 slice, without
FTZ. One headless invocation requested `gpt-6-luna` (campaign call 32); no
provider-confirmed model identity was reported. The integrated source is exactly
the worker patch. There was no repair invocation, coordinator candidate edit or
paid external review call.

The coordinator supplied a frozen interface, numerical provider and independent
acceptance driver before dispatch. Separate agents reviewed the source/provider
contract and candidate proofs. Fresh replay rebuilt pinned dependencies, checked
the independent driver and audited all 23 public declarations against only the
permitted standard Lean axioms. This measures implementation of a precise supplied
contract, not independent semantic discovery or full softmax verification.

The first preparation and its retry failed before any model call: Lake produced
`proofwidgets/widget/package-lock.json.hash` outside `.lake`. A reviewed helper
change recognizes this exact generated file, requires the underlying lock file
to be tracked and unchanged, rejects symbolic links and unknown files, and pins
the cache bytes in the prerequisite artifact manifest. Two added regression tests
exercise cache drift, tracked-source drift, unknown-file rejection and symlinks.
A fresh preparation then succeeded; the failed preparation records are retained.

The first frozen acceptance driver reached deterministic elaboration timeouts at
two calls with implicit instruction arguments. Driver v2 makes those arguments
explicit. Every proposition, hypothesis and test remains unchanged; an independent
review confirmed that comparison. A direct precheck passed, then a third fresh
replay passed. The second replay exhausted disk during dependency setup and could
not persist its final status. Its unchanged stale result and a separate recovery
record retain that failure. Generated caches from this task were removed to free
space; source worktrees and evidence were preserved. All three replay records and
both driver versions are archived. These
costs belong to coordinator setup/checker repair, not worker failure. The worker
reported its build and direct check, but did not report its own dependency audit;
acceptance relies on the independently performed audit.

The instruction preserves all numerical results, including the conservative NaN
allowance. It handles arbitrary preexisting state, both predicate polarities,
source/destination aliases, target checks and actual fetch. Enabled destination
meaning follows from execution; finite-range assumptions are needed only for
numerical analysis. One-step existence is proved, not assumed. No whole-kernel
termination, softmax execution or hardware correspondence is claimed.

Run from the repository root:

```sh
./scripts/check.sh
(cd integration/torchlean && ./check.sh)
```

The integration suite includes corrected driver v2. Historical driver v1 is
retained as intentionally failing evidence and is not part of the passing suite.
The archive omits raw model events, which may contain vendor text; their hashes
and the local original archive hash are retained. Source interpretation and
candidate review are explained in the
[source review](../../../docs/formalization/reciprocal-instruction-source-review.md).

## Workflow deviation and calibration

The required complete reference-fixture preflight was omitted before dispatch.
Freezing a driver before dispatch alone did not satisfy that workflow requirement.
This omission is recorded as coordinator process error and is not repaired
retroactively by successful checks. Post-generation calibration accepts the
original candidate and rejects three deliberately wrong definitions: ignoring
the input, mapping the operation to the approximate mnemonic, and weakening the
target threshold. Each mutant independently compiles and passes its own 23
declaration dependency audit, so the driver rejects semantic changes rather than
merely broken files. Probe sources and logs are archived. Reproduce without any
model call using a new output directory:

```sh
python3 formalization/review/check_reciprocal_instruction.py --output /tmp/reciprocal-probes
```
